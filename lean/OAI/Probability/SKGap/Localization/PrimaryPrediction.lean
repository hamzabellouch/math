import Mathlib
import OAI.Probability.SKGap.Localization.Append

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram

inductive Partial (D : Type*) where
  | done : Diagram D → Partial D
  | more : Diagram D → Partial D → Partial D
  deriving DecidableEq
namespace Partial
variable {D : Type*}
def word : Partial D → List (Letter D)
  | .done d => d.word
  | .more d p => d.word ++ (.noise :: p.word)
def head : Partial D → Diagram D
  | .done d => d
  | .more d _ => d
def diag (a : D) : Partial D → Partial D
  | .done d => .done (.diag a d)
  | .more d p => .more (.diag a d) p
def create (p : Partial D) : Partial D := .more .nil p
def contract : Partial D → Option (Partial D)
  | .done _ => none
  | .more d (.done e) => some (.done (.arch d e))
  | .more d (.more e p) => some (.more (.arch d e) p)
def noise (p : Partial D) : List (Partial D) := create p :: (contract p).toList

@[simp] lemma word_diag (a : D) (p : Partial D) : (p.diag a).word = .diag a :: p.word := by
  cases p <;> rfl
@[simp] lemma word_create (p : Partial D) : p.create.word = .noise :: p.word := rfl
lemma word_contract (p q : Partial D) (h : p.contract=some q) : q.word = .noise :: p.word := by
  cases p with
  | done d => simp [contract] at h
  | more d p => cases p <;> simp only [contract,Option.some.injEq] at h <;> subst q <;>
      simp [word,Diagram.word,List.append_assoc]
lemma diag_injective (a : D) : Function.Injective (diag a : Partial D → Partial D) := by
  intro p q h; cases p <;> cases q <;> simp_all [diag]
lemma create_injective : Function.Injective (create : Partial D → Partial D) := by
  intro p q h; exact Partial.more.inj h |>.2
lemma contract_injective {p q r : Partial D} (hp : p.contract=some r) (hq : q.contract=some r) : p=q := by
  cases p with
  | done d => simp [contract] at hp
  | more d p =>
    cases q with
    | done e => simp [contract] at hq
    | more e q =>
      cases p <;> cases q <;> simp only [contract,Option.some.injEq] at hp hq <;>
        subst r <;> simp_all
lemma create_ne_contract (p q r : Partial D) (h : q.contract=some r) : p.create≠r := by
  cases q with
  | done d => simp [contract] at h
  | more d q => cases q <;> simp only [contract,Option.some.injEq] at h <;> subst r <;> simp [create]

lemma diag_preimage (a : D) (F : List (Letter D)) (p : Partial D)
    (h : p.word = .diag a :: F) : ∃ q : Partial D, q.word=F ∧ p=q.diag a := by
  cases p with
  | done d => cases d <;> simp only [word,Diagram.word] at h
              case diag b d => simp only [List.cons.injEq,Letter.diag.injEq] at h
                               obtain ⟨rfl,h⟩ := h; exact ⟨.done d,h,rfl⟩
              all_goals simp at h
  | more d p =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | arch d e => simp [word,Diagram.word] at h
    | diag b d =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,Letter.diag.injEq] at h
      obtain ⟨rfl,h⟩ := h; exact ⟨.more d p,h,rfl⟩
lemma noise_preimage (F : List (Letter D)) (p : Partial D)
    (h : p.word = .noise :: F) :
    ∃ q : Partial D, q.word=F ∧ (p=q.create ∨ q.contract=some p) := by
  cases p with
  | done d =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons.injEq,true_and] at h
      exact ⟨.more d (.done e),h,Or.inr rfl⟩
  | more d p =>
    cases d with
    | nil =>
      simp only [word,Diagram.word,List.nil_append,List.cons.injEq,true_and] at h
      exact ⟨p,h,Or.inl rfl⟩
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      exact ⟨.more d (.more e p),h,Or.inr rfl⟩

def enumerate : List (Letter D) → List (Partial D)
  | [] => [.done .nil]
  | .diag a :: F => (enumerate F).map (diag a)
  | .noise :: F => (enumerate F).flatMap noise

@[simp] lemma mem_enumerate (F : List (Letter D)) (p : Partial D) :
    p∈enumerate F ↔ p.word=F := by
  induction F generalizing p with
  | nil =>
    cases p with
    | done d => cases d <;> simp [enumerate,word,Diagram.word]
    | more d p => simp [enumerate,word]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [enumerate,List.mem_map,ih]
      constructor
      · rintro ⟨q,hq,rfl⟩; simp [hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := diag_preimage a F p hp; exact ⟨q,hq,hp.symm⟩
    | noise =>
      simp only [enumerate,List.mem_flatMap,noise,List.mem_cons,Option.mem_toList,ih]
      constructor
      · rintro ⟨q,hq,hp|hp⟩
        · subst p; simp [hq]
        · rw [word_contract q p hp,hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := noise_preimage F p hp; exact ⟨q,hq,hp⟩

lemma noise_nodup (p : Partial D) : p.noise.Nodup := by
  cases p with
  | done d => simp [noise,contract]
  | more d p => cases p <;> simp [noise,contract,create]
lemma noise_disjoint {p q : Partial D} (h : p≠q) : List.Disjoint p.noise q.noise := by
  apply List.disjoint_left.mpr
  intro r hr hq
  simp only [noise,List.mem_cons,Option.mem_toList] at hr hq
  rcases hr with hr|hr <;> rcases hq with hq|hq
  · exact h (create_injective (hr.symm.trans hq))
  · exact create_ne_contract p q r hq hr.symm
  · exact create_ne_contract q p r hr hq.symm
  · exact h (contract_injective hr hq)
lemma enumerate_nodup (F : List (Letter D)) : (enumerate F).Nodup := by
  induction F with
  | nil => simp [enumerate]
  | cons a F ih =>
    cases a with
    | diag a => exact ih.map (diag_injective a)
    | noise =>
      rw [enumerate,List.nodup_flatMap]
      exact ⟨fun p _ => noise_nodup p, List.Pairwise.imp (fun h => noise_disjoint h) ih⟩
end Partial

section Fock
variable {ι : Type*} [Fintype ι]
abbrev D := ι → ℝ
abbrev Stack := D (ι:=ι) × List (D (ι:=ι))
abbrev Space := Stack (ι:=ι) →₀ ℝ

def ket (s : Stack (ι:=ι)) : Space (ι:=ι) := Finsupp.single s 1

def diagonal (a : D (ι:=ι)) : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => ket (a*s.1,s.2))
def creation : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => ket (1,s.1::s.2))
def annihilation : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => match s.2 with
    | [] => 0
    | a::L => Diagram.mean s.1 • ket (a,L))
def noise (j : ℝ) : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) := creation + j • annihilation

def vacuum : Space (ι:=ι) := ket (1,[])
def project : Space (ι:=ι) →ₗ[ℝ] D (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => if s.2=[] then s.1 else 0)

omit [Fintype ι] in
@[simp] lemma diagonal_ket (a : D (ι:=ι)) (s : Stack (ι:=ι)) :
    diagonal a (ket s)=ket (a*s.1,s.2) := by simp [diagonal,ket]
omit [Fintype ι] in
@[simp] lemma creation_ket (s : Stack (ι:=ι)) :
    creation (ket s)=ket (1,s.1::s.2) := by simp [creation,ket]
@[simp] lemma annihilation_ket_nil (a : D (ι:=ι)) :
    annihilation (ket (a,[]))=0 := by simp [annihilation,ket]
@[simp] lemma annihilation_ket_cons (a b : D (ι:=ι)) (L : List (D (ι:=ι))) :
    annihilation (ket (a,b::L))=Diagram.mean a • ket (b,L) := by simp [annihilation,ket]
omit [Fintype ι] in
@[simp] lemma project_ket_nil (a : D (ι:=ι)) : project (ket (a,[])) = a := by
  simp [project,ket]
omit [Fintype ι] in
@[simp] lemma project_ket_cons (a b : D (ι:=ι)) (L : List (D (ι:=ι))) :
    project (ket (a,b::L)) = 0 := by simp [project,ket]

def letter (j : ℝ) : Letter (D (ι:=ι)) → Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι)
  | .diag a => diagonal a
  | .noise => noise j

def word (j : ℝ) : List (Letter (D (ι:=ι))) → Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι)
  | [] => LinearMap.id
  | a::F => (letter j a).comp (word j F)

def outer : Diagram (D (ι:=ι)) → D (ι:=ι)
  | .nil => 1
  | .diag a d => a * outer d
  | .arch _ d => outer d

def coefficient (j : ℝ) : Diagram (D (ι:=ι)) → ℝ
  | .nil => 1
  | .diag _ d => coefficient j d
  | .arch a b => j * Diagram.mean (a.value j) * coefficient j b

lemma value_factor (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    d.value j i=coefficient j d * outer d i := by
  induction d with
  | nil => simp [Diagram.value,coefficient,outer]
  | diag a d ih => simp [Diagram.value,coefficient,outer,ih]; ring
  | arch a b ia ib => simp [Diagram.value,coefficient,outer,ib]; ring
lemma mean_value (j : ℝ) (d : Diagram (D (ι:=ι))) :
    Diagram.mean (d.value j)=coefficient j d * Diagram.mean (outer d) := by
  simp only [funext (value_factor j d),Diagram.mean_const_mul]

def Partial.stack : Partial (D (ι:=ι)) → Stack (ι:=ι)
  | .done d => (outer d,[])
  | .more d p => (outer d,p.stack.1::p.stack.2)
def Partial.coefficient (j : ℝ) : Partial (D (ι:=ι)) → ℝ
  | .done d => Primary.coefficient j d
  | .more d p => Primary.coefficient j d * p.coefficient j

def Partial.state (j : ℝ) (p : Partial (D (ι:=ι))) : Space (ι:=ι) :=
  p.coefficient j • ket p.stack

lemma Partial.state_diag (j : ℝ) (a : D (ι:=ι)) (p : Partial (D (ι:=ι))) :
    (p.diag a).state j = diagonal a (p.state j) := by
  cases p <;> simp [state,stack,Partial.diag,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_create (j : ℝ) (p : Partial (D (ι:=ι))) :
    p.create.state j = creation (p.state j) := by
  simp [state,stack,create,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_contract (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.contract.toList).map (Partial.state j)).sum = j • annihilation (p.state j) := by
  cases p with
  | done d => simp [state,stack,Partial.contract]
  | more d p =>
    cases p <;> simp [state,stack,Partial.contract,Partial.coefficient,
      Primary.coefficient,Primary.outer,mean_value,smul_smul,mul_assoc,mul_left_comm,mul_comm]
lemma Partial.state_noise (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.noise).map (Partial.state j)).sum = Primary.noise j (p.state j) := by
  simp only [Partial.noise,List.map_cons,List.sum_cons,state_create,state_contract]
  rfl

lemma word_vacuum (j : ℝ) (F : List (Letter (D (ι:=ι)))) :
    word j F vacuum = ((Partial.enumerate F).map (Partial.state j)).sum := by
  induction F with
  | nil => simp [word,vacuum,Partial.enumerate,Partial.state,Partial.stack,
      Partial.coefficient,Primary.coefficient,Primary.outer]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_map]
      simp only [map_list_sum,Function.comp_def,Partial.state_diag,List.map_map]
    | noise =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_flatMap]
      rw [SKGap.Noncrossing.InverseDiagram.sum_flatMap]
      simp only [Partial.state_noise,map_list_sum,List.map_map,Function.comp_def]

lemma Partial.project_state_done (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    project ((.done d : Partial _).state j) i = d.value j i := by
  simp [Partial.state,Partial.stack,Partial.coefficient,value_factor]
lemma Partial.project_state_more (j : ℝ) (d : Diagram (D (ι:=ι)))
    (p : Partial (D (ι:=ι))) : project ((Partial.more d p).state j) = 0 := by
  simp [Partial.state,Partial.stack]

lemma prediction_as_finset (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    Diagram.prediction j F i = ∑ d∈Diagram.enumerate F, d.value j i := by
  classical
  let e : Diagram.Paired F ≃ {d // d∈Diagram.enumerate F} :=
    { toFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mpr d.property⟩
      invFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mp d.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑ d : Diagram.Paired F, d.val.value j i) = _
  calc
    _ = ∑ d : {d // d∈Diagram.enumerate F}, d.val.value j i :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort (Diagram.enumerate F) (fun d => d.value j i)

theorem project_word (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    project (word j F vacuum) i = Diagram.prediction j F i := by
  classical
  rw [word_vacuum,map_list_sum,List.map_map]
  change (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i = _
  have heval : (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i =
      ((Partial.enumerate F).map (fun p => project (p.state j) i)).sum := by
    induction Partial.enumerate F with
    | nil => rfl
    | cons p L ih => simp [ih]
  rw [heval,← List.sum_toFinset _ (Partial.enumerate_nodup F),prediction_as_finset]
  have hsub : (Diagram.enumerate F).image Partial.done ⊆ (Partial.enumerate F).toFinset := by
    intro p hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
    simpa [Partial.word] using hd
  rw [← Finset.sum_subset hsub (fun p hp hn => ?_)]
  · rw [Finset.sum_image (fun d _ e _ h => Partial.done.inj h)]
    exact Finset.sum_congr rfl (fun d _ => Partial.project_state_done j d i)
  · cases p with
    | done d =>
      exfalso; apply hn
      exact Finset.mem_image.mpr ⟨d,by simpa [Partial.word] using hp,rfl⟩
    | more d p => simp [Partial.project_state_more]

def previousDiagonal (a : ℕ → D (ι:=ι)) : ℕ → D (ι:=ι)
  | 0 => 1
  | n+1 => a n

def creationLabels (a : ℕ → D (ι:=ι)) : ℕ → List (D (ι:=ι))
  | 0 => []
  | n+1 => previousDiagonal a n :: creationLabels a n

def primaryOperator (j : ℝ) (a : ℕ → D (ι:=ι)) :
    ℕ → Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι)
  | 0 => LinearMap.id
  | 1 => noise j
  | n+2 => (noise j).comp ((diagonal (a n)).comp (primaryOperator j a (n+1))) -
      (j*Diagram.mean (a n)) •
        (diagonal (previousDiagonal a n)).comp (primaryOperator j a n)

theorem primaryOperator_vacuum (j : ℝ) (a : ℕ → D (ι:=ι)) (n : ℕ) :
    primaryOperator j a n vacuum = ket (1,creationLabels a n) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [primaryOperator,noise,vacuum,creationLabels,previousDiagonal]
  | more n hn hn1 =>
    simp [primaryOperator,LinearMap.comp_apply,hn,hn1,noise,creationLabels,
      previousDiagonal,smul_smul]

theorem primaryOperator_prediction_zero (j : ℝ) (a : ℕ → D (ι:=ι))
    (n : ℕ) (hn : 0<n) : project (primaryOperator j a n vacuum) = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [primaryOperator_vacuum]; simp [creationLabels]

abbrev WordPolynomial := List (ℝ × List (Letter (D (ι:=ι))))

def prependWords (F : List (Letter (D (ι:=ι)))) (P : WordPolynomial (ι:=ι)) :
    WordPolynomial (ι:=ι) := P.map (fun p => (p.1,F++p.2))
def scale (c : ℝ) (P : WordPolynomial (ι:=ι)) : WordPolynomial (ι:=ι) :=
  P.map (fun p => (c*p.1,p.2))

def polynomialOperator (j : ℝ) (P : WordPolynomial (ι:=ι)) :
    Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  (P.map (fun p => p.1 • word j p.2)).sum

def polynomialPrediction (j : ℝ) (P : WordPolynomial (ι:=ι)) (i : ι) : ℝ :=
  (P.map (fun p => p.1 * Diagram.prediction j p.2 i)).sum

def primaryPolynomial (j : ℝ) (a : ℕ → D (ι:=ι)) : ℕ → WordPolynomial (ι:=ι)
  | 0 => [(1,[])]
  | 1 => [(1,[.noise])]
  | n+2 => prependWords [.noise,.diag (a n)] (primaryPolynomial j a (n+1)) ++
      scale (-(j*Diagram.mean (a n)))
        (prependWords [.diag (previousDiagonal a n)] (primaryPolynomial j a n))

lemma word_append (j : ℝ) (F G : List (Letter (D (ι:=ι)))) :
    word j (F++G) = (word j F).comp (word j G) := by
  induction F with
  | nil => simp [word]
  | cons a F ih => simp [word,ih,LinearMap.comp_assoc]
lemma polynomialOperator_append (j : ℝ) (P Q : WordPolynomial (ι:=ι)) :
    polynomialOperator j (P++Q) = polynomialOperator j P + polynomialOperator j Q := by
  simp [polynomialOperator]
lemma polynomialOperator_prefix (j : ℝ) (F : List (Letter (D (ι:=ι))))
    (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (prependWords F P) = (word j F).comp (polynomialOperator j P) := by
  induction P with
  | nil => simp [prependWords,polynomialOperator]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [word_append,ih,LinearMap.comp_add,LinearMap.comp_smul]
lemma polynomialOperator_scale (j c : ℝ) (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (scale c P)=c • polynomialOperator j P := by
  induction P with
  | nil => simp [scale,polynomialOperator]
  | cons p P ih =>
    simp only [scale,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

lemma primaryPolynomial_operator (j : ℝ) (a : ℕ → D (ι:=ι)) (n : ℕ) :
    polynomialOperator j (primaryPolynomial j a n)=primaryOperator j a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,polynomialOperator,primaryOperator,word]
  | one => simp [primaryPolynomial,polynomialOperator,primaryOperator,word,letter]
  | more n hn hn1 =>
    simp only [primaryPolynomial,polynomialOperator_append,polynomialOperator_prefix,
      polynomialOperator_scale,hn,hn1,word,letter,LinearMap.comp_id,primaryOperator]
    ext v k
    simp [LinearMap.comp_apply,sub_eq_add_neg,neg_smul]

lemma polynomialPrediction_eq_project (j : ℝ) (P : WordPolynomial (ι:=ι)) (i : ι) :
    polynomialPrediction j P i = project (polynomialOperator j P vacuum) i := by
  induction P with
  | nil => simp [polynomialPrediction,polynomialOperator]
  | cons p P ih =>
    simp only [polynomialPrediction,polynomialOperator,List.map_cons,List.sum_cons,
      LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul] at *
    rw [project_word,ih]

theorem primaryPolynomial_prediction_zero (j : ℝ) (a : ℕ → D (ι:=ι))
    (n : ℕ) (hn : 0<n) (i : ι) :
    polynomialPrediction j (primaryPolynomial j a n) i = 0 := by
  rw [polynomialPrediction_eq_project,primaryPolynomial_operator,
    primaryOperator_prediction_zero j a n hn]
  rfl

end Fock
end SKGap.Noncrossing.Primary
end
end

end OAI
