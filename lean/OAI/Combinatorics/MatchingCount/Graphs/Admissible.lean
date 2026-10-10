import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.EnlargementRun
import OAI.Combinatorics.MatchingCount.Sampling.PairStep

namespace OAI

namespace MatchingFPRAS.Variation

open Finset

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

lemma bind_perturbation_on (p : Ω → ℝ) (k l : Ω → Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) (ε : ℝ)
    (he : ∀ x,p x≠0 → tv (k x) (l x) ≤ ε) :
    tv (bind p k) (bind p l) ≤ ε := by
  unfold tv bind
  have h : ∑ y,|∑ x,p x*k x y-∑ x,p x*l x y| ≤ 2*ε := by
    calc
      _ = ∑ y,|∑ x,p x*(k x y-l x y)| := by simp only [mul_sub,sum_sub_distrib]
      _ ≤ ∑ y,∑ x,|p x*(k x y-l x y)| := sum_le_sum (fun y _ => abs_sum_le_sum_abs _ _)
      _ = ∑ x,p x*(∑ y,|k x y-l x y|) := by
        rw [sum_comm]; simp_rw [abs_mul,abs_of_nonneg (hp _),←mul_sum]
      _ ≤ ∑ x,p x*(2*ε) := by
        apply sum_le_sum
        intro x _
        by_cases hx : p x=0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left _ (hp x)
          have hh:=he x hx
          unfold tv at hh
          linarith
      _ = _ := by rw [←sum_mul,hs,one_mul]
  linarith

end MatchingFPRAS.Variation

namespace MatchingFPRAS.WeightedOptions

open Finset Variation

variable {J Ω B : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

theorem drawThen_tv_on (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ)
    (P : J → Ω → ℝ) (e : ℝ) (he : ∀ j,c.law j≠0 → tv (imageLaw (g j)) (P j)≤e) :
    tv (imageLaw (c.drawThen g k)) (bind (fun j=>(c.law j:ℝ)) P)≤
      2*c.size/(2:ℝ)^k+e := by
  rw [drawThen_law]
  calc
    _ ≤ tv (bind (imageLaw (c.draw k)) (fun j=>imageLaw (g j)))
        (bind (fun j=>(c.law j:ℝ)) (fun j=>imageLaw (g j)))+
        tv (bind (fun j=>(c.law j:ℝ)) (fun j=>imageLaw (g j)))
          (bind (fun j=>(c.law j:ℝ)) P) := tv_triangle _ _ _
    _ ≤ 2*c.size/(2:ℝ)^k+e := add_le_add
      ((bind_contraction _ _ _ (fun _=>imageLaw_nonneg _) (fun _=>imageLaw_sum _)).trans (c.draw_tv k))
      (bind_perturbation_on _ _ _ (fun j=>by exact_mod_cast c.law_nonneg j)
        (c.real_law_sum) e (fun j hj=>he j (by exact_mod_cast hj)))

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Replica

open Finset Variation

variable {I Ω B : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B] [LinearOrder (Update I)]

def admissible (guides : I → Finset I) (base : Finset I) : Option (Update I) → Prop
  | none => True
  | some (.inl ij) => ij.2∈guides ij.1
  | some (.inr i) => i∈base

lemma scanChoice_support (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty)
    (u : Option (Update I)) (hu : (scanChoice guides base hb).law u≠0) :
    admissible guides base u := by
  cases u with
  | none => trivial
  | some u =>
    by_contra h
    apply hu
    simp only [scanChoice,WeightedOptions.mix_law,WeightedOptions.pure_law,
      WeightedOptions.map_law]
    simp only [reduceCtorEq,ite_false,Option.some.injEq,sum_ite_eq',mem_univ,ite_true]
    rw [WeightedOptions.uniform_law]
    have hn : u∉updates guides base := by
      cases u <;> simpa [updates,admissible] using h
    simp [hn]

omit [LinearOrder (Update I)] in
lemma localSampler_tv_on [LinearOrder (Update I)] (p : I → Ω → ℝ) (Q : ∀ x y,PairCapacity p x y)
    (guides : I → Finset I) (base : Finset I)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (e : ℝ) (he : 0≤e)
    (hp : ∀ x y,y∈guides x → ∀ a,tv (imageLaw (pair x y a))
      (fun b=>(Q x y).q a b/(p x a.1*p y a.2))≤e)
    (hr : ∀ i,i∈base → tv (imageLaw (refresh i)) (p i)≤e)
    (s : I → Ω) (u : Option (Update I)) (hu : admissible guides base u) :
    tv (imageLaw (localSampler pair refresh s u)) (updateKernel p Q s u)≤e := by
  cases u with
  | none =>
    have h : imageLaw (localSampler pair refresh s none)=updateKernel p Q s none := by
      funext t
      simp only [imageLaw,push,localSampler,updateKernel]
      by_cases hst : s=t
      · subst t
        simpa using uniform_sum (A:=B)
      · simp [hst]
    rw [h,tv_self]
    exact he
  | some u => cases u with
    | inl ij =>
      have hk : updateKernel p Q s (some (.inl ij))=
          push (fun b=>(Q ij.1 ij.2).q (s ij.1,s ij.2) b/(p ij.1 (s ij.1)*p ij.2 (s ij.2)))
            (replacePair ij.1 ij.2 s) := by
        funext t
        simp only [updateKernel,pairStep,push]
      rw [hk]
      change tv (imageLaw ((replacePair ij.1 ij.2 s) ∘ pair ij.1 ij.2 (s ij.1,s ij.2)))
        (push (fun b=>(Q ij.1 ij.2).q (s ij.1,s ij.2) b/(p ij.1 (s ij.1)*p ij.2 (s ij.2)))
          (replacePair ij.1 ij.2 s))≤e
      rw [imageLaw_comp]
      exact (push_contraction _ _ _).trans (hp _ _ hu _)
    | inr i =>
      have hk : updateKernel p Q s (some (.inr i))=push (p i) (Function.update s i) := by
        funext t
        simp only [updateKernel,baseStep,push]
        apply sum_congr rfl
        intro a _
        congr 1
      rw [hk]
      change tv (imageLaw ((Function.update s i) ∘ refresh i)) (push (p i) (Function.update s i))≤e
      rw [imageLaw_comp]
      exact (push_contraction _ _ _).trans (hr i hu)

theorem sampleScan_tv_on (p : I → Ω → ℝ) (hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (guides : I → Finset I) (hself : ∀ x y,y∈guides x → x≠y)
    (base : Finset I) (hb : base.Nonempty) (Q : ∀ x y,PairCapacity p x y)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (e : ℝ) (he : 0≤e)
    (hpr : ∀ x y,y∈guides x → ∀ a,tv (imageLaw (pair x y a))
      (fun b=>(Q x y).q a b/(p x a.1*p y a.2))≤e)
    (hr : ∀ i,i∈base → tv (imageLaw (refresh i)) (p i)≤e) (k : ℕ) (s : I → Ω) :
    tv (imageLaw (sampleScan guides base hb pair refresh k s))
      (FiniteChain.kernel (density p) (scanFlow p guides base Q) s)≤
      2*(1+updateCount guides base)/(2:ℝ)^k+e := by
  have ht := WeightedOptions.drawThen_tv_on (scanChoice guides base hb) (localSampler pair refresh s)
    k (updateKernel p Q s) e (fun u hu=>
      localSampler_tv_on p Q guides base pair refresh e he hpr hr s u (scanChoice_support guides base hb u hu))
  have hl : Variation.bind (fun u=>((scanChoice guides base hb).law u:ℝ)) (updateKernel p Q s)=
      FiniteChain.kernel (density p) (scanFlow p guides base Q) s := by
    funext t
    rw [scanChoice_law,localScan_kernel p hp hs guides hself base Q]
  rw [hl,scanChoice_size] at ht
  simpa only [Nat.cast_add,Nat.cast_one,sampleScan] using ht



open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma metropolis_normalize (P : SymmetricProposal Ω) (u : Ω → ℝ) (hu : ∀ a,0<u a)
    (c : ℝ) (hc : 0<c) (a b : Ω) :
    metropolis P (fun x=>u x/c) a b=metropolis P u a b := by
  have huc : ∀ x,0<u x/c:=fun x=>div_pos (hu x) hc
  have hf := WeightedOptions.row_eq_of_off _ _ (metropolis_row P _ huc a)
    (metropolis_row P _ hu a) a (fun b hab=>?_)
  · exact congrFun hf b
  rw [metropolis_acceptance _ _ huc _ _ hab,metropolis_acceptance _ _ hu _ _ hab]
  congr 2
  field_simp

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Transport.Sparse

open Finset Replica Variation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

attribute [local instance] finsetOrder pmOrder

def rationalWeight (w : E → ℚ) (A : PM (fun e v=>v∈ends e)) : ℚ := ∏ e∈A.val,w e

omit [DecidableEq V] [Fintype E] [LinearOrder E] in
lemma rationalWeight_pos [DecidableEq V] [Fintype E] [LinearOrder E]
    (w : E → ℚ) (hw : ∀ e,0<w e) (A : PM (fun e v=>v∈ends e)) :
    0<rationalWeight ends w A := prod_pos (fun e _=>hw e)

omit [DecidableEq V] [Fintype E] [LinearOrder E] in
lemma rationalWeight_cast [DecidableEq V] [Fintype E] [LinearOrder E]
    (w : E → ℚ) (A : PM (fun e v=>v∈ends e)) :
    (rationalWeight ends w A:ℝ)=matchingWeight (fun e=>(w e:ℝ)) A := by
  simp [rationalWeight,matchingWeight]

def rationalPairWeight (w z : E → ℚ) (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) : ℚ :=
  rationalWeight ends w a.1*rationalWeight ends z a.2

lemma rationalPairWeight_pos (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) : 0<rationalPairWeight ends w z a :=
  mul_pos (rationalWeight_pos ends w hw a.1) (rationalWeight_pos ends z hz a.2)

def pairStepTable (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) :=
  (pairTable ends hloop hpar a).metropolisChoice (rationalPairWeight ends w z)
    (rationalPairWeight_pos ends w z hw hz) a

theorem pairStepTable_law (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a b : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) :
    ((pairStepTable ends hloop hpar w z hw hz a).law b:ℝ)=
      metropolis (pairProposal ends hloop hpar) (pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))) a b := by
  rw [pairStepTable,WeightedOptions.metropolisChoice_law (pairProposal ends hloop hpar)
    (pairTable ends hloop hpar) (pairTable_law ends hloop hpar)]
  have hw' : ∀ e,(0:ℝ)<w e:=fun e=>by exact_mod_cast hw e
  have hz' : ∀ e,(0:ℝ)<z e:=fun e=>by exact_mod_cast hz e
  let c:=partition (inc:=fun e v=>v∈ends e) (fun e=>(w e:ℝ))*
    partition (inc:=fun e v=>v∈ends e) (fun e=>(z e:ℝ))
  have hc : 0<c:=mul_pos (partition_pos _ hw' a.1) (partition_pos _ hz' a.2)
  have he : pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))=
      (fun x=>(rationalPairWeight ends w z x:ℝ)/c) := by
    funext x
    simp only [pairLaw,gibbs,rationalPairWeight,Rat.cast_mul,rationalWeight_cast,c]
    exact div_mul_div_comm _ _ _ _
  rw [he,metropolis_normalize _ _ (fun x=>by exact_mod_cast rationalPairWeight_pos ends w z hw hz x) c hc]

theorem pairStepTable_tv (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) (k : ℕ) :
    tv (imageLaw ((pairStepTable ends hloop hpar w z hw hz a).draw k))
      (metropolis (pairProposal ends hloop hpar) (pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))) a) ≤
      4*(8*a.1.val.card.choose 2+2*a.1.val.card+(a.1.val.card+a.2.val.card)+3)/(2:ℝ)^k := by
  have ht := (pairStepTable ends hloop hpar w z hw hz a).draw_tv k
  have hl : (fun b=>((pairStepTable ends hloop hpar w z hw hz a).law b:ℝ))=
      metropolis (pairProposal ends hloop hpar) (pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))) a :=
    funext (pairStepTable_law ends hloop hpar w z hw hz a)
  rw [hl] at ht
  apply ht.trans
  rw [pairStepTable,WeightedOptions.metropolisChoice_size]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs := pairTable_size ends hloop hpar a
  have hs' : ((pairTable ends hloop hpar a).size:ℝ)≤
      8*a.1.val.card.choose 2+2*a.1.val.card+(a.1.val.card+a.2.val.card)+3 := by exact_mod_cast hs
  push_cast
  nlinarith

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS.FiniteChoice

lemma choose_pos {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ i,p i=1)
    (hK : 0<K) (J : Fin K) : 0<p (choose p hs hK J) := by
  have hl := choose_lower p hs hK J
  have hu := choose_upper p hs hK J
  have hd := cumulative_step p (choose p hs hK J)
  linarith

lemma chooseBits_pos {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i,p i=1)
    (k : ℕ) (bits : Fin k → Bool) : 0<p (chooseBits p hs k bits) :=
  choose_pos p hs _ _

end MatchingFPRAS.FiniteChoice

namespace MatchingFPRAS.UnitRefresh

instance {α : Type*} [Finite α] : Finite (Pairing α) := by
  apply Finite.of_injective Pairing.mate
  intro p q h
  cases p; cases q
  simp only [Pairing.mk.injEq] at *
  exact h

noncomputable instance {α : Type*} [Fintype α] : Fintype (Pairing α) := Fintype.ofFinite _

variable {α β : Type*}

variable [DecidableEq α]

universe u



open Finset Polynomial

def completionSum (a : ℕ) : ℕ[X] →+ ℕ where
  toFun p := p.sum (fun k c => c * pairingCount (a+k))
  map_zero' := Polynomial.sum_zero_index _
  map_add' p q := Polynomial.sum_add_index p q _ (by simp) (by intros; exact Nat.add_mul ..)

@[simp] lemma completion_monomial (a k c : ℕ) :
    completionSum a (monomial k c)=c*pairingCount (a+k) := by
  change (monomial k c : ℕ[X]).sum (fun j d => d * pairingCount (a+j)) = _
  exact Polynomial.sum_monomial_index c _ (Nat.zero_mul _)

noncomputable def interfacePolynomial (s : ℕ) (F : Fin (s+1) → ℕ) : ℕ[X] :=
  ∑ l : Fin (s+1), monomial (s-l.val) (s.choose l.val * F l)

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def convolution (s : I → ℕ) (F : ∀ i, Fin (s i+1) → ℕ) : ℕ[X] :=
  ∏ i, interfacePolynomial (s i) (F i)

omit [Fintype I] in
lemma prod_monomials (t : Finset I) (n c : I → ℕ) :
    (∏ i ∈ t, monomial (n i) (c i) : ℕ[X]) = monomial (∑ i ∈ t,n i) (∏ i ∈ t,c i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi,ih,Polynomial.monomial_mul_monomial]

theorem convolution_recurrence (s : I → ℕ) (F : ∀ i, Fin (s i+1) → ℕ) (u k : ℕ) :
    completionSum (u+k) (convolution s F) =
      ∑ l : ∀ i, Fin (s i+1),
        pairingCount (u+k+(∑ i, (s i - (l i).val))) * (∏ i, ((s i).choose (l i).val * F i (l i))) := by
  classical
  unfold convolution interfacePolynomial
  rw [Fintype.prod_sum,map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [prod_monomials,completion_monomial,Nat.mul_comm]



open Finset Polynomial

lemma interface_natDegree (s : ℕ) (F : Fin (s+1) → ℕ) :
    (interfacePolynomial s F).natDegree ≤ s := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l hl
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma convolution_natDegree (s : I → ℕ) (F : ∀ i, Fin (s i+1) → ℕ) :
    (convolution s F).natDegree ≤ ∑ i,s i := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  exact Finset.sum_le_sum fun i _ => interface_natDegree (s i) (F i)

omit [DecidableEq I] in
theorem convolution_finite_evaluation (s : I → ℕ) (F : ∀ i, Fin (s i+1) → ℕ)
    (N u k : ℕ) (hN : (∑ i,s i) ≤ N) :
    completionSum (u+k) (convolution s F) =
      ∑ a ∈ Finset.range (N+1), (convolution s F).coeff a * pairingCount (u+k+a) := by
  change (convolution s F).sum (fun a c => c * pairingCount (u+k+a)) = _
  apply Polynomial.sum_eq_of_subset
  · simp
  · intro a ha
    apply Finset.mem_range.mpr
    by_contra hn
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (convolution_natDegree s F |>.trans hN) (by omega : N<a))
    exact Polynomial.mem_support_iff.mp ha hz



def Pairing.sigma {L : Type*} {A : L → Type*} (p : ∀ l, Pairing (A l)) : Pairing (Sigma A) where
  mate x := ⟨x.1,(p x.1).mate x.2⟩
  involutive x := by
    cases x with
    | mk l x => exact congrArg (Sigma.mk l) ((p l).involutive x)
  no_fixed x h := by
    have he : (p x.1).mate x.2=x.2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact (p x.1).no_fixed x.2 he

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

structure ColoredPairing (bags : V → Finset L) where
  pair : Pairing V
  color : V → L
  allowed : ∀ x, color x ∈ bags x
  same_color : ∀ x, color (pair.mate x)=color x

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
@[ext] lemma ColoredPairing.ext {bags : V → Finset L} {p q : ColoredPairing bags}
    (hp : p.pair=q.pair) (hc : p.color=q.color) : p=q := by
  cases p; cases q; simp_all

instance (bags : V → Finset L) : Finite (ColoredPairing bags) :=
  Finite.of_injective (fun p : ColoredPairing bags => (p.pair,p.color)) (by
    intro p q h
    exact ColoredPairing.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance (bags : V → Finset L) : Fintype (ColoredPairing bags) := Fintype.ofFinite _

abbrev Assignment (bags : V → Finset L) := {f : V → L // ∀ x, f x ∈ bags x}

def ColoredPairing.fiber {bags : V → Finset L} (p : ColoredPairing bags) (l : L) :
    Pairing {x : V // p.color x=l} where
  mate x := ⟨p.pair.mate x,(p.same_color x).trans x.property⟩
  involutive x := Subtype.ext (p.pair.involutive x)
  no_fixed x h := p.pair.no_fixed x (congrArg Subtype.val h)

def ColoredPairing.glue (bags : V → Finset L) (f : Assignment bags)
    (p : ∀ l,Pairing {x : V // f.val x=l}) : ColoredPairing bags where
  pair := (Pairing.sigma p).map (Equiv.sigmaFiberEquiv f.val)
  color := f.val
  allowed := f.property
  same_color x := (p (f.val x)).mate ⟨x,rfl⟩ |>.property

def assignmentPairingEquiv (bags : V → Finset L) :
    ColoredPairing bags ≃ Σ f : Assignment bags, ∀ l, Pairing {x : V // f.val x=l} where
  toFun p := ⟨⟨p.color,p.allowed⟩,p.fiber⟩
  invFun q := ColoredPairing.glue bags q.1 q.2
  left_inv p := by
    apply ColoredPairing.ext
    · ext x; rfl
    · rfl
  right_inv q := by
    rcases q with ⟨f,p⟩
    change (⟨f,(ColoredPairing.glue bags f p).fiber⟩ :
      Σ f : Assignment bags, ∀ l, Pairing {x : V // f.val x=l}) = ⟨f,p⟩
    apply congrArg (fun q : ∀ l, Pairing {x : V // f.val x=l} =>
      (⟨f,q⟩ : Σ f : Assignment bags, ∀ l, Pairing {x : V // f.val x=l}))
    funext l
    ext x
    change ((p (f.val x)).mate ⟨x,rfl⟩).val = ((p l).mate x).val
    obtain ⟨x,hx⟩ := x
    dsimp at hx ⊢
    subst l
    rfl

theorem coloredPairing_card (bags : V → Finset L) :
    Fintype.card (ColoredPairing bags) =
      ∑ f : Assignment bags, ∏ l : L, pairingCount (Fintype.card {x : V // f.val x=l}) := by
  classical
  rw [Fintype.card_congr (assignmentPairingEquiv bags),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro l hl
  exact pairing_card

end MatchingFPRAS.UnitRefresh

end OAI
