import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.LocalVariance
import OAI.Combinatorics.MatchingCount.Sampling.Certify

namespace OAI

namespace MatchingFPRAS.Transport.Sparse

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

instance decideOverlay (U : Finset E) :
    DecidableRel (overlayLineGraph (fun e v => v ∈ ends e) U).Adj := by
  intro e f
  change Decidable (e ≠ f ∧ e ∈ U ∧ f ∈ U ∧ ∃ v, v ∈ ends e ∧ v ∈ ends f)
  infer_instance

def component (U : Finset E) (a : E) : Finset E :=
  U ∩ ComputableReach.closure (overlayLineGraph (fun e v => v ∈ ends e) U) a

lemma component_eq (U : Finset E) (a : E) :
    component ends U a = componentEdges (inc:=fun e v => v ∈ ends e) U a := by
  ext e
  simp only [component,mem_inter,ComputableReach.mem_closure,mem_componentEdges]

def allComponents (U : Finset E) : Finset (Finset E) := U.image (component ends U)

lemma allComponents_eq (U : Finset E) :
    allComponents ends U = components (inc:=fun e v => v ∈ ends e) U := by
  simp only [allComponents,components]
  exact Finset.image_congr (fun a _ => component_eq ends U a)

def discrepancies (A B : PM (fun e v => v ∈ ends e)) : Finset (Finset E) :=
  (allComponents ends (A.val ∪ B.val)).filter (fun S => ¬S ⊆ A.val ∩ B.val)

lemma discrepancies_eq (A B : PM (fun e v => v ∈ ends e)) :
    discrepancies ends A B = discrepancyComponents A B := by
  rw [discrepancies,allComponents_eq]
  rfl

def cycle (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e))
    (S : Finset E) : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e) :=
  if h : S ∈ allComponents ends (p.1.val ∪ p.2.val) then
    (⟨exchange p.1.val p.2.val S,exchange_matching p.1.property p.2.property
        (component_exchange_compatible (by rwa [allComponents_eq] at h))⟩,
     ⟨exchange p.2.val p.1.val S,exchange_matching p.2.property p.1.property
        (component_exchange_compatible (by rwa [allComponents_eq] at h)).symm⟩)
  else p

lemma cycle_eq (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) (S : Finset E) :
    cycle ends p S = cycleMove p S := by
  unfold cycle cycleMove
  simp only [allComponents_eq]

lemma discrepancies_card (A B : PM (fun e v => v ∈ ends e)) :
    (discrepancies ends A B).card ≤ A.val.card+B.val.card := by
  calc
    _ ≤ (allComponents ends (A.val ∪ B.val)).card := card_filter_le _ _
    _ ≤ (A.val ∪ B.val).card := card_image_le
    _ ≤ _ := card_union_le _ _

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS

structure WeightedOptions (Ω : Type*) where
  size : ℕ
  out : Fin size → Ω
  mass : Fin size → ℚ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

namespace WeightedOptions

open Finset

variable {Ω Ψ : Type*}

def pure (a : Ω) : WeightedOptions Ω where
  size := 1
  out := fun _ => a
  mass := fun _ => 1
  nonneg := by simp
  total := by simp

def map (f : Ω → Ψ) (c : WeightedOptions Ω) : WeightedOptions Ψ where
  size := c.size
  out := f ∘ c.out
  mass := c.mass
  nonneg := c.nonneg
  total := c.total

def mix (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : WeightedOptions Ω) : WeightedOptions Ω where
  size := a.size+b.size
  out := Fin.addCases a.out b.out
  mass := Fin.addCases (fun i => p*a.mass i) (fun i => (1-p)*b.mass i)
  nonneg i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
      exact mul_nonneg hp (a.nonneg i)
    · simp only [Fin.addCases_right]
      exact mul_nonneg (sub_nonneg.mpr hp1) (b.nonneg i)
  total := by
    simp only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,←mul_sum,a.total,b.total]
    ring

variable [DecidableEq Ω]

def law (c : WeightedOptions Ω) (b : Ω) : ℚ := ∑ i, if c.out i=b then c.mass i else 0

lemma law_nonneg (c : WeightedOptions Ω) (b : Ω) : 0 ≤ c.law b := by
  apply sum_nonneg
  intro i _
  split_ifs <;> [exact c.nonneg i; exact le_rfl]

lemma law_sum [Fintype Ω] (c : WeightedOptions Ω) : ∑ b, c.law b=1 := by
  unfold law
  rw [sum_comm]
  simpa using c.total

@[simp] lemma pure_law (a b : Ω) : (pure a).law b=if a=b then 1 else 0  := by
  change (∑ _i : Fin 1, if a=b then (1:ℚ) else 0)=_
  simp

lemma mix_law (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a b : WeightedOptions Ω) (x : Ω) :
    (mix p hp hp1 a b).law x=p*a.law x+(1-p)*b.law x := by
  change (∑ i : Fin (a.size+b.size), if Fin.addCases a.out b.out i=x then
    Fin.addCases (fun i=>p*a.mass i) (fun i=>(1-p)*b.mass i) i else (0:ℚ))=_
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,law,mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro i _ <;> split_ifs <;> simp

lemma sum_law_mul [Fintype Ω] (c : WeightedOptions Ω) (f : Ω → ℚ) :
    ∑ b, c.law b*f b = ∑ i, c.mass i*f (c.out i) := by
  simp only [law,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [ite_mul,zero_mul]
  simp

lemma map_law [Fintype Ω] [DecidableEq Ψ] (f : Ω → Ψ) (c : WeightedOptions Ω) (b : Ψ) :
    (c.map f).law b = ∑ a, if f a=b then c.law a else 0 := by
  change (∑ i : Fin c.size, if f (c.out i)=b then c.mass i else (0:ℚ))=_
  calc
    _ = ∑ i, c.mass i*(if f (c.out i)=b then 1 else 0) := by
      simp only [mul_ite,mul_one,mul_zero]
    _ = ∑ a, c.law a*(if f a=b then 1 else 0) :=
      (c.sum_law_mul (fun a => if f a=b then (1:ℚ) else 0)).symm
    _ = _ := by simp

lemma map_first_law [DecidableEq Ψ] (c : WeightedOptions Ω) (a : Ψ) (b : Ω × Ψ) :
    (c.map (fun x => (x,a))).law b = if a=b.2 then c.law b.1 else 0 := by
  change (∑ i : Fin c.size, if (c.out i,a)=b then c.mass i else (0:ℚ))=_
  rcases b with ⟨b,d⟩
  by_cases h : a=d
  · subst d
    simp [law]
  · simp [h]

def accept (c : WeightedOptions Ω) (hold : Ω) (p : Ω → ℚ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) : WeightedOptions Ω where
  size := c.size+c.size
  out := Fin.addCases c.out (fun _ => hold)
  mass := Fin.addCases (fun i => c.mass i*p (c.out i))
    (fun i => c.mass i*(1-p (c.out i)))
  nonneg i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
      exact mul_nonneg (c.nonneg i) (hp _)
    · simp only [Fin.addCases_right]
      exact mul_nonneg (c.nonneg i) (sub_nonneg.mpr (hp1 _))
  total := by
    simp only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,←sum_add_distrib]
    simp only [←mul_add,add_sub_cancel,mul_one,c.total]

lemma accept_law (c : WeightedOptions Ω) (hold : Ω) (p : Ω → ℚ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) (b : Ω) :
    (c.accept hold p hp hp1).law b = c.law b*p b +
      if hold=b then ∑ i, c.mass i*(1-p (c.out i)) else 0 := by
  change (∑ i : Fin (c.size+c.size), if Fin.addCases c.out (fun _=>hold) i=b then
    Fin.addCases (fun i=>c.mass i*p (c.out i)) (fun i=>c.mass i*(1-p (c.out i))) i
    else (0:ℚ))=_
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  congr 1
  · rw [law,sum_mul]
    apply sum_congr rfl
    intro i _
    split_ifs with h
    · rw [h]
    · simp
  · split_ifs <;> simp_all

variable [LinearOrder Ω]

def numbering (s : Finset Ω) : Fin s.card ≃ ↥s := (s.orderIsoOfFin rfl).toEquiv

def uniform (s : Finset Ω) (hs : s.Nonempty) : WeightedOptions Ω where
  size := s.card
  out := fun i => (numbering s i).val
  mass := fun _ => (s.card:ℚ)⁻¹
  nonneg := by intro i; positivity
  total := by
    have h : (s.card:ℚ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    simp [h]

lemma uniform_law (s : Finset Ω) (hs : s.Nonempty) (b : Ω) :
    (uniform s hs).law b=if b ∈ s then (s.card:ℚ)⁻¹ else 0 := by
  unfold law uniform
  change (∑ i, if (numbering s i).val=b then (s.card:ℚ)⁻¹ else 0)=_
  rw [(numbering s).sum_comp (fun i : ↥s => if i.val=b then (s.card:ℚ)⁻¹ else 0)]
  rw [Finset.sum_coe_sort s (fun x : Ω => if x=b then (s.card:ℚ)⁻¹ else 0)]
  simp

def neighbors (a : Ω) (s : Finset Ω) (d : ℕ) (hd : s.card ≤ d) : WeightedOptions Ω where
  size := s.card+1
  out := Fin.lastCases a (fun i => (numbering s i).val)
  mass := Fin.lastCases (1-(s.card:ℚ)/d) (fun _ => (d:ℚ)⁻¹)
  nonneg i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
      by_cases h : d=0
      · simp [h]
      · have hh : (0:ℚ)<d := by exact_mod_cast Nat.pos_of_ne_zero h
        exact sub_nonneg.mpr ((div_le_one hh).mpr (by exact_mod_cast hd))
    · simp only [Fin.lastCases_castSucc]
      positivity
  total := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,sum_const,card_fin,nsmul_eq_mul]
    ring

lemma neighbors_law (a : Ω) (s : Finset Ω) (d : ℕ) (hd : s.card ≤ d) (b : Ω) :
    (neighbors a s d hd).law b=(if b ∈ s then (d:ℚ)⁻¹ else 0)+
      (if a=b then 1-(s.card:ℚ)/d else 0) := by
  unfold law neighbors
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
  congr 1
  rw [(numbering s).sum_comp (fun i : ↥s => if i.val=b then (d:ℚ)⁻¹ else 0)]
  rw [Finset.sum_coe_sort s (fun x : Ω => if x=b then (d:ℚ)⁻¹ else 0)]
  simp

end WeightedOptions

end MatchingFPRAS

namespace MatchingFPRAS.Transport.Sparse

open Finset WeightedOptions

variable {Ω : Type*} [Fintype Ω] [LinearOrder Ω] [DecidableEq Ω]

omit [LinearOrder Ω] in
lemma erased_eq (R : Ω → Ω → Prop) (s : Finset Ω) (a : Ω)
    (hs : ∀ b, b ∈ s ↔ R a b) : s.erase a = relationDestinations R a := by
  classical
  ext b
  simp only [mem_erase,relationDestinations,mem_filter,mem_univ,true_and,hs,ne_comm]

lemma neighbors_real (R : Ω → Ω → Prop) (s : Finset Ω) (d : ℕ) (a b : Ω)
    (hs : s=relationDestinations R a) (hd : s.card ≤ d) :
    ((WeightedOptions.neighbors a s d hd).law b : ℝ) = relationProposal R d a b := by
  classical
  rw [WeightedOptions.neighbors_law]
  push_cast
  subst s
  rw [relationProposal,relationOff_sum]
  by_cases hab : a=b
  · subst b
    simp [relationDestinations]
  · simp only [hab,ite_false,relationOff]
    split_ifs <;> push_cast <;> simp

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

local instance finsetOrder : LinearOrder (Finset E) :=
  LinearOrder.lift' toColex toColex.injective

local instance pmOrder : LinearOrder (PM (fun e v => v ∈ ends e)) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

lemma color_degree (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : ((colors ends A).erase A).card ≤ Fintype.card V :=
  (card_erase_le).trans ((colors_card ends hpar A).trans_eq (A.twice_card ends hloop))

lemma switch_degree (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) :
    ((switches ends A).erase A).card ≤ 8*(Fintype.card V/2).choose 2 := by
  have h : Fintype.card V/2=A.val.card := by have := A.twice_card ends hloop; omega
  rw [h]
  exact card_erase_le.trans (switches_card ends hpar A)

def colorTable (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : WeightedOptions (PM (fun e v => v ∈ ends e)) :=
  WeightedOptions.neighbors A ((colors ends A).erase A) (Fintype.card V)
    (color_degree ends hloop hpar A)

def switchTable (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : WeightedOptions (PM (fun e v => v ∈ ends e)) :=
  WeightedOptions.neighbors A ((switches ends A).erase A) (8*(Fintype.card V/2).choose 2)
    (switch_degree ends hloop hpar A)

lemma colorTable_law (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) :
    ((colorTable ends hloop hpar A).law B : ℝ)=colorProposal ends A B := by
  exact neighbors_real (ColorChange ends) ((colors ends A).erase A) (Fintype.card V) A B
    (erased_eq _ _ _ (mem_colors ends A)) (color_degree ends hloop hpar A)

lemma switchTable_law (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) :
    ((switchTable ends hloop hpar A).law B : ℝ)=switchProposal ends A B := by
  exact neighbors_real (fun A B => TwoEdgeSwitch A B) ((switches ends A).erase A)
    (8*(Fintype.card V/2).choose 2) A B
    (erased_eq _ _ _ (mem_switches ends A)) (switch_degree ends hloop hpar A)

def cycleTable (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    WeightedOptions (PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :=
  if h : (discrepancies ends p.1 p.2).Nonempty then
    (WeightedOptions.uniform _ h).map (cycle ends p)
  else WeightedOptions.pure p

lemma cycleTable_law (p q : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    ((cycleTable ends p).law q : ℝ)=cycleProposal p q := by
  classical
  by_cases h : (discrepancies ends p.1 p.2).Nonempty
  · have h' : (discrepancyComponents p.1 p.2).Nonempty := by rwa [←discrepancies_eq]
    rw [cycleTable,dite_eq_left h,cycleProposal,ite_eq_left h',WeightedOptions.map_law]
    push_cast
    apply sum_congr rfl
    intro S _
    rw [WeightedOptions.uniform_law,cycle_eq,discrepancies_eq]
    unfold cycleTerm
    split_ifs <;> simp_all
  · have h' : ¬(discrepancyComponents p.1 p.2).Nonempty := by rwa [←discrepancies_eq]
    rw [cycleTable,dite_eq_right h,cycleProposal,ite_eq_right h',WeightedOptions.pure_law]
    split_ifs <;> norm_num

def pairTable (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    WeightedOptions (PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :=
  WeightedOptions.mix (1/3) (by norm_num) (by norm_num)
    ((switchTable ends hloop hpar p.1).map (fun x => (x,p.2)))
    (WeightedOptions.mix (1/2) (by norm_num) (by norm_num)
      ((colorTable ends hloop hpar p.1).map (fun x => (x,p.2)))
      (cycleTable ends p))

lemma pairTable_law (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (p q : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    ((pairTable ends hloop hpar p).law q : ℝ)=pairProposalRaw ends p q := by
  unfold pairTable
  rw [WeightedOptions.mix_law,WeightedOptions.mix_law,
    WeightedOptions.map_first_law,WeightedOptions.map_first_law]
  push_cast
  unfold pairProposalRaw firstLift
  by_cases h : p.2=q.2
  · simp only [ite_eq_left h]
    rw [switchTable_law,colorTable_law,cycleTable_law]
    ring
  · simp only [ite_eq_right h]
    push_cast
    rw [cycleTable_law]
    ring

lemma pairTable_size (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    (pairTable ends hloop hpar p).size ≤
      8*p.1.val.card.choose 2 + 2*p.1.val.card + (p.1.val.card+p.2.val.card)+3 := by
  have hs : ((switches ends p.1).erase p.1).card ≤ 8*p.1.val.card.choose 2 := card_erase_le.trans (switches_card ends hpar p.1)
  have hc : ((colors ends p.1).erase p.1).card ≤ 2*p.1.val.card := card_erase_le.trans (colors_card ends hpar p.1)
  have hy := discrepancies_card ends p.1 p.2
  simp only [pairTable,WeightedOptions.mix,WeightedOptions.map,switchTable,colorTable,
    WeightedOptions.neighbors]
  have hz : (cycleTable ends p).size ≤ p.1.val.card+p.2.val.card+1 := by
    unfold cycleTable
    split_ifs <;> simp only [WeightedOptions.map,WeightedOptions.uniform,WeightedOptions.pure]
    · omega
    · omega
  omega

end MatchingFPRAS.Transport.Sparse

end OAI
