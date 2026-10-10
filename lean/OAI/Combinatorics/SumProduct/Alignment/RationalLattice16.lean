import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PolynomialArray01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalPolynomialMap
lemma finset_sum {σ ι : Type*} (s : Finset ι) {f : ι → (σ → ℝ) → ℝ}
    (hf : ∀ i∈s,IsPolynomial (f i)) : IsPolynomial (fun x=>∑ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (σ:=σ))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using add (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))
end RationalPolynomialMap
namespace RationalLattice.PolynomialArrays
open WeightedPolynomial MalcevCharacters PolynomialArrayInterpolation
open CorrectedBoxLeibman (gridEval)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)

def weight (a : Index w q) : ℕ:=w a.1

lemma toLog_weighted (u : Fin q → ℝ) (i : Fin n) :
    IsWeighted (weight (q:=q) w) (w i) (fun x=>toLog w x u i) := by
  apply IsWeighted.sum
  intro e he
  unfold fullCoeff
  split_ifs with h
  · simpa only [mul_comm,weight] using (IsWeighted.coordinate (weight w) ⟨i,⟨e,h⟩⟩).smul
      (∏ j,u j^(e j).val)
  · simpa only [zero_mul] using IsWeighted.const (weight (q:=q) w) (w i) 0

lemma toLog_integer_polynomial (z : Fin q → ℤ) (i : Fin n) :
    RationalPolynomialMap.IsPolynomial (fun x=>toLog w x (fun j=>(z j:ℝ)) i) := by
  apply RationalPolynomialMap.finset_sum
  intro e he
  have hp : (∏ j,(z j:ℝ)^(e j).val)=((∏ j,(z j:ℚ)^(e j).val:ℚ):ℝ) := by push_cast; rfl
  unfold fullCoeff
  split_ifs with h
  · rw [hp]
    exact RationalPolynomialMap.mul (RationalPolynomialMap.coordinate (⟨i,⟨e,h⟩⟩ : Index w q))
      (RationalPolynomialMap.const _)
  · simpa only [zero_mul] using RationalPolynomialMap.zero

def multiply (x : (Index w q ⊕ Index w q) → ℝ) (a : Index w q) : ℝ:=
  PolynomialArrayInterpolation.coefficients (fun u=>canonicalLog c
    (canonicalExp c (toLog w (fun j=>x (Sum.inl j)) u)*
      canonicalExp c (toLog w (fun j=>x (Sum.inr j)) u)) a.1) a.2.val

omit [IsTopologicalGroup G] in
lemma multiply_polynomial (a : Index w q) :
    RationalPolynomialMap.IsPolynomial (fun x=>multiply c w x a) := by
  apply RationalPolynomialMap.finset_sum
  intro v hv
  apply RationalPolynomialMap.mul (RationalPolynomialMap.const _)
  have hl (i : Fin n):=RationalPolynomialMap.comp
    (toLog_integer_polynomial w (fun j=>((v j).val:ℤ)) i)
    (fun k=>RationalPolynomialMap.coordinate (Sum.inl k : Index w q ⊕ Index w q))
  have hr (i : Fin n):=RationalPolynomialMap.comp
    (toLog_integer_polynomial w (fun j=>((v j).val:ℤ)) i)
    (fun k=>RationalPolynomialMap.coordinate (Sum.inr k : Index w q ⊕ Index w q))
  have he (i : Fin n):=RationalPolynomialMap.comp (canonicalExp_polynomial c i) hl
  have hf (i : Fin n):=RationalPolynomialMap.comp (canonicalExp_polynomial c i) hr
  have hm:=polynomialMap_mul c he hf
  have hh:=RationalPolynomialMap.comp (canonicalLog_polynomial c a.1) hm
  simpa only [Homeomorph.symm_apply_apply,Int.cast_natCast] using hh

include hsk hA in
lemma multiply_weighted (a : Index w q) :
    IsWeighted (Sum.elim (weight w) (weight w)) (weight w a) (fun x=>multiply c w x a) := by
  apply IsWeighted.sum
  intro v hv
  apply IsWeighted.smul
  have hin (j : Fin n ⊕ Fin n) :
      IsWeighted (Sum.elim (weight w) (weight w)) (Sum.elim w w j)
        (fun x=>Sum.elim
          (toLog w (fun k=>x (Sum.inl k)) (fun k=>((v k).val:ℝ)))
          (toLog w (fun k=>x (Sum.inr k)) (fun k=>((v k).val:ℝ))) j) := by
    cases j with
    | inl j => exact (toLog_weighted w _ j).comp (fun k=>IsWeighted.coordinate _ (Sum.inl k))
    | inr j => exact (toLog_weighted w _ j).comp (fun k=>IsWeighted.coordinate _ (Sum.inr k))
  have hm:=(log_multiplication_weighted c hsk A w hA a.1).comp hin
  simpa only [Sum.elim_inl,Sum.elim_inr,weight] using hm

lemma coefficientHomeomorph_mul (f g : group (q:=q) c hsk A w hA) :
    coefficientHomeomorph c hsk A w hA (f*g)=multiply c w
      (Sum.elim (coefficientHomeomorph c hsk A w hA f)
        (coefficientHomeomorph c hsk A w hA g)) := by
  funext a
  change coefficients c hsk A w hA (f*g) a=_
  unfold multiply
  simp only [Sum.elim_inl,Sum.elim_inr]
  change _=PolynomialArrayInterpolation.coefficients (fun u=>canonicalLog c
    (canonicalExp c (toLog w (coefficients c hsk A w hA f) u)*
      canonicalExp c (toLog w (coefficients c hsk A w hA g) u)) a.1) a.2.val
  simp only [toLog_coefficients,canonicalExp_log]
  rfl

end RationalLattice.PolynomialArrays
end
 
end

section
 

noncomputable section
namespace RationalLattice.FiniteWeightedLawChart
open WeightedPolynomial
variable {σ K : Type*} [Fintype σ] [Group K] [TopologicalSpace K]
variable (e : K ≃ₜ (σ → ℝ)) (he : e 1=0) (w : σ → ℕ) (hw : ∀ i,0<w i)

def reindex : K ≃ₜ (Fin (Fintype.card σ) → ℝ) where
  toFun g i:=e g (SortedFiniteWeights.indexing w i)
  invFun x:=e.symm (fun a=>x ((SortedFiniteWeights.indexing w).symm a))
  left_inv g:=by apply e.injective; simp
  right_inv x:=by funext i; simp
  continuous_toFun:=continuous_pi (fun i=>(continuous_apply _).comp e.continuous)
  continuous_invFun:=e.symm.continuous.comp (continuous_pi (fun a=>continuous_apply _))

include he in
lemma reindex_one : reindex e w 1=0 := by ext i; exact congrFun he _

def law (x : (σ ⊕ σ) → ℝ) (a : σ) : ℝ:=
  e (e.symm (fun j=>x (Sum.inl j))*e.symm (fun j=>x (Sum.inr j))) a

def reshuffle (x : (Fin (Fintype.card σ) ⊕ Fin (Fintype.card σ)) → ℝ) : (σ ⊕ σ) → ℝ:=
  Sum.elim (fun a=>x (Sum.inl ((SortedFiniteWeights.indexing w).symm a)))
    (fun a=>x (Sum.inr ((SortedFiniteWeights.indexing w).symm a)))

lemma law_reindex (x : (Fin (Fintype.card σ) ⊕ Fin (Fintype.card σ)) → ℝ)
    (i : Fin (Fintype.card σ)) :
    WeightedLawChart.law (reindex e w) x i=law e (reshuffle w x) (SortedFiniteWeights.indexing w i) := rfl

lemma reshuffle_polynomial (a : σ ⊕ σ) :
    RationalPolynomialMap.IsPolynomial (fun x=>reshuffle w x a) := by
  cases a with
  | inl a => exact RationalPolynomialMap.coordinate _
  | inr a => exact RationalPolynomialMap.coordinate _

lemma reshuffle_weighted (a : σ ⊕ σ) :
    IsWeighted (Sum.elim (fun i=>w (SortedFiniteWeights.indexing w i))
      (fun i=>w (SortedFiniteWeights.indexing w i))) (Sum.elim w w a)
      (fun x=>reshuffle w x a) := by
  cases a with
  | inl a =>
      simpa only [reshuffle,Sum.elim_inl,Equiv.apply_symm_apply] using (IsWeighted.coordinate
        (Sum.elim (fun i=>w (SortedFiniteWeights.indexing w i))
          (fun i=>w (SortedFiniteWeights.indexing w i)))
        (Sum.inl ((SortedFiniteWeights.indexing w).symm a)))
  | inr a =>
      simpa only [reshuffle,Sum.elim_inr,Equiv.apply_symm_apply] using (IsWeighted.coordinate
        (Sum.elim (fun i=>w (SortedFiniteWeights.indexing w i))
          (fun i=>w (SortedFiniteWeights.indexing w i)))
        (Sum.inr ((SortedFiniteWeights.indexing w).symm a)))

variable (hp : ∀ a,RationalPolynomialMap.IsPolynomial (fun x=>law e x a))
variable (hb : ∀ a,IsWeighted (Sum.elim w w) (w a) (fun x=>law e x a))
def chart : RealCoordinates K (Fintype.card σ):=
  WeightedLawChart.realCoordinates (reindex e w) (reindex_one e he w)
    (fun i=>w (SortedFiniteWeights.indexing w i)) (fun i=>hw _)
    (SortedFiniteWeights.indexing_monotone w)
    (fun i=>by simpa only [law_reindex] using
      RationalPolynomialMap.comp (hp (SortedFiniteWeights.indexing w i)) (reshuffle_polynomial w))
    (fun i=>by simpa only [law_reindex] using
      (hb (SortedFiniteWeights.indexing w i)).comp (reshuffle_weighted w))

lemma chart_apply (g : K) (i : Fin (Fintype.card σ)) :
    (chart e he w hw hp hb).coord g i=e g (SortedFiniteWeights.indexing w i) := rfl
lemma chart_symm_apply (x : Fin (Fintype.card σ) → ℝ) :
    (chart e he w hw hp hb).coord.symm x=e.symm
      (fun a=>x ((SortedFiniteWeights.indexing w).symm a)) := rfl

end RationalLattice.FiniteWeightedLawChart
end
 
end

section
 

 

noncomputable section
open scoped BigOperators commutatorElement
namespace RationalLattice.PolynomialArrays
open WeightedPolynomial MalcevCharacters MalcevWeightedCoordinates PolynomialArrayInterpolation
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i)

lemma finite_law_eq (x : (Index w q ⊕ Index w q) → ℝ) (a : Index w q) :
    FiniteWeightedLawChart.law (coefficientHomeomorph c hsk A w hA) x a=multiply c w x a := by
  rw [FiniteWeightedLawChart.law,coefficientHomeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]
  congr 2
  funext j
  cases j <;> rfl

def chart : RealCoordinates (group (q:=q) c hsk A w hA) (Fintype.card (Index w q)) :=
  FiniteWeightedLawChart.chart (coefficientHomeomorph c hsk A w hA)
    (coefficientHomeomorph_one c hsk A w hA) (weight w) (fun a=>hw a.1)
    (fun a=>by simpa only [finite_law_eq] using multiply_polynomial c w a)
    (fun a=>by simpa only [finite_law_eq] using multiply_weighted c hsk A w hA a)

def orderedWeight (i : Fin (Fintype.card (Index w q))) : ℕ:=
  weight w (SortedFiniteWeights.indexing (weight w) i)
include hw in
lemma orderedWeight_pos (i : Fin (Fintype.card (Index w q))) : 0<orderedWeight w i:=hw _
lemma orderedWeight_monotone : Monotone (orderedWeight (q:=q) w):=
  SortedFiniteWeights.indexing_monotone (weight w)

def level (k : ℕ) : Subgroup (group (q:=q) c hsk A w hA) where
  carrier:=fun f=>∀ u,f.val u∈A.level k
  one_mem':=fun _=>(A.level k).one_mem
  mul_mem':=fun hf hg u=>(A.level k).mul_mem (hf u) (hg u)
  inv_mem':=fun hf u=>(A.level k).inv_mem (hf u)

def filtration : CubeFaces.Filtration (group (q:=q) c hsk A w hA) where
  level:=level c hsk A w hA
  antitone:=fun _ _ hij _ hf u=>A.antitone hij (hf u)
  commutator_le i j:=Subgroup.commutator_le.mpr (fun f hf g hg u=>
    (Subgroup.commutator_le.mp (A.commutator_le i j)) (f.val u) (hf u) (g.val u) (hg u))

variable (hmono : Monotone w)
include hmono in
lemma coefficients_adapted (k : ℕ) (f : group (q:=q) c hsk A w hA) :
    f∈level c hsk A w hA k ↔ ∀ a : Index w q,weight w a<k → coefficients c hsk A w hA f a=0 := by
  constructor
  · intro hf a ha
    change ∑ v : Grid q (w a.1),_ =0
    apply Finset.sum_eq_zero
    intro v hv
    dsimp only
    rw [(mem_level_iff_log c A w hmono hA k _).mp (hf _) a.1 ha,mul_zero]
  · intro hf u
    apply (mem_level_iff_log c A w hmono hA k _).mpr
    intro i hi
    rw [← toLog_coefficients c hsk A w hA f u]
    unfold toLog CorrectedBoxLeibman.gridEval
    apply Finset.sum_eq_zero
    intro e he
    unfold fullCoeff
    split_ifs with hd
    · rw [hf ⟨i,⟨e,hd⟩⟩ hi,zero_mul]
    · rw [zero_mul]

include hmono in
lemma chart_adapted (k : ℕ) (f : group (q:=q) c hsk A w hA) :
    f∈(filtration c hsk A w hA).level k ↔ ∀ i,orderedWeight (q:=q) w i<k →
      (chart c hsk A w hA hw).coord f i=0 := by
  rw [show (filtration c hsk A w hA).level k=level c hsk A w hA k from rfl,
    coefficients_adapted c hsk A w hA hmono]
  change (∀ a,weight w a<k → coefficients c hsk A w hA f a=0) ↔
    ∀ i,weight w (SortedFiniteWeights.indexing (weight w) i)<k →
      coefficients c hsk A w hA f (SortedFiniteWeights.indexing (weight w) i)=0
  exact (SortedFiniteWeights.indexing (weight w)).surjective.forall

def secondChart : RealCoordinates (group (q:=q) c hsk A w hA) (Fintype.card (Index w q)):=
  secondCoordinates (chart c hsk A w hA hw)
lemma secondChart_secondKind : SecondKind (secondChart (q:=q) c hsk A w hA hw):=
  secondCoordinates_secondKind _
include hmono in
lemma secondChart_adapted (k : ℕ) (f : group (q:=q) c hsk A w hA) :
    f∈(filtration c hsk A w hA).level k ↔ ∀ i,orderedWeight (q:=q) w i<k →
      (secondChart c hsk A w hA hw).coord f i=0 := by
  obtain ⟨r,hr,he⟩:=exists_weight_cutoff (orderedWeight (q:=q) w) (orderedWeight_monotone w) k
  have hb : ∀ f : group (q:=q) c hsk A w hA,f∈(filtration c hsk A w hA).level k ↔
      ∀ i : Fin (Fintype.card (Index w q)),i.val<r → (chart c hsk A w hA hw).coord f i=0 := by
    intro f
    simpa only [he] using chart_adapted c hsk A w hA hw hmono k f
  simpa only [← he,secondChart] using secondCoordinates_adapted
    (chart c hsk A w hA hw) ((filtration c hsk A w hA).level k) r hb f

end RationalLattice.PolynomialArrays

end
end
end

end OAI
