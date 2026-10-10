import Mathlib
import OAI.Probability.JammingConcavity.FamilyPositiveTotal

namespace OAI

/-! Cascade Path Coordinates. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

open Classical
namespace MicroscopicJamming

def cascadePathIndex : (k : ℕ) → CascadePath k → Fin k → CascadeMarkIndex k
  | 0, _, j => Fin.elim0 j
  | k+1, ℓ, j => Fin.cases (ℓ.1.1,ℓ.1.2,none)
      (fun j => (ℓ.1.1,ℓ.1.2,some (cascadePathIndex k ℓ.2 j))) j

lemma cascadePathIndex_depth (k : ℕ) (ℓ : CascadePath k) (j : Fin k) :
    cascadeMarkDepth k (cascadePathIndex k ℓ j) = j := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change cascadeMarkDepth k (cascadePathIndex k ℓ.2 i)+1 = i.val+1
      rw [ih]

lemma cascadePathIndex_injective (k : ℕ) (ℓ : CascadePath k) :
    Function.Injective (cascadePathIndex k ℓ) := by
  intro i j h
  apply Fin.ext
  simpa only [cascadePathIndex_depth] using congrArg (cascadeMarkDepth k) h

lemma familyPathMark_zip {E : Type} [AddCommMonoid E] (k : ℕ) (x : E)
    (ω : CascadeTree k) (y : CascadeMarkTree E k) (ℓ : CascadePath k) :
    familyPathMark k x (zipCascade k (ω,y)) ℓ =
      x+∑ j : Fin k, cascadeMarkCoordinates k y (cascadePathIndex k ℓ j) := by
  induction k generalizing x with
  | zero => simp [familyPathMark]
  | succ k ih =>
    change familyPathMark k (x+(y ℓ.1.1 ℓ.1.2).1)
      (zipCascade k (((ω ℓ.1.1).2 ℓ.1.2).2,(y ℓ.1.1 ℓ.1.2).2)) ℓ.2 = _
    rw [ih, Fin.sum_univ_succ]
    simp only [cascadePathIndex]
    exact add_assoc _ _ _

lemma familyPathMark_coordinates {E : Type} [AddCommMonoid E] (k : ℕ) (x : E)
    (ω : CascadeTree k) (y : CascadeMarkTree E k) (ℓ : CascadePath k) :
    familyPathMark k x (zipCascade k (ω,y)) ℓ =
      x+∑ i ∈ Finset.univ.image (cascadePathIndex k ℓ), cascadeMarkCoordinates k y i := by
  rw [familyPathMark_zip, Finset.sum_image]
  exact fun i _ j _ h => cascadePathIndex_injective k ℓ h
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma measurable_familyPathWeight {E : Type} [MeasurableSpace E]
    (ms : List ℝ) (ℓ : CascadePath ms.length) : Measurable (fun ω => familyPathWeight (E := E) ms ω ℓ) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    change Measurable (fun ω : PointCloud (E × FamilyCascadeTree E ms.length) =>
      if ℓ.1.2 < (ω ℓ.1.1).1 then
        ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m))*
          familyPathWeight ms ((ω ℓ.1.1).2 ℓ.1.2).2.2 ℓ.2 else 0)
    have hi := (ih ℓ.2).comp (by fun_prop : Measurable
      (fun ω : PointCloud (E × FamilyCascadeTree E ms.length) => ((ω ℓ.1.1).2 ℓ.1.2).2.2))
    have hc : MeasurableSet {ω : PointCloud (E × FamilyCascadeTree E ms.length) |
        ℓ.1.2 < (ω ℓ.1.1).1} := measurableSet_lt measurable_const (by fun_prop)
    have hw : Measurable (fun ω : PointCloud (E × FamilyCascadeTree E ms.length) =>
        ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m))) := by fun_prop
    exact Measurable.ite hc (hw.mul hi) measurable_const

lemma measurable_familyPathMark {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (k : ℕ) (ℓ : CascadePath k) :
    Measurable (fun z : E × FamilyCascadeTree E k => familyPathMark k z.1 z.2 ℓ) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    exact (ih ℓ.2).comp (show Measurable
      (fun z : E × PointCloud (E × FamilyCascadeTree E k) =>
        (z.1+((z.2 ℓ.1.1).2 ℓ.1.2).2.1,((z.2 ℓ.1.1).2 ℓ.1.2).2.2)) from by fun_prop)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
variable {E : Type} [MeasurableSpace E] [AddMonoid E] [MeasurableAdd₂ E]

def normalizedFamilyPathWeight (ms : List ℝ) (ω : FamilyCascadeTree E ms.length)
    (ℓ : CascadePath ms.length) : ℝ :=
  (familyPathWeight ms ω ℓ/familyUnmarkedTotal ms ω).toReal

lemma measurable_normalizedFamilyPathWeight (ms : List ℝ) (ℓ : CascadePath ms.length) :
    Measurable (fun ω : FamilyCascadeTree E ms.length => normalizedFamilyPathWeight ms ω ℓ) :=
  ((measurable_familyPathWeight ms ℓ).div (measurable_familyUnmarkedTotal ms)).ennreal_toReal

omit [MeasurableAdd₂ E] in
lemma normalized_familyPath_series [MeasurableAdd₂ E] (ms : List ℝ) (f : E → ℝ≥0∞) (x : E)
    (ω : FamilyCascadeTree E ms.length)
    (hu : 0 < familyUnmarkedTotal ms ω) (hf : familyPositiveTotal ms f x ω ≠ ∞) :
    Summable (fun ℓ => normalizedFamilyPathWeight ms ω ℓ*(f (familyPathMark ms.length x ω ℓ)).toReal) ∧
    (∑' ℓ, normalizedFamilyPathWeight ms ω ℓ*(f (familyPathMark ms.length x ω ℓ)).toReal) =
      (familyPositiveTotal ms f x ω/familyUnmarkedTotal ms ω).toReal := by
  let a (ℓ : CascadePath ms.length) : ℝ≥0∞ :=
    familyPathWeight ms ω ℓ/familyUnmarkedTotal ms ω*f (familyPathMark ms.length x ω ℓ)
  have he : (∑' ℓ, a ℓ) = familyPositiveTotal ms f x ω/familyUnmarkedTotal ms ω := by
    simp only [a, div_eq_mul_inv]
    simp_rw [mul_right_comm (familyPathWeight ms ω _) _ (f _)]
    rw [ENNReal.tsum_mul_right, tsum_familyPathWeight_terminal]
  have ha : (∑' ℓ, a ℓ) ≠ ∞ := by rw [he]; exact ENNReal.div_ne_top hf hu.ne'
  have hai : ∀ ℓ, a ℓ ≠ ∞ := fun ℓ => ne_top_of_le_ne_top ha (ENNReal.le_tsum ℓ)
  have hreal : (fun ℓ => (a ℓ).toReal) =
      (fun ℓ => normalizedFamilyPathWeight ms ω ℓ*(f (familyPathMark ms.length x ω ℓ)).toReal) := by
    funext ℓ
    simp only [a, normalizedFamilyPathWeight, ENNReal.toReal_mul]
  refine ⟨hreal ▸ ENNReal.summable_toReal ha, ?_⟩
  rw [← hreal, ← ENNReal.tsum_toReal_eq hai, he]

lemma normalized_familyPath_weights (ms : List ℝ) (ω : FamilyCascadeTree E ms.length)
    (hu : 0 < familyUnmarkedTotal ms ω ∧ familyUnmarkedTotal ms ω < ∞) :
    Summable (normalizedFamilyPathWeight ms ω) ∧ (∑' ℓ, normalizedFamilyPathWeight ms ω ℓ) = 1 := by
  have hf : familyPositiveTotal ms (fun _ : E => 1) 0 ω ≠ ∞ := by
    simpa only [familyPositiveTotal_const, one_mul] using hu.2.ne
  have H := normalized_familyPath_series ms (fun _ : E => 1) 0 ω hu.1 hf
  simpa only [ENNReal.toReal_one, mul_one, familyPositiveTotal_const, one_mul,
    ENNReal.div_self hu.1.ne' hu.2.ne] using H
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma forgetFamilyMarks_zip {E : Type} (k : ℕ) (ω : CascadeTree k) (y : CascadeMarkTree E k) :
    forgetFamilyMarks k (zipCascade k (ω,y)) = ω := by
  induction k with
  | zero => cases ω; rfl
  | succ k ih =>
    funext n
    apply Prod.ext
    · rfl
    · funext i
      apply Prod.ext
      · rfl
      · exact ih _ _

def normalizedCascadePathWeight (ms : List ℝ) (ω : CascadeTree ms.length)
    (ℓ : CascadePath ms.length) : ℝ := (cascadePathWeight ms ω ℓ/cascadeTotal ms ω).toReal

lemma normalizedFamilyPathWeight_zip {E : Type} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableAdd₂ E] (ms : List ℝ) (ω : CascadeTree ms.length)
    (y : CascadeMarkTree E ms.length) (ℓ : CascadePath ms.length) :
    normalizedFamilyPathWeight ms (zipCascade ms.length (ω,y)) ℓ =
      normalizedCascadePathWeight ms ω ℓ := by
  rw [normalizedFamilyPathWeight, familyPathWeight_zip, familyUnmarkedTotal, forgetFamilyMarks_zip]
  rfl

def rootMarkCoordinates {E : Type} (k : ℕ) (p : E × CascadeMarkTree E k) :
    Option (CascadeMarkIndex k) → E := fun i => i.elim p.1 (cascadeMarkCoordinates k p.2)

lemma measurable_rootMarkCoordinates {E : Type} [MeasurableSpace E] (k : ℕ) :
    Measurable (rootMarkCoordinates (E := E) k) := by
  apply Measurable.of_eval
  intro i
  cases i with
  | none => exact measurable_fst
  | some i => exact (measurable_pi_apply i).comp ((measurable_cascadeMarkCoordinates k).comp measurable_snd)

lemma rootMarkCoordinates_law {E : Type} [MeasurableSpace E] (k : ℕ)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : ℕ → Measure E)
    [∀ j, IsProbabilityMeasure (ν j)] :
    (μ.prod (cascadeMarkLaw k ν)).map (rootMarkCoordinates k) =
      Measure.infinitePi (fun i : Option (CascadeMarkIndex k) => i.elim μ (fun j => ν (cascadeMarkDepth k j))) := by
  rw [show rootMarkCoordinates (E := E) k = (fun z i => i.elim z.1 z.2) ∘
      Prod.map id (cascadeMarkCoordinates k) from rfl,
    ← Measure.map_map (by
      apply Measurable.of_eval
      intro i
      cases i <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop) (measurable_id.prodMap (measurable_cascadeMarkCoordinates k)),
    ← Measure.map_prod_map _ _ measurable_id (measurable_cascadeMarkCoordinates k), Measure.map_id,
    cascadeMarkCoordinates_law, infinitePi_option]

def rootPathField {E : Type} [AddCommMonoid E] (k : ℕ)
    (g : Option (CascadeMarkIndex k) → E) (ℓ : CascadePath k) : E :=
  g none+∑ j : Fin k, g (some (cascadePathIndex k ℓ j))

lemma rootPathField_eq {E : Type} [AddCommMonoid E] (k : ℕ) (x : E)
    (ω : CascadeTree k) (y : CascadeMarkTree E k) (ℓ : CascadePath k) :
    familyPathMark k x (zipCascade k (ω,y)) ℓ = rootPathField k (rootMarkCoordinates k (x,y)) ℓ := by
  rw [familyPathMark_zip]
  rfl

def zipRootCascade {E : Type} (k : ℕ) (p : CascadeTree k × (E × CascadeMarkTree E k)) :
    E × FamilyCascadeTree E k := (p.2.1, zipCascade k (p.1,p.2.2))

lemma measurable_zipRootCascade {E : Type} [MeasurableSpace E] (k : ℕ) :
    Measurable (zipRootCascade (E := E) k) :=
  (measurable_fst.comp measurable_snd).prodMk ((measurable_zipCascade k).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

lemma zipRootCascade_law {E : Type} [MeasurableSpace E] (ms : List ℝ)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : ℕ → Measure E)
    [∀ j, IsProbabilityMeasure (ν j)] :
    ((cascadeLaw ms).prod (μ.prod (cascadeMarkLaw ms.length ν))).map (zipRootCascade ms.length) =
      μ.prod (familyCascadeLaw ms.length ν) := by
  rw [show zipRootCascade (E := E) ms.length = (Prod.map id (zipCascade ms.length)) ∘
    (fun z => (z.2.1,(z.1,z.2.2))) from rfl,
    ← Measure.map_map (measurable_id.prodMap (measurable_zipCascade ms.length)) (by fun_prop),
    prod_rotate_map, ← Measure.map_prod_map _ _ measurable_id (measurable_zipCascade ms.length),
    Measure.map_id, cascade_independent_marks]

lemma integral_cascade_coordinates {E : Type} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableAdd₂ E] (ms : List ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (ν : ℕ → Measure E) [∀ j, IsProbabilityMeasure (ν j)]
    {f : E × FamilyCascadeTree E ms.length → ℝ} (hf : Measurable f)
    {g : CascadeTree ms.length × (Option (CascadeMarkIndex ms.length) → E) → ℝ} (hg : Measurable g)
    (he : ∀ ω x y, f (x,zipCascade ms.length (ω,y)) = g (ω,rootMarkCoordinates ms.length (x,y))) :
    (∫ z, f z ∂μ.prod (familyCascadeLaw ms.length ν)) =
      ∫ z, g z ∂(cascadeLaw ms).prod (Measure.infinitePi
        (fun i : Option (CascadeMarkIndex ms.length) => i.elim μ (fun j => ν (cascadeMarkDepth ms.length j)))) := by
  rw [← zipRootCascade_law ms μ ν,
    integral_map (measurable_zipRootCascade ms.length).aemeasurable hf.aestronglyMeasurable]
  have hmap := rootMarkCoordinates_law ms.length μ ν
  rw [← hmap, ← (Measure.map_id (μ := cascadeLaw ms)),
    Measure.map_prod_map _ _ measurable_id (measurable_rootMarkCoordinates ms.length),
    integral_map (measurable_id.prodMap (measurable_rootMarkCoordinates ms.length)).aemeasurable hg.aestronglyMeasurable]
  rw [Measure.map_id]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => he z.1 z.2.1 z.2.2
end MicroscopicJamming

 
 
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma enn_pair_sum_mul {I : Type*} (a : I → ℝ≥0∞) :
    (∑' i, a i)*(∑' i, a i) = ∑' p : I × I, a p.1*a p.2 := by
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

lemma enn_pair_same_block {I L : Type*} (a : I → L → ℝ≥0∞) (R : L → L → Prop) :
    (∑' p : (I × L) × (I × L),
      if p.1.1=p.2.1 ∧ R p.1.2 p.2.2 then a p.1.1 p.1.2*a p.2.1 p.2.2 else 0) =
    ∑' i, ∑' p : L × L, if R p.1 p.2 then a i p.1*a i p.2 else 0 := by
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_comm]
  have H (j : I) : (∑' l, ∑' r, if i=j ∧ R l r then a i l*a j r else 0) =
      if i=j then ∑' l, ∑' r, if R l r then a i l*a j r else 0 else 0 := by
    by_cases h : i=j <;> simp [h]
  simp_rw [H]
  simpa only [eq_comm] using (tsum_ite_eq i (fun j => ∑' l, ∑' r, if R l r then a i l*a j r else 0))

lemma enn_pair_scale {L : Type*} (a : L → ℝ≥0∞) (c : ℝ≥0∞) (R : L → L → Prop) :
    (∑' p : L × L, if R p.1 p.2 then (c*a p.1)*(c*a p.2) else 0) =
      c^2*(∑' p : L × L, if R p.1 p.2 then a p.1*a p.2 else 0) := by
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro p
  split_ifs
  · ring
  · simp only [mul_zero]
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

def pathAgree : (k : ℕ) → ℕ → CascadePath k → CascadePath k → Prop
  | 0, _, _, _ => True
  | _+1, 0, _, _ => True
  | k+1, j+1, a, b => a.1=b.1 ∧ pathAgree k j a.2 b.2

def familyLeafMass {E : Type} [Add E] (ms : List ℝ) (u : E → ℝ) (x : E)
    (ω : FamilyCascadeTree E ms.length) (ℓ : CascadePath ms.length) : ℝ≥0∞ :=
  familyPathWeight ms ω ℓ*ENNReal.ofReal (Real.exp (u (familyPathMark ms.length x ω ℓ)))

def familyPairSum {E : Type} [Add E] (ms : List ℝ) (j : ℕ) (u : E → ℝ) (x : E)
    (ω : FamilyCascadeTree E ms.length) : ℝ≥0∞ :=
  ∑' p : CascadePath ms.length × CascadePath ms.length,
    if pathAgree ms.length j p.1 p.2 then familyLeafMass ms u x ω p.1*familyLeafMass ms u x ω p.2 else 0

lemma tsum_familyLeafMass {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length) :
    (∑' ℓ, familyLeafMass ms u x ω ℓ) = familyLeafTotal ms u x ω := by
  exact (tsum_familyPathWeight_terminal ms (fun y => ENNReal.ofReal (Real.exp (u y))) x ω).trans
    (familyPositiveTotal_exp ms u x ω)

lemma pathAgree_zero (k : ℕ) (a b : CascadePath k) : pathAgree k 0 a b := by
  cases k <;> trivial

lemma familyPairSum_zero {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length) :
    familyPairSum ms 0 u x ω = (familyLeafTotal ms u x ω)^2 := by
  simp only [familyPairSum, pathAgree_zero, ite_true]
  rw [← enn_pair_sum_mul, tsum_familyLeafMass, pow_two]

lemma familyLeafMass_cons {E : Type} [Add E] (m : ℝ) (ms : List ℝ)
    (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E (m::ms).length)
    (i : ℕ × ℕ) (ℓ : CascadePath ms.length) :
    familyLeafMass (m::ms) u x ω (i,ℓ) =
      (if i.2 < (ω i.1).1 then ENNReal.ofReal (((i.1:ℝ)+((ω i.1).2 i.2).1)^(-1/m)) else 0)*
        familyLeafMass ms u (x+((ω i.1).2 i.2).2.1) ((ω i.1).2 i.2).2.2 ℓ := by
  by_cases hi : i.2 < (ω i.1).1
  · simp only [familyLeafMass, List.length_cons, familyPathWeight, familyPathMark, hi, ite_true, mul_assoc]
  · simp only [familyLeafMass, familyPathWeight, hi, ite_false, zero_mul]

lemma familyPairSum_cons {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (m : ℝ) (ms : List ℝ) (j : ℕ) (u : E → ℝ) (x : E)
    (ω : FamilyCascadeTree E (m::ms).length) :
    familyPairSum (m::ms) (j+1) u x ω =
      pointCloudFunctional (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
        (ENNReal.ofReal (z.1^(-1/m)))^2*familyPairSum ms j u (x+z.2.1) z.2.2) ω := by
  simp only [familyPairSum, List.length_cons, pathAgree]
  change (∑' p : ((ℕ × ℕ) × CascadePath ms.length) × ((ℕ × ℕ) × CascadePath ms.length),
    if p.1.1=p.2.1 ∧ pathAgree ms.length j p.1.2 p.2.2 then
      familyLeafMass (m::ms) u x ω p.1*familyLeafMass (m::ms) u x ω p.2 else 0) = _
  refine Eq.trans ?_ ((enn_pair_same_block (fun i ℓ => familyLeafMass (m::ms) u x ω (i,ℓ))
    (pathAgree ms.length j)).trans ?_)
  · apply tsum_congr
    rintro ⟨⟨i,ℓ⟩,⟨j,r⟩⟩
    split_ifs <;> rfl
  · simp_rw [familyLeafMass_cons, enn_pair_scale]
    rw [ENNReal.tsum_prod']
    simp only [pointCloudFunctional, poissonBinSum]
    apply tsum_congr
    intro n
    rw [tsum_eq_sum (s := Finset.range (ω n).1) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [not_lt.mpr hi])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range.mp hi, ite_true]
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma cascadePathIndex_eq_iff (k : ℕ) (a b : CascadePath k) (j : Fin k) :
    cascadePathIndex k a j = cascadePathIndex k b j ↔ pathAgree k (j.val+1) a b := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · change (a.1.1,a.1.2,none) = (b.1.1,b.1.2,(none : Option (CascadeMarkIndex k))) ↔
        a.1=b.1 ∧ pathAgree k 0 a.2 b.2
      simp [Prod.ext_iff, pathAgree_zero]
    · change (a.1.1,a.1.2,some (cascadePathIndex k a.2 i)) =
        (b.1.1,b.1.2,some (cascadePathIndex k b.2 i)) ↔
        a.1=b.1 ∧ pathAgree k (i.val+1) a.2 b.2
      simp only [Option.some.injEq, ih, Prod.ext_iff]
      tauto

lemma cascadePathIndex_depth_eq {k : ℕ} {a b : CascadePath k} {i j : Fin k}
    (h : cascadePathIndex k a i = cascadePathIndex k b j) : i = j := by
  apply Fin.ext
  simpa only [cascadePathIndex_depth] using congrArg (cascadeMarkDepth k) h

def rootPathIndex (k : ℕ) (ℓ : CascadePath k) : Fin (k+1) → Option (CascadeMarkIndex k) :=
  Fin.cases none (fun j => some (cascadePathIndex k ℓ j))

lemma rootPathIndex_injective (k : ℕ) (ℓ : CascadePath k) :
    Function.Injective (rootPathIndex k ℓ) := by
  intro i j h
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => simp [rootPathIndex] at h
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [rootPathIndex] at h
    | succ j =>
      apply congrArg Fin.succ
      exact cascadePathIndex_injective k ℓ (Option.some.inj h)

lemma rootPathIndex_depth_eq {k : ℕ} {a b : CascadePath k} {i j : Fin (k+1)}
    (h : rootPathIndex k a i = rootPathIndex k b j) : i = j := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => simp [rootPathIndex] at h
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [rootPathIndex] at h
    | succ j => exact congrArg Fin.succ (cascadePathIndex_depth_eq (Option.some.inj h))

lemma rootPathIndex_eq_iff (k : ℕ) (a b : CascadePath k) (j : Fin (k+1)) :
    rootPathIndex k a j = rootPathIndex k b j ↔ pathAgree k j.val a b := by
  cases j using Fin.cases with
  | zero => simp [rootPathIndex, pathAgree_zero]
  | succ j => simpa only [rootPathIndex, Fin.cases_succ, Option.some.injEq, Fin.val_succ]
      using cascadePathIndex_eq_iff k a b j

lemma finite_incidence_covariance {A J : Type*} [Fintype A] [Fintype J]
    (e f : J → A) (_hf : Function.Injective f) (v : J → ℝ)
    (hdepth : ∀ i j, e i = f j → i = j) :
    (∑ a : A, (∑ i : J, if e i=a then v i else 0)*(∑ j : J, if f j=a then v j else 0)) =
      ∑ i : J, if e i=f i then (v i)^2 else 0 := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  have he (j : J) : (∑ a : A, (if e i=a then v i else 0)*(if f j=a then v j else 0)) =
      if e i=f j then v i*v j else 0 := by
    rw [Finset.sum_eq_single (e i)]
    · simp only [ite_true]
      by_cases hh : e i=f j
      · simp [hh]
      · simp [hh, Ne.symm hh]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  simp_rw [he]
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j _ hj
    simp only [ite_eq_right (fun hh => hj (hdepth i j hh).symm)]
  · simp
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

open Classical
namespace MicroscopicJamming

def cascadeCoordinateSet (k : ℕ) (S : Finset (CascadePath k)) : Finset (Option (CascadeMarkIndex k)) :=
  S.biUnion (fun ℓ => Finset.univ.image (rootPathIndex k ℓ))

lemma rootPathIndex_mem (k : ℕ) (S : Finset (CascadePath k)) (ℓ : S) (j : Fin (k+1)) :
    rootPathIndex k ℓ.val j ∈ cascadeCoordinateSet k S := by
  apply Finset.mem_biUnion.mpr
  exact ⟨ℓ.val,ℓ.property,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩

def finiteRootPathIndex (k : ℕ) (S : Finset (CascadePath k)) (ℓ : S) (j : Fin (k+1)) :
    cascadeCoordinateSet k S := ⟨rootPathIndex k ℓ.val j,rootPathIndex_mem k S ℓ j⟩

def finiteRootPathField {E : Type} [AddCommMonoid E] (k : ℕ) (S : Finset (CascadePath k))
    (z : cascadeCoordinateSet k S → E) (ℓ : S) : E := ∑ j, z (finiteRootPathIndex k S ℓ j)

lemma rootPathField_finite {E : Type} [AddCommMonoid E] (k : ℕ) (S : Finset (CascadePath k))
    (z : Option (CascadeMarkIndex k) → E) (ℓ : S) :
    rootPathField k z ℓ.val = finiteRootPathField k S ((cascadeCoordinateSet k S).restrict z) ℓ := by
  rw [finiteRootPathField, Fin.sum_univ_succ]
  rfl

lemma measurable_finiteRootPathField {E : Type} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableAdd₂ E] (k : ℕ) (S : Finset (CascadePath k)) :
    Measurable (fun z ℓ => finiteRootPathField (E := E) k S z ℓ) := by
  unfold finiteRootPathField
  fun_prop

lemma integral_cascade_finite_coordinates {E : Type} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableAdd₂ E] (ms : List ℝ) (S : Finset (CascadePath ms.length))
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : ℕ → Measure E)
    [∀ j, IsProbabilityMeasure (ν j)]
    {f : E × FamilyCascadeTree E ms.length → ℝ} (hf : Measurable f)
    {g : CascadeTree ms.length × (cascadeCoordinateSet ms.length S → E) → ℝ} (hg : Measurable g)
    (he : ∀ ω x y, f (x,zipCascade ms.length (ω,y)) =
      g (ω,(cascadeCoordinateSet ms.length S).restrict (rootMarkCoordinates ms.length (x,y)))) :
    (∫ z, f z ∂μ.prod (familyCascadeLaw ms.length ν)) =
      ∫ z, g z ∂(cascadeLaw ms).prod (Measure.pi
        (fun i : cascadeCoordinateSet ms.length S => i.val.elim μ (fun j => ν (cascadeMarkDepth ms.length j)))) := by
  let C := cascadeCoordinateSet ms.length S
  let η : Option (CascadeMarkIndex ms.length) → Measure E :=
    fun i => i.elim μ (fun j => ν (cascadeMarkDepth ms.length j))
  have hη (i) : IsProbabilityMeasure (η i) := by cases i <;> dsimp [η] <;> infer_instance
  let := hη
  have hm : Measurable (Prod.map (id : CascadeTree ms.length → CascadeTree ms.length)
    (C.restrict : (Option (CascadeMarkIndex ms.length) → E) → (C → E))) := by
    exact measurable_id.prodMap (Measurable.of_eval fun i => measurable_pi_apply i.val)
  rw [integral_cascade_coordinates ms μ ν hf (hg.comp hm) he]
  have hr : Measurable (C.restrict : (Option (CascadeMarkIndex ms.length) → E) → (C → E)) :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  change (∫ z, g (Prod.map id C.restrict z) ∂(cascadeLaw ms).prod (Measure.infinitePi η)) = _
  rw [← integral_map hm.aemeasurable hg.aestronglyMeasurable,
    ← Measure.map_prod_map _ _ measurable_id hr, Measure.map_id, Measure.infinitePi_map_restrict]
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

open Classical
namespace MicroscopicJamming

lemma weighted_incidence_covariance {A J : Type*} [Fintype A] [Fintype J]
    (e f : J → A) (q : A → ℝ) (hdepth : ∀ i j, e i=f j → i=j) :
    (∑ a : A, q a*(∑ i : J, if e i=a then (1:ℝ) else 0)*(∑ j : J, if f j=a then (1:ℝ) else 0)) =
      ∑ i : J, if e i=f i then q (e i) else 0 := by
  calc
    _ = ∑ i : J, ∑ a : A, (q a*(if e i=a then (1:ℝ) else 0))*
        (∑ j : J, if f j=a then (1:ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ i : J, q (e i)*(∑ j : J, if f j=e i then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (e i)]
      · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · by_cases hh : e i=f i <;> simp [hh, Ne.symm]
      · intro j _ hj
        exact ite_eq_right (fun hh => hj (hdepth i j hh.symm).symm)
      · simp

def rootCoordinateVariance (k : ℕ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0)
    (a : Option (CascadeMarkIndex k)) : ℝ≥0 :=
  a.elim p₀ (fun j => d (cascadeMarkDepth k j))

def pathCovarianceDifference (k : ℕ) (d d' : ℕ → ℝ≥0) (p₀ p₀' : ℝ≥0)
    (a b : CascadePath k) : ℝ :=
  (p₀:ℝ)-(p₀':ℝ)+∑ j : Fin k,
    if pathAgree k (j.val+1) a b then (d j:ℝ)-(d' j:ℝ) else 0

lemma rootVariance_path (k : ℕ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0)
    (ℓ : CascadePath k) (j : Fin (k+1)) :
    rootCoordinateVariance k d p₀ (rootPathIndex k ℓ j) = Fin.cases p₀ (fun i => d i) j := by
  cases j using Fin.cases with
  | zero => rfl
  | succ j => change d (cascadeMarkDepth k (cascadePathIndex k ℓ j)) = d j
              rw [cascadePathIndex_depth]

lemma finiteRoot_incidence_covariance (k : ℕ) (S : Finset (CascadePath k))
    (d d' : ℕ → ℝ≥0) (p₀ p₀' : ℝ≥0) (ℓ r : S) :
    (∑ a : cascadeCoordinateSet k S,
      ((rootCoordinateVariance k d p₀ a:ℝ)-(rootCoordinateVariance k d' p₀' a:ℝ))*
      (∑ j : Fin (k+1), if finiteRootPathIndex k S ℓ j=a then (1:ℝ) else 0)*
      (∑ j : Fin (k+1), if finiteRootPathIndex k S r j=a then (1:ℝ) else 0)) =
      pathCovarianceDifference k d d' p₀ p₀' ℓ.val r.val := by
  have H := weighted_incidence_covariance (finiteRootPathIndex k S ℓ)
    (finiteRootPathIndex k S r)
    (fun a => (rootCoordinateVariance k d p₀ a:ℝ)-(rootCoordinateVariance k d' p₀' a:ℝ))
    (fun i j hij => rootPathIndex_depth_eq (congrArg Subtype.val hij))
  calc
    _ = ∑ i : Fin (k+1), if finiteRootPathIndex k S ℓ i=finiteRootPathIndex k S r i then
      (rootCoordinateVariance k d p₀ (finiteRootPathIndex k S ℓ i):ℝ)-
      (rootCoordinateVariance k d' p₀' (finiteRootPathIndex k S ℓ i):ℝ) else 0 := by
      convert H using 1 <;> congr 4 <;> funext a <;> congr 3 <;> funext j <;> split_ifs <;> rfl
    _ = _ := by
      rw [Fin.sum_univ_succ]
      simp only [finiteRootPathIndex, Subtype.mk.injEq, rootPathIndex_eq_iff,
        rootVariance_path, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ,
        pathAgree_zero, ite_true, pathCovarianceDifference]

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

def rowReplicaCovariance (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0)
    (xs : Fin r → CascadePath k) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (p₀:ℝ) + ∑ a : Fin k, if pathAgree k (a.val+1) (xs i) (xs j) then (d a:ℝ) else 0

def rowReplicaGaussianField (k r : ℕ) (xs : Fin r → CascadePath k)
    (z : Option (CascadeMarkIndex k) → ℝ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun i => rootPathField k z (xs i))

def RowReplicaGaussianStatement : Prop :=
  ∀ (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (xs : Fin r → CascadePath k),
    (rowReplicaCovariance k r d p₀ xs).PosSemidef ∧
    (Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance k d p₀ a))).map
      (rowReplicaGaussianField k r xs) = multivariateGaussian 0 (rowReplicaCovariance k r d p₀ xs)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

def rowReplicaResidualCovariance (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (xs : Fin r → CascadePath k) : Matrix (Fin r) (Fin r) ℝ :=
  rowReplicaCovariance k r d p₀ xs + Matrix.diagonal (fun _ => (Δ:ℝ))

def rowReplicaResidualField (k r : ℕ) (xs : Fin r → CascadePath k)
    (w : (Option (CascadeMarkIndex k) → ℝ) × (Fin r → ℝ)) : EuclideanSpace ℝ (Fin r) :=
  rowReplicaGaussianField k r xs w.1 + WithLp.toLp 2 w.2

def RowReplicaResidualStatement : Prop :=
  ∀ (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) (xs : Fin r → CascadePath k),
    (rowReplicaResidualCovariance k r d p₀ Δ xs).PosSemidef ∧
    ((Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance k d p₀ a))).prod
      (Measure.pi (fun _ : Fin r => gaussianReal 0 Δ))).map
      (rowReplicaResidualField k r xs) =
      multivariateGaussian 0 (rowReplicaResidualCovariance k r d p₀ Δ xs)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder

namespace MicroscopicJamming

def gaussianAdjunctionMap {A : Type*} (m : ℕ)
    (C : A → Matrix (Fin m) (Fin m) ℝ)
    (w : A × EuclideanSpace ℝ (Fin m)) : A × EuclideanSpace ℝ (Fin m) :=
  (w.1, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C w.1)) w.2)

def gaussianAdjunctionMeasure {A : Type*} [MeasurableSpace A] (m : ℕ)
    (C : A → Matrix (Fin m) (Fin m) ℝ) (μ : Measure A) :
    Measure (A × EuclideanSpace ℝ (Fin m)) :=
  (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin m)))).map (gaussianAdjunctionMap m C)

def GaussianAdjunctionStatement : Prop :=
  ∀ (A : Type) (tA : TopologicalSpace A) (mA : MeasurableSpace A),
    ∀ (_hB : @BorelSpace A tA mA) (_hSC : SecondCountableTopology A)
      (_hPM : TopologicalSpace.PseudoMetrizableSpace A),
  ∀ (m : ℕ) (C : A → Matrix (Fin m) (Fin m) ℝ),
    Continuous C → (∀ x, (C x).PosSemidef) →
    (∃ K : ℝ, ∀ x i j, |C x i j| ≤ K) →
  ∀ (μ : ℕ → ProbabilityMeasure A) (μ₀ : ProbabilityMeasure A),
    Tendsto μ atTop (𝓝 μ₀) →
    ∃ (ρ : ℕ → ProbabilityMeasure (A × EuclideanSpace ℝ (Fin m)))
      (ρ₀ : ProbabilityMeasure (A × EuclideanSpace ℝ (Fin m))),
      (∀ n, (ρ n : Measure _) = gaussianAdjunctionMeasure m C (μ n)) ∧
      (ρ₀ : Measure _) = gaussianAdjunctionMeasure m C μ₀ ∧
      Tendsto ρ atTop (𝓝 ρ₀)
end MicroscopicJamming

end

end OAI
