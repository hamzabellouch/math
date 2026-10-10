import Mathlib.Probability.ProductMeasure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

def singleTagCylinder (F : Finset ι) (T A : ι → Set X) (i : ι) : Set (ι → X) :=
  Set.pi (F : Set ι) (fun q => if q = i then T q else A q)

theorem singleTagCylinder_measurable (F : Finset ι) (T A : ι → Set X)
    (hT : ∀ q ∈ F, MeasurableSet (T q)) (hA : ∀ q ∈ F, MeasurableSet (A q)) (i : ι) :
    MeasurableSet (singleTagCylinder F T A i) := by
  classical
  have he : singleTagCylinder F T A i = ⋂ q, ⋂ (_ : q ∈ F),
      (fun ω : ι → X => ω q) ⁻¹' (if q = i then T q else A q) := by
    ext ω
    simp [singleTagCylinder,Set.mem_pi]
  rw [he]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro hq
  by_cases h : q = i
  · simpa only [ite_eq_left h] using (hT q hq).preimage (measurable_pi_apply q)
  · simpa only [ite_eq_right h] using (hA q hq).preimage (measurable_pi_apply q)

/-- Independent finite coordinates with one distinguished tag. The other
coordinates are explicitly nontagged, so these cylinders are disjoint. -/
theorem finite_single_tag_lower (μ : ι → Measure X) [∀ q, IsProbabilityMeasure (μ q)]
    (F : Finset ι) (T A : ι → Set X)
    (hT : ∀ q ∈ F, MeasurableSet (T q)) (hA : ∀ q ∈ F, MeasurableSet (A q))
    (hdisj : ∀ q ∈ F, Disjoint (T q) (A q)) (t a : ℝ≥0∞)
    (hTm : ∀ q ∈ F, t ≤ μ q (T q)) (hAm : ∀ q ∈ F, a ≤ μ q (A q)) :
    (F.card : ℝ≥0∞)*t*a^(F.card-1) ≤
      (Measure.infinitePi μ) (⋃ i ∈ F, singleTagCylinder F T A i) := by
  classical
  have hd : Set.PairwiseDisjoint (F : Set ι) (singleTagCylinder F T A) := by
    intro i hi l hl hil
    apply Set.disjoint_left.mpr
    intro ω hωi hωl
    have ht : ω i ∈ T i := by simpa using (hωi i hi)
    have ha : ω i ∈ A i := by simpa only [ite_eq_right hil] using (hωl i hi)
    exact Set.disjoint_left.mp (hdisj i hi) ht ha
  have hsingle (i : ι) (hi : i ∈ F) : t*a^(F.card-1) ≤
      (Measure.infinitePi μ) (singleTagCylinder F T A i) := by
    have hmeas (q : ι) (hq : q ∈ F) : MeasurableSet (if q = i then T q else A q) := by
      split_ifs <;> first | exact hT q hq | exact hA q hq
    rw [singleTagCylinder,Measure.infinitePi_pi _ hmeas]
    have he : t*a^(F.card-1) = ∏ q ∈ F, if q = i then t else a := by
      rw [← Finset.mul_prod_erase F (fun q => if q = i then t else a) hi,ite_eq_left rfl]
      congr 1
      calc
        a^(F.card-1) = ∏ _q ∈ F.erase i, a := by simp [Finset.card_erase_of_mem hi]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [ite_eq_right (Finset.mem_erase.mp hq).1]
    rw [he]
    apply Finset.prod_le_prod
    intro q hq
    by_cases h : q = i
    · simpa only [ite_eq_left h] using hTm q hq
    · simpa only [ite_eq_right h] using hAm q hq
  rw [measure_biUnion_finset hd (fun i _ => singleTagCylinder_measurable F T A hT hA i)]
  have hh := Finset.sum_le_sum hsingle
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

end
end FiniteFactor

end OAI
