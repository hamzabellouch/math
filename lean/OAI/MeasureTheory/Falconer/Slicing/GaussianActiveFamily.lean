import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveCount

namespace OAI

/-! # Active counts for measurable original-label tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianActiveFamily_measurable (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (r : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Sphere d =>
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞)) := by
  classical
  have he (p : ((Fin h → Space d) × Space h) × Sphere d) :
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞) =
      ∑ i : ι, {q : ((Fin h → Space d) × Space h) × Sphere d |
        i ∈ J q.2 ∧ a i ∈ gaussianPointBand q.1.1 q.1.2 r}.indicator (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand p.1.1 p.1.2 r then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : ((Fin h → Space d) × Space h) × Sphere d |
    ∀ j, |inner ℝ (a i) (q.1.1 j)-q.1.2 j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

omit [Fintype ι] [DecidableEq ι] in
theorem gaussianActiveFamily_exceptional_bound
    (A : Fin h → Space d) (J : Sphere d → Finset ι) (a : ι → Space d)
    {r : ℝ} (hr : 0 ≤ r) {N T : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞) (w : Sphere d) :
    (volume : Measure (Space h)) {z | T < (gaussianActiveAnchorCount A (J w) a r z : ℝ≥0∞)} ≤
      N*ENNReal.ofReal ((2*r)^h)/T := by
  apply (gaussianActiveAnchorCount_exceptional A (J w) a hr hT hTfin).trans
  simp only [div_eq_mul_inv]
  exact mul_le_mul_left (mul_le_mul_left (hN w) _) _

theorem gaussianActiveFamily_slice_count_measurable
    (A : Fin h → Space d) (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (R : ℝ) :
    Measurable (fun p : Space h × Sphere d =>
      (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)) := by
  classical
  have he (p : Space h × Sphere d) :
      (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞) =
      ∑ i : ι, {q : Space h × Sphere d | i ∈ J q.2 ∧ a i ∈ gaussianPointBand A q.1 R}.indicator
        (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand A p.1 R then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : Space h × Sphere d |
    ∀ j, |inner ℝ (a i) (A j)-q.1 j| ≤ R}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianActiveFamily_slice_measurable
    (A : Fin h → Space d) (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (R : ℝ) (T : ℝ≥0∞) :
    MeasurableSet {p : Space h × Sphere d |
      T < (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)} :=
  measurableSet_lt measurable_const (gaussianActiveFamily_slice_count_measurable A J hJ a R)

end Falconer

end OAI
