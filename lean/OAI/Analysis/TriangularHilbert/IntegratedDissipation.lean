import OAI.Analysis.TriangularHilbert.PlaneInterval

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma totalPlaneTime_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (totalPlaneTime A h u d α) volume a b := by
  have hi : IntervalIntegrable (∑ v : Three, ∑ w : Three,
      fun s => α w * planeIntegral (fun p => heatVariance A h u p (fun z => α z*s) v w) d) volume a b := by
    apply IntervalIntegrable.sum Finset.univ
    intro v _
    apply IntervalIntegrable.sum Finset.univ
    intro w _
    exact ((planeTime_intervalIntegrable A hh u d α hα ha hab).1 v w).const_mul (α w)
  convert hi using 1
  ext s
  simp [totalPlaneTime]

lemma integral_totalPlaneTime (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, totalPlaneTime A h u d α s) =
      totalPlaneEnergy A h u d (fun w => α w*b) - totalPlaneEnergy A h u d (fun w => α w*a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (totalPlaneTime_intervalIntegrable A hh u d α hα ha hab)
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  exact totalPlaneEnergy_hasDerivAt A hh u d α hα (ha.trans_le hs.1)

lemma integrated_strict_dissipation (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (i : Three)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    strictConstant * (∫ s in a..b, ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) ≤
      totalPlaneEnergy A h u d (fun w => strictRate i w*a) - totalPlaneEnergy A h u d (fun w => strictRate i w*b) := by
  have hc : IntervalIntegrable (fun s => ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) volume a b :=
    by
      have hi : IntervalIntegrable (∑ w : Three, fun s => planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) volume a b := IntervalIntegrable.sum Finset.univ (fun w _ => (planeTime_intervalIntegrable A hh u d (strictRate i) (strictRate_pos i) ha hab).2 w w)
      convert hi using 1
      ext s
      simp
  have ht := totalPlaneTime_intervalIntegrable A hh u d (strictRate i) (strictRate_pos i) ha hab
  have hi := intervalIntegral.integral_mono_on hab (hc.const_mul strictConstant) ht.neg
    (fun s hs => plane_strict_dissipation A hh u d i (ha.trans_le hs.1))
  rw [intervalIntegral.integral_const_mul] at hi
  change strictConstant * (∫ s in a..b, ∑ w, planeIntegral (fun p => heatCost A h u p (fun z => strictRate i z*s) w w) d) ≤ ∫ s in a..b, -(totalPlaneTime A h u d (strictRate i) s) at hi
  rw [intervalIntegral.integral_neg,integral_totalPlaneTime A hh u d (strictRate i) (strictRate_pos i) ha hab] at hi
  linarith

end
end TriangularHilbert.Heat
end

end OAI
