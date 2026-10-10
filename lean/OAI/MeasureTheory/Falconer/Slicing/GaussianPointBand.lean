import OAI.MeasureTheory.Falconer.Slicing.GaussianBox
import OAI.MeasureTheory.Falconer.Slicing.GaussianVectorBand
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMean

namespace OAI

/-! # Point bands in the actual Gaussian row coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianRowCoordinates (A : Fin h → Space d) (x : Space d) : Space h :=
  WithLp.toLp 2 (fun i => inner ℝ x (A i))

noncomputable def gaussianPointBand (A : Fin h → Space d) (z : Space h) (r : ℝ) : Set (Space d) :=
  {x | ∀ i, |inner ℝ x (A i)-z i| ≤ r}

theorem gaussianPointBand_measurable (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    MeasurableSet (gaussianPointBand A z r) := by
  simp only [gaussianPointBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem gaussianPointBand_parameter_measure (A : Fin h → Space d) (x : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r} = ENNReal.ofReal ((2*r)^h) := by
  have he : {z : Space h | x ∈ gaussianPointBand A z r} =
      (fun z => z-gaussianRowCoordinates A x) ⁻¹' coordinateBox h r := by
    ext z
    simp only [gaussianPointBand,coordinateBox,gaussianRowCoordinates,mem_ofPred_eq,
      mem_preimage,PiLp.sub_apply,abs_sub_comm]
  rw [he]
  simpa only [sub_eq_add_neg] using
    (measure_preimage_add_right (volume : Measure (Space h)) (-gaussianRowCoordinates A x)
      (coordinateBox h r)).trans (coordinateBox_volume hr)

theorem gaussianPointBand_integrated_mass (μ : Measure (Space d)) [SFinite μ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, μ (gaussianPointBand A z r)) = ENNReal.ofReal ((2*r)^h)*μ univ := by
  let S : Set (Space h × Space d) := {p | p.2 ∈ gaussianPointBand A p.1 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : Space h × Space d | ∀ i, |inner ℝ p.2 (A i)-p.1 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  calc
    _ = ((volume : Measure (Space h)).prod μ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ x, (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r} ∂μ :=
      Measure.prod_apply_symm hS
    _ = ∫⁻ _ : Space d, ENNReal.ofReal ((2*r)^h) ∂μ := by
      apply lintegral_congr
      intro x
      exact gaussianPointBand_parameter_measure A x hr
    _ = _ := lintegral_const _

theorem gaussianPointBand_pair_difference (A : Fin h → Space d) (z : Space h) {r : ℝ}
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r := by
  intro i
  calc
    _ = |(inner ℝ x (A i)-z i)-(inner ℝ y (A i)-z i)| := by rw [inner_sub_left]; congr 1; ring
    _ ≤ |inner ℝ x (A i)-z i|+|inner ℝ y (A i)-z i| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (inner ℝ x (A i)-z i) (inner ℝ y (A i)-z i)
    _ ≤ 2*r := by linarith [hx i,hy i]

end Falconer

end OAI
