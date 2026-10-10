import OAI.Probability.FreeIsing.Gaussian.BinaryRegression
import OAI.Probability.FreeIsing.Trees.RootCorrelation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := by trivial

theorem BinaryRegression.condExp_eq_cov_mul_spinSign
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ s : IsingSpin, mu {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f : Ω → ℝ} (hf : Integrable f mu) (hzero : ∫ ω, f ω ∂mu = 0) :
    ∀ ω, mu[f | isingSpinMeasurable.comap S] ω =
      (∫ z, f z * spinSign (S z) ∂mu) * spinSign (S ω) := by
  obtain ⟨a, ha⟩ := BinaryRegression.exists_condExp_mul_spinSign hS hfair hzero
  have hsign : Measurable spinSign := measurable_of_finite _
  have hSm : Measurable[isingSpinMeasurable.comap S] S :=
    measurable_iff_comap_le.mpr le_rfl
  have hprod : Integrable (fun ω => f ω * spinSign (S ω)) mu := by
    apply hf.mul_bdd (c := 1) (hsign.comp hS).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by cases h : S ω <;> norm_num [h, spinSign])
  have hpull := condExp_mul_of_stronglyMeasurable_right
    (μ := mu) (m := isingSpinMeasurable.comap S)
    (f := f) (g := fun ω => spinSign (S ω))
    (hsign.comp hSm).stronglyMeasurable hprod hf
  have hint := integral_congr_ae hpull
  rw [integral_condExp hS.comap_le] at hint
  have hcoeff : (∫ z, f z * spinSign (S z) ∂mu) = a := by
    simpa [Pi.mul_apply, ha, mul_assoc, spinSign_mul_self] using hint
  intro ω
  rw [ha, hcoeff]

theorem HasFreeIsingLaw.condExp_root_given_spin {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    ∀ x, mu[(fun y => spinSign (y (ConnectedHull.root d))) |
      isingSpinMeasurable.comap (fun y => y v)] x =
        theta^v.1.length * spinSign (x v) := by
  let := hmu.isProbabilityMeasure
  have hf : Integrable (fun y : TreeVertex d → IsingSpin =>
      spinSign (y (ConnectedHull.root d))) mu := by
    simpa only [IsingSpin.toReal_eq_spinSign] using integrable_spin mu (ConnectedHull.root d)
  have h := BinaryRegression.condExp_eq_cov_mul_spinSign (measurable_pi_apply v)
    (hmu.marginal v) hf (hmu.integral_spinSign (ConnectedHull.root d))
  simpa only [hmu.root_correlation hlo hhi v] using h

theorem HasFreeIsingLaw.condExp_spin_given_root {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    ∀ x, mu[(fun y => spinSign (y v)) |
      isingSpinMeasurable.comap (fun y => y (ConnectedHull.root d))] x =
        theta^v.1.length * spinSign (x (ConnectedHull.root d)) := by
  let := hmu.isProbabilityMeasure
  have hf : Integrable (fun y : TreeVertex d → IsingSpin => spinSign (y v)) mu := by
    simpa only [IsingSpin.toReal_eq_spinSign] using integrable_spin mu v
  have h := BinaryRegression.condExp_eq_cov_mul_spinSign
    (measurable_pi_apply (ConnectedHull.root d))
    (hmu.marginal (ConnectedHull.root d)) hf (hmu.integral_spinSign v)
  have hc : (∫ y, spinSign (y v) * spinSign (y (ConnectedHull.root d)) ∂mu) =
      theta^v.1.length := by
    simpa only [mul_comm] using hmu.root_correlation hlo hhi v
  simpa only [hc] using h

theorem HasFreeIsingLaw.integral_condExp_root_given_spin_sq {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    ∫ x, (mu[(fun y => spinSign (y (ConnectedHull.root d))) |
      isingSpinMeasurable.comap (fun y => y v)] x)^2 ∂mu =
        theta^(2 * v.1.length) := by
  let := hmu.isProbabilityMeasure
  simp only [hmu.condExp_root_given_spin hlo hhi v, mul_pow, spinSign_sq, mul_one]
  simp [← pow_mul, Nat.mul_comm]

end Problem367

end

end OAI
