import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryVolumeTrace

namespace OAI

/-! # Absolute boundary masses from compact image sandwiches -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- A compact lower/upper sandwich gives one positive comparison constant
for the absolute boundary image masses throughout the map family. -/
theorem boundary_image_mass_bounds
    {P G S T : Type*} [Group G] [MeasurableSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : P → S → T) (f : P → G → G) (μ : Measure T) (height : G → ℝ)
    (hvolume : ∀ g E, μ (actT g '' E) = ENNReal.ofReal (Real.exp (height g)) * μ E)
    (U : Set S) (Vminus Vplus : Set T)
    (hVminus0 : μ Vminus ≠ 0) (hVminusfinite : μ Vminus ≠ ⊤) (hVplusfinite : μ Vplus ≠ ⊤)
    (hsandwich : ∀ p x, actT (f p x) '' Vminus ⊆ B p '' (actS x '' U) ∧
      B p '' (actS x '' U) ⊆ actT (f p x) '' Vplus) :
    ∃ K : ℝ, 0 < K ∧ ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μ (B p '' (actS x '' U)) ∧
      μ (B p '' (actS x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))) := by
  let c := (μ Vminus).toReal
  let C := (μ Vplus).toReal
  have hc : 0 < c := ENNReal.toReal_pos hVminus0 hVminusfinite
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  let K := C + 1 / c + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKC : C ≤ K := by dsimp [K]; linarith [one_div_nonneg.mpr hc.le]
  have hKc : 1 ≤ K * c := by
    have h : (1 / c) * c = (1 : ℝ) := div_mul_cancel₀ 1 hc.ne'
    dsimp only [K]
    nlinarith [mul_nonneg hC hc.le]
  have hKcm : 1 ≤ ENNReal.ofReal K * μ Vminus := by
    rw [← ENNReal.ofReal_toReal hVminusfinite, ← ENNReal.ofReal_mul hK.le]
    exact_mod_cast ENNReal.ofReal_le_ofReal hKc
  have hCm : μ Vplus ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_toReal hVplusfinite]
    exact ENNReal.ofReal_le_ofReal hKC
  refine ⟨K, hK, ?_⟩
  intro p x
  have hlo := measure_mono (μ := μ) (hsandwich p x).1
  have hup := measure_mono (μ := μ) (hsandwich p x).2
  rw [hvolume] at hlo hup
  constructor
  · calc
      ENNReal.ofReal (Real.exp (height (f p x))) =
          ENNReal.ofReal (Real.exp (height (f p x))) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (Real.exp (height (f p x))) *
          (ENNReal.ofReal K * μ Vminus) := mul_le_mul' le_rfl hKcm
      _ = ENNReal.ofReal K *
          (ENNReal.ofReal (Real.exp (height (f p x))) * μ Vminus) := by ac_rfl
      _ ≤ ENNReal.ofReal K * μ (B p '' (actS x '' U)) := mul_le_mul' le_rfl hlo
  · exact hup.trans (by simpa only [mul_comm] using mul_le_mul' le_rfl hCm)

/-- A bounded change of scalar height changes its exponential mass by one
uniform multiplicative constant. -/
theorem exponential_mass_bounds_of_abs_sub_le
    {a b K C : ℝ} {m : ℝ≥0∞} (hK : 0 ≤ K)
    (hab : |a - b| ≤ C)
    (hlower : ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal K * m)
    (hupper : m ≤ ENNReal.ofReal K * ENNReal.ofReal (Real.exp a)) :
    ENNReal.ofReal (Real.exp b) ≤ ENNReal.ofReal (K * Real.exp C) * m ∧
      m ≤ ENNReal.ofReal (K * Real.exp C) * ENNReal.ofReal (Real.exp b) := by
  have ha : a ≤ C + b := by have := le_abs_self (a - b); linarith
  have hb : b ≤ C + a := by have := neg_le_abs (a - b); linarith
  have ha' : ENNReal.ofReal (Real.exp a) ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (Real.exp b) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ha)
  have hb' : ENNReal.ofReal (Real.exp b) ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (Real.exp a) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hb)
  rw [ENNReal.ofReal_mul hK]
  constructor
  · have hh := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp C))) hlower
    exact hb'.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)
  · have hh := mul_le_mul' (le_refl (ENNReal.ofReal K)) ha'
    exact hupper.trans (by simpa only [mul_assoc] using hh)

end PolycyclicRecognition

end

end OAI
