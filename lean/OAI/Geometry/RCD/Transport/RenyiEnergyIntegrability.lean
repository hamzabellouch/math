import OAI.Geometry.RCD.Transport.RenyiGlobalVariation

namespace OAI

/-! # Integrability of the finite-dimensional energy weight -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integrable_positive_power_of_bounded {r : X → ℝ} (hr : Measurable r)
    (hp : ∀ᵐ x ∂μ, 0<r x) (hi : Integrable r μ) {M a : ℝ}
    (hb : ∀ᵐ x ∂μ, r x≤M) (ha : 1≤a) : Integrable (fun x => (r x)^a) μ := by
  have ht : Integrable (fun x => r x*(r x)^(a-1)) μ := by
    apply hi.mul_bdd (hr.pow_const (a-1)).aestronglyMeasurable
    filter_upwards [hp,hb] with x hx hm
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)]
    exact Real.rpow_le_rpow hx.le hm (by linarith)
  apply ht.congr
  filter_upwards [hp] with x hx
  calc
    _ = (r x)^(1:ℝ)*(r x)^(a-1) := by rw [Real.rpow_one]
    _ = _ := by rw [←Real.rpow_add hx]; congr 1; ring

theorem memLp_density_power {r : X → ℝ} (hr : Measurable r)
    (hp : ∀ᵐ x ∂μ, 0<r x) (hi : Integrable r μ) {M q : ℝ}
    (hb : ∀ᵐ x ∂μ, r x≤M) (hq : 1/2≤q) : MemLp (fun x => (r x)^q) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hr.pow_const q).aestronglyMeasurable).mpr
  have hh := integrable_positive_power_of_bounded μ hr hp hi hb (show 1≤q*2 by linarith)
  apply hh.congr
  filter_upwards [hp] with x hx
  rw [Real.rpow_mul hx.le,Real.rpow_two]

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] (hQ : QuadraticCheegerEnergy μ)

/-- The usual relative gradient estimate for a positive log-Lipschitz
density makes the Rényi energy pairing integrable at every N >= 2. -/
theorem renyi_energy_integrable_of_relative_gradient (u ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0<SobolevSpace.toLp μ hQ ρ x)
    (hi : Integrable (SobolevSpace.toLp μ hQ ρ) μ) {M L q : ℝ}
    (hb : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ ρ x≤M) (hq : 1/2≤q)
    (hrel : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ ρ x≤
      L*SobolevSpace.toLp μ hQ ρ x) :
    Integrable (fun x => (q-1)*(SobolevSpace.toLp μ hQ ρ x)^(q-1)*
      localGamma μ hQ u ρ x) μ := by
  let r := SobolevSpace.toLp μ hQ ρ
  have hr := (Lp.stronglyMeasurable r).measurable
  have hpow := memLp_density_power μ hr hp hi hb hq
  have hprod := (hpow.integrable_mul (Lp.memLp (SobolevSpace.minimalSlope μ hQ u))).const_mul (|q-1| * L)
  apply hprod.mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul ((hr.pow_const (q-1)).const_mul (q-1))
    unfold localGamma
    fun_prop
  · filter_upwards [hp,hrel,localGamma_abs_le μ hQ u ρ,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u)] with x hx hρ hΓ hu
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hx _)]
    calc
      _ ≤ |q-1| * (r x)^(q-1)*(SobolevSpace.minimalSlope μ hQ u x*
          (L*r x)) := mul_le_mul_of_nonneg_left
        (hΓ.trans (mul_le_mul_of_nonneg_left hρ hu)) (by positivity)
      _ = (|q-1| * L)*((r x)^q*SobolevSpace.minimalSlope μ hQ u x) := by
        have he : (r x)^(q-1)*r x=(r x)^q := by
          calc
            _ = (r x)^(q-1)*(r x)^(1:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hx]; congr 1; ring
        calc
          _ = (|q-1| * L)*(((r x)^(q-1)*r x)*SobolevSpace.minimalSlope μ hQ u x) := by ring
          _ = _ := by rw [he]

end RegularPointCoordinates

end

end OAI
