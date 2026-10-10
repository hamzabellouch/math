import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmoothBarrierRegular
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarComparison

namespace OAI

/-! The source-width lower barrier forces a uniformly positive core pressure. -/

open Set
namespace DefocusingNLS

noncomputable def radialCoreBarrier (R m : ℝ) : ℝ → ℝ :=
  radialLowerBarrier (1/10000) (R-7/10000) m

theorem radialCoreBarrier_flat (R m r : ℝ) (hr : r ≤ R-7/10000) :
    radialCoreBarrier R m r=m := by
  have h := (radialSmoothRamp_flat (1/10000) (r-(R-7/10000)) (by linarith)).1
  simp only [radialCoreBarrier,radialLowerBarrier,h,zero_div,sub_zero]

theorem radialCoreBarrier_bounds (R m r : ℝ) (hm : (999/1000 : ℝ) ≤ m)
    (hr : r ∈ Icc 0 R) :
    (1/2 : ℝ) ≤ radialCoreBarrier R m r ∧ radialCoreBarrier R m r ≤ m := by
  have hf := radialSmoothRamp_bounds (1/10000) (by norm_num) (r-(R-7/10000))
  have hx : max (r-(R-7/10000)) 0 ≤ (7/10000 : ℝ) :=
    max_le (by linarith [hr.2]) (by norm_num)
  have hsq := pow_le_pow_left₀ (le_max_right (r-(R-7/10000)) 0) hx 2
  dsimp only [radialCoreBarrier,radialLowerBarrier]
  constructor <;> nlinarith [hf.1,hf.2.1]

theorem radialCoreBarrier_boundary (R m lo : ℝ) (hm : m ≤ 1)
    (hlo : 1-(1/10000 : ℝ)^2/5 ≤ lo) : radialCoreBarrier R m R ≤ lo := by
  have hf := (radialSmoothRamp_quadratic (1/10000) (R-(R-7/10000))
    (by norm_num) (by linarith)).1
  dsimp only [radialCoreBarrier,radialLowerBarrier]
  rw [hf]
  nlinarith

theorem radialCoreBarrier_origin (R m : ℝ) (hR : 1 ≤ R) :
    deriv (radialCoreBarrier R m) 0=0 := by
  rw [show radialCoreBarrier R m=radialLowerBarrier (1/10000) (R-7/10000) m from rfl,
    (hasDerivAt_radialLowerBarrier _ _ _ _ (by norm_num)).deriv]
  have hf := (radialSmoothRamp_flat (1/10000) (0-(R-7/10000)) (by linarith)).2.1
  rw [hf]
  norm_num

theorem radialCoreBarrier_laplacian_bound (R m r : ℝ) (hR : 1 ≤ R)
    (hr : r ∈ Ioo 0 R) :
    -deriv (deriv (radialCoreBarrier R m)) r-11/r*deriv (radialCoreBarrier R m) r ≤ (1/20 : ℝ) := by
  change -deriv (deriv (radialLowerBarrier (1/10000) (R-7/10000) m)) r-
    11/r*deriv (radialLowerBarrier (1/10000) (R-7/10000) m) r ≤ _
  rw [radialLowerBarrier_laplacian _ _ _ _ (by norm_num)]
  by_cases hc : r ≤ R-7/10000
  · have hf := radialSmoothRamp_flat (1/10000) (r-(R-7/10000)) (by linarith)
    rw [hf.2.1,hf.2.2]
    norm_num
  · have hx : 0 < r-(R-7/10000) := by linarith
    have hf := radialSmoothRamp_bounds (1/10000) (by norm_num) (r-(R-7/10000))
    have hD : radialSmoothRampD (1/10000) (r-(R-7/10000)) ≤ (14/10000 : ℝ) := by
      have hb := hf.2.2.2.1
      rw [max_eq_left hx.le] at hb
      linarith [hr.2]
    have hdiv : 11/r ≤ (12 : ℝ) := (div_le_iff₀ hr.1).2 (by linarith)
    have hprod := mul_le_mul hdiv hD hf.2.2.1 (by norm_num : (0 : ℝ) ≤ 12)
    nlinarith [hf.2.2.2.2.2]

theorem radialCoreBarrier_subsolution (p : ℕ) (hp : 2 ≤ p) (R m : ℝ)
    (hR : 1 ≤ R) (hm : (999/1000 : ℝ) ≤ m) (hmp : m^(p-1)=(1/5 : ℝ))
    (V : ℝ → ℝ) (hV : ∀ r ∈ Ioo 0 R, (3/10 : ℝ) ≤ V r) :
    ∀ r ∈ Ioo 0 R,
      -deriv (deriv (radialCoreBarrier R m)) r-11/r*deriv (radialCoreBarrier R m) r+
        (radialCoreBarrier R m r)^p ≤ V r*radialCoreBarrier R m r := by
  intro r hr
  have hB := radialCoreBarrier_bounds R m r hm ⟨hr.1.le,hr.2.le⟩
  have hnonneg : 0 ≤ radialCoreBarrier R m r := le_trans (by norm_num) hB.1
  have hpow := pow_le_pow_left₀ hnonneg hB.2 (p-1)
  rw [hmp] at hpow
  have he : (radialCoreBarrier R m r)^p=
      (radialCoreBarrier R m r)^(p-1)*radialCoreBarrier R m r := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowp : (radialCoreBarrier R m r)^p ≤ radialCoreBarrier R m r/5 := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hpow hnonneg]
  have hVmul := mul_le_mul_of_nonneg_right (hV r hr) hnonneg
  linarith [radialCoreBarrier_laplacian_bound R m r hR hr]

end DefocusingNLS

end OAI
