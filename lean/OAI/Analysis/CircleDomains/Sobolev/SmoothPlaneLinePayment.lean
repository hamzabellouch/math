import OAI.Analysis.CircleDomains.Sobolev.SmoothLineOscillation

namespace OAI

/-! Integrate the positive oscillation cost over an arbitrary finite
measurable set of horizontal lines. No choice of crossing points needs
to be measurable. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_plane_half_payment
    {v : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hv : ∀ y, ContDiff ℝ 1 (v y))
    (hE : Integrable (fun p : ℝ × ℝ => deriv (v p.1) p.2^2) (volume.prod volume))
    {J : Set ℝ} (_hJ : MeasurableSet J) (hJf : volume J ≠ ∞)
    (hcross : ∀ᵐ y ∂volume.restrict J, ∃ c ∈ Icc (-L) L,
      (1:ℝ)/2 ≤ v y c-v y (-L)) :
    (volume J).toReal/(8*L) ≤ ∫ p : ℝ × ℝ, deriv (v p.1) p.2^2 ∂(volume.prod volume) := by
  let E := fun p : ℝ × ℝ => deriv (v p.1) p.2^2
  let μ := (volume.restrict J).prod (volume.restrict (Ioc (-L) L))
  have hEr : Integrable E μ := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact hE.restrict
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJf
  have hLL : -L ≤ L := by linarith
  have hbound : ∀ᵐ y ∂volume.restrict J,
      1/(8*L) ≤ ∫ x in Ioc (-L) L, deriv (v y) x^2 := by
    filter_upwards [hcross] with y hy
    obtain ⟨c,hc,hcjump⟩ := hy
    simpa only [intervalIntegral.integral_of_le hLL] using smooth_line_half_payment hL (hv y) hc hcjump
  calc
    _ = ∫ _y in J, (1/(8*L) : ℝ) := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,div_eq_mul_inv,one_mul]
    _ ≤ ∫ y in J, ∫ x in Ioc (-L) L, deriv (v y) x^2 :=
      integral_mono_ae (integrable_const _) hEr.integral_prod_left hbound
    _ = ∫ p, E p ∂μ := (integral_prod _ hEr).symm
    _ = ∫ p in J ×ˢ Ioc (-L) L, E p ∂(volume.prod volume) := by
      dsimp only [μ]
      rw [Measure.prod_restrict]
    _ ≤ _ := setIntegral_le_integral hE (Eventually.of_forall (fun p => sq_nonneg _))

end CircleDomainRigidity

end

end OAI
