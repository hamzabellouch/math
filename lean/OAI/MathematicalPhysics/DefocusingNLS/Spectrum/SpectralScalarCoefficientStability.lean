import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFiniteExistence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFiniteStability

namespace OAI

/-! Finite-interval continuous dependence for the actual scalar coefficients,
used for the rescaled Airy limit. -/

open Set
namespace DefocusingNLS

theorem spectralScalarField_coefficient_bound (V W : ℂ) (u v : ℂ × ℂ) :
    ‖spectralScalarField V u-spectralScalarField W v‖≤
      (1+‖V‖)*‖u-v‖+‖W-V‖*‖v‖ := by
  have he : spectralScalarField V u-spectralScalarField W v=
      (spectralScalarField V u-spectralScalarField V v)+(0,(W-V)*v.1) := by
    apply Prod.ext <;> dsimp only [spectralScalarField,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] <;> ring
  have hn : ‖((0 : ℂ),(W-V)*v.1)‖≤‖W-V‖*‖v‖ := by
    rw [Prod.norm_def,Prod.fst,Prod.snd,norm_zero,max_eq_right (norm_nonneg _),norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg _)
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (spectralScalarField_lipschitz V u v) hn)

theorem spectralScalar_coefficient_stability
    (T B delta M : ℝ) (hB : 0≤B) (hd : 0≤delta) (hM : 0≤M)
    (V W : ℝ → ℂ) (q p : ℝ → ℂ × ℂ)
    (hq : ContinuousOn q (Icc 0 T)) (hp : ContinuousOn p (Icc 0 T))
    (hqD : ∀ t ∈ Icc 0 T, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hpD : ∀ t ∈ Icc 0 T, HasDerivAt p (spectralScalarField (W t) (p t)) t)
    (hV : ∀ t ∈ Icc 0 T, ‖V t‖≤B)
    (hVW : ∀ t ∈ Icc 0 T, ‖W t-V t‖≤delta)
    (hpb : ∀ t ∈ Icc 0 T, ‖p t‖≤M)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖q t-p t‖≤(‖q 0-p 0‖+delta*M/(1+B))*Real.exp ((1+B)*T) := by
  apply radial_finite_difference_bound T (1+B) (delta*M) (by positivity) (mul_nonneg hd hM)
    q p (fun t => spectralScalarField (V t) (q t)) (fun t => spectralScalarField (W t) (p t))
    hq hp hqD hpD _ t ht
  intro s hs
  apply (spectralScalarField_coefficient_bound (V s) (W s) (q s) (p s)).trans
  exact add_le_add (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hV s hs)) (norm_nonneg _))
    (mul_le_mul (hVW s hs) (hpb s hs) (norm_nonneg _) hd)

end DefocusingNLS

end OAI
