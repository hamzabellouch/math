import OAI.Analysis.LipschitzHilbert.Phase.PlanarSliceFourierAngular
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! Product-coordinate Plancherel and the common-frequency witness
needed for the actual planar packet Gram matrix. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

private abbrev HilbertPlane := WithLp 2 (ℝ×ℝ)

private def liftPlanar (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap HilbertPlane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) f

private theorem integral_hilbertPlane {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : HilbertPlane → V) :
    (∫ x, F x)=(∫ z : ℝ×ℝ, F (WithLp.toLp 2 z) ∂volume.prod volume) := by
  exact ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ×ℝ)).measurableEmbedding F).symm

private theorem fourier_liftPlanar (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    𝓕 (liftPlanar f) (WithLp.toLp 2 z)=planarFourier f z := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq,integral_hilbertPlane]
  unfold planarFourier
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [WithLp.prod_inner_apply,Real.inner_apply,liftPlanar,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply]
  rfl

/-- Lift a planar Schwartz function to the Hilbert norm on the same coordinates. -/
def hilbertPlanarSchwartz (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ :=
  liftPlanar f

theorem hilbertPlanarSchwartz_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    hilbertPlanarSchwartz f (WithLp.toLp 2 z)=f z := rfl

theorem integral_hilbertPlanar_bridge {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : WithLp 2 (ℝ×ℝ) → V) :
    (∫ x, F x)=(∫ z : ℝ×ℝ, F (WithLp.toLp 2 z) ∂volume.prod volume) :=
  integral_hilbertPlane F

theorem fourier_hilbertPlanar_bridge (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    𝓕 (hilbertPlanarSchwartz f) (WithLp.toLp 2 z)=planarFourier f z :=
  fourier_liftPlanar f z

/-- Plancherel for the manuscript's product-coordinate Fourier transform. -/
theorem planar_integral_inner_fourier (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, inner ℂ (planarFourier f z) (planarFourier g z) ∂volume.prod volume)=
      ∫ z, inner ℂ (f z) (g z) ∂volume.prod volume := by
  calc
    _ = ∫ x : HilbertPlane, inner ℂ (𝓕 (liftPlanar f) x) (𝓕 (liftPlanar g) x) := by
      rw [integral_hilbertPlane]
      simp only [fourier_liftPlanar]
    _ = ∫ x : HilbertPlane, inner ℂ (liftPlanar f x) (liftPlanar g x) :=
      SchwartzMap.integral_inner_fourier_fourier (liftPlanar f) (liftPlanar g)
    _ = _ := by
      rw [integral_hilbertPlane]
      rfl

theorem planar_inner_eq_zero_of_disjoint (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hdisjoint : ∀ z, planarFourier f z=0 ∨ planarFourier g z=0) :
    (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)=0 := by
  rw [←planar_integral_inner_fourier f g]
  have hz (z : ℝ×ℝ) : inner ℂ (planarFourier f z) (planarFourier g z)=0 := by
    rcases hdisjoint z with hf | hg
    · rw [hf,inner_zero_left]
    · rw [hg,inner_zero_right]
  simp only [hz,integral_zero]

/-- Nonzero interaction gives an actual common angular frequency;
no support-overlap premise is added to the packet estimate. -/
theorem exists_common_angular_frequency (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) :
    ∃ ξ η, planarAngularFourier f (ξ,η)≠0 ∧ planarAngularFourier g (ξ,η)≠0 := by
  have hex : ∃ z, planarFourier f z≠0 ∧ planarFourier g z≠0 := by
    by_contra h
    apply hinner
    apply planar_inner_eq_zero_of_disjoint f g
    intro z
    by_cases hf : planarFourier f z=0
    · exact Or.inl hf
    · exact Or.inr (by by_contra hg; exact h ⟨z,hf,hg⟩)
  obtain ⟨z,hf,hg⟩ := hex
  refine ⟨(2*Real.pi)*z.1,(2*Real.pi)*z.2,?_,?_⟩
  · simpa only [planarAngularFourier,mul_div_cancel_left₀ _ (by positivity : (2:ℝ)*Real.pi≠0)] using hf
  · simpa only [planarAngularFourier,mul_div_cancel_left₀ _ (by positivity : (2:ℝ)*Real.pi≠0)] using hg

end LipschitzHilbert

end

end OAI
