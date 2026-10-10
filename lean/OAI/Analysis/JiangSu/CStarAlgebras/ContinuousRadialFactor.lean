import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace ContinuousRadialFactor
open Filter Topology

def radial (z : ℂ) : ℂ := (Real.sqrt ‖z‖ : ℂ)⁻¹*z

lemma radial_zero : radial 0=0 := by simp [radial]

lemma sqrt_mul_radial (z : ℂ) : (Real.sqrt ‖z‖ : ℂ)*radial z=z := by
  by_cases hz : z=0
  · simp [hz,radial_zero]
  · have hs : (Real.sqrt ‖z‖ : ℂ)≠0 := by
      exact_mod_cast (Real.sqrt_pos.2 (norm_pos_iff.2 hz)).ne'
    simp [radial,hs]

lemma norm_radial (z : ℂ) : ‖radial z‖=Real.sqrt ‖z‖ := by
  by_cases hz : z=0
  · simp [hz,radial_zero]
  · have hs : Real.sqrt ‖z‖≠0 := (Real.sqrt_pos.2 (norm_pos_iff.2 hz)).ne'
    rw [radial,norm_mul,norm_inv,Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc
      (Real.sqrt ‖z‖)⁻¹*‖z‖=(Real.sqrt ‖z‖)⁻¹*(Real.sqrt ‖z‖*Real.sqrt ‖z‖) := by
        rw [←sq,Real.sq_sqrt (norm_nonneg z)]
      _=Real.sqrt ‖z‖ := by rw [←mul_assoc,inv_mul_cancel₀ hs,one_mul]

lemma continuous_radial : Continuous radial := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    rw [ContinuousAt,radial_zero,tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_radial]
    have h := (Real.continuous_sqrt.comp continuous_norm).continuousAt (x := (0:ℂ))
    change Tendsto (fun x : ℂ => Real.sqrt ‖x‖) (𝓝 0) (𝓝 (Real.sqrt ‖(0:ℂ)‖)) at h
    simpa using h
  · exact (((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).continuousAt.inv₀
      (by
        change (Real.sqrt ‖z‖ : ℂ)≠0
        exact_mod_cast (Real.sqrt_pos.2 (norm_pos_iff.2 hz)).ne')).mul continuousAt_id)

variable {X : Type*} [TopologicalSpace X]

theorem exists_factorization (f : C(X,ℂ)) :
    ∃ g h : C(X,ℂ), g*h=f ∧ (∀ x, f x=0 → g x=0 ∧ h x=0) := by
  refine ⟨⟨fun x => (Real.sqrt ‖f x‖ : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp f.continuous.norm)⟩,
    ⟨fun x => radial (f x),continuous_radial.comp f.continuous⟩,?_,?_⟩
  · ext x
    exact sqrt_mul_radial (f x)
  · intro x hx
    simp [hx,radial_zero]

end ContinuousRadialFactor

end
end

end OAI
