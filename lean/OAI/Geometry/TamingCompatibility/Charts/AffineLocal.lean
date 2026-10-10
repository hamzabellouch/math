import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.InteriorRegularity
import OAI.Geometry.TamingCompatibility.Charts.AffineBase

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def affineHomeomorph (p : E) (r : ℝ) (hr : r ≠ 0) : E ≃ₜ E :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 r hr)).toHomeomorph.trans
    (Homeomorph.addRight p)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineHomeomorph_apply (p x : E) (r : ℝ) (hr : r ≠ 0) :
    affineHomeomorph p r hr x = r • x+p := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma affineSchwartz_comp_inverse (p : E) (r : ℝ) (hr : r ≠ 0) (g : 𝓢(E,ℂ)) :
    affineSchwartz (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) (affineSchwartz p r hr g) = g := by
  ext x
  simp only [affineSchwartz_apply,smul_add,smul_neg,smul_smul,mul_inv_cancel₀ hr,
    one_smul,neg_add_cancel_right]

lemma memSobolevLoc_affine (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {U : Set E} {u : 𝓢'(E,F)} (hu : HilbertSobolev.MemSobolevLoc U n u) :
    HilbertSobolev.MemSobolevLoc ((fun y => r⁻¹ • y + -(r⁻¹ • p)) ⁻¹' U) n
      (affineDistribution p r hr u) := by
  intro g hg hgU
  let q := affineSchwartz p r hr g
  have he : (q : E → ℂ) = g ∘ affineHomeomorph p r hr := by
    funext x
    exact affineSchwartz_apply p x r hr g
  have hq : HasCompactSupport (q : E → ℂ) := by
    rw [he]
    exact hg.comp_homeomorph _
  have hqU : tsupport q ⊆ U := by
    rw [he,tsupport_comp_eq_preimage]
    intro x hx
    have h := hgU hx
    simpa only [mem_preimage,affineHomeomorph_apply,affine_inverse_point p x hr] using h
  have h := memSobolev_nat_affine n p r hr (hu q hq hqU)
  rw [affineDistribution_product,affineSchwartz_comp_inverse] at h
  exact h

lemma memSobolevLoc_zoom (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {U : Set E} {u : 𝓢'(E,F)} (hu : HilbertSobolev.MemSobolevLoc U n u) :
    HilbertSobolev.MemSobolevLoc ((fun y => r • y+p) ⁻¹' U) n (zoomDistribution p r hr u) := by
  have h := memSobolevLoc_affine n (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) hu
  simpa only [zoomDistribution,inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg] using h

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
