import OAI.Geometry.RCD.Sobolev.BoundedLpSquare
import OAI.Geometry.RCD.Sobolev.InnerProductVariation

namespace OAI

/-! # Scalar differentiation of a bounded L² square against a varying weight -/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Pairing a bounded L² square with a bounded weight agrees with the
continuous weighted quadratic form. -/
theorem inner_boundedLpSquare (f w : Lp ℝ 2 μ) (V : Lp ℝ ∞ μ)
    (hV : V =ᵐ[μ] w) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂μ, |f x| ≤ C) :
    inner ℝ w (boundedLpSquare μ f C hC hf) = inner ℝ f (lpMultiplier μ V f) := by
  simp only [L2.inner_def,Real.inner_apply]
  apply integral_congr_ae
  filter_upwards [hV,boundedLpSquare_coe μ f C hC hf,lpMultiplier_coe μ V f] with x hv hs hp
  rw [hs,hp,hv]
  ring

/-- The derivative uses only L² derivatives of the two paths; boundedness
supplies the extra continuity required for the square. -/
theorem boundedSquare_pairing_hasDerivAt {F W : ℝ → Lp ℝ 2 μ} {t C : ℝ}
    {F' W' : Lp ℝ 2 μ} (hC : 0 ≤ C) (hb : ∀ s, ∀ᵐ x ∂μ, |F s x| ≤ C)
    (hF : HasDerivAt F F' t) (hW : HasDerivAt W W' t)
    (V : Lp ℝ ∞ μ) (hV : V =ᵐ[μ] W t) :
    HasDerivAt (fun s => inner ℝ (W s) (boundedLpSquare μ (F s) C hC (hb s)))
      (inner ℝ W' (boundedLpSquare μ (F t) C hC (hb t))+
        2*inner ℝ F' (lpMultiplier μ V (F t))) t := by
  apply hasDerivAt_inner_of_frozen hW (boundedLpSquare_continuousAt μ hC hF.continuousAt hb)
  have hd := hF.inner ℝ ((lpMultiplier μ V).hasFDerivAt.comp_hasDerivAt t hF)
  have he : inner ℝ (F t) (lpMultiplier μ V F') = inner ℝ F' (lpMultiplier μ V (F t)) := by
    rw [lpMultiplier_inner_symm]
    exact real_inner_comm _ _
  rw [he] at hd
  have hfun : (fun s => inner ℝ (W t) (boundedLpSquare μ (F s) C hC (hb s))) =
      (fun s => inner ℝ (F s) (lpMultiplier μ V (F s))) := by
    funext s
    exact inner_boundedLpSquare μ (F s) (W t) V hV C hC (hb s)
  rw [hfun]
  dsimp only [Function.comp_apply] at hd
  convert! hd using 1
  ring

end RegularPointCoordinates

end

end OAI
