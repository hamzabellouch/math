import OAI.NumberTheory.JointDickman.Analysis.ZetaContourRegion
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! # Normalized logarithms on the finite zero-free rectangles -/
namespace JointDickman
open Set

def zetaOpenRectangle (δ T : ℝ) : Set ℂ :=
  (Complex.re ⁻¹' Ioo (1-δ) 2) ∩ (Complex.im ⁻¹' Ioo (-T) T)

theorem zetaOpenRectangle_isOpen (δ T : ℝ) : IsOpen (zetaOpenRectangle δ T) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem zetaOpenRectangle_convex (δ T : ℝ) : Convex ℝ (zetaOpenRectangle δ T) :=
  ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

theorem zetaOpenRectangle_one {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    (1:ℂ) ∈ zetaOpenRectangle δ T := by
  change ((1:ℝ) ∈ Ioo (1-δ) 2) ∧ (0:ℝ) ∈ Ioo (-T) T
  constructor <;> constructor <;> linarith

theorem zeta_rectangle_log : ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧ ∀ T : ℝ, 0 < T →
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (zetaOpenRectangle (zetaContourWidth A T) T) ∧
      f 1 = 0 ∧ ∀ s ∈ zetaOpenRectangle (zetaContourWidth A T) T,
        Complex.exp (f s) = zetaPoleFactor s := by
  obtain ⟨A,hA,hA4,hzero⟩ := zeta_contour_zero_free
  refine ⟨A,hA,hA4,fun T hT => ?_⟩
  obtain ⟨hδ,_,hzeta⟩ := hzero T hT.le
  have h1 := zetaOpenRectangle_one hδ hT
  let : ContractibleSpace (zetaOpenRectangle (zetaContourWidth A T) T) :=
    (zetaOpenRectangle_convex _ _).contractibleSpace ⟨1,h1⟩
  have hsimp : IsSimplyConnected (zetaOpenRectangle (zetaContourWidth A T) T) := by
    change SimplyConnectedSpace _
    infer_instance
  apply exists_zetaPoleLog hsimp (zetaOpenRectangle_isOpen _ _) h1
  intro s hs _
  exact hzeta s hs.1.1.le (abs_le.mpr ⟨hs.2.1.le,hs.2.2.le⟩)

end JointDickman

end OAI
