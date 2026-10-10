import OAI.Analysis.KadisonKastler.L2LinearFields
import OAI.Analysis.KadisonKastler.HilbertSumIsometryMap

namespace OAI

/-! # Constant Hilbert-space coordinate changes on L²

This is used to lift the countable coordinate fibers into the universe of
the original representation without changing their operators or measures.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H K : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (μ : Measure X) (e : H ≃ₗᵢ[ℂ] K)

def l2CoordinateIsometry : Lp H 2 μ →ₗᵢ[ℂ] Lp K 2 μ :=
  l2IsometryField μ (fun _ => e.toLinearIsometry)
    (fun _ => stronglyMeasurable_const.aestronglyMeasurable)

theorem l2CoordinateIsometry_ae (f : Lp H 2 μ) :
    l2CoordinateIsometry μ e f =ᵐ[μ] fun x => e (f x) :=
  l2IsometryField_ae μ (fun _ => e.toLinearIsometry)
    (fun _ => stronglyMeasurable_const.aestronglyMeasurable) f

theorem l2CoordinateIsometry_surjective : Function.Surjective (l2CoordinateIsometry μ e) := by
  intro f
  refine ⟨l2CoordinateIsometry μ e.symm f, ?_⟩
  apply Lp.ext
  filter_upwards [l2CoordinateIsometry_ae μ e (l2CoordinateIsometry μ e.symm f),
    l2CoordinateIsometry_ae μ e.symm f] with x hx hy
  rw [hx, hy, LinearIsometryEquiv.apply_symm_apply]

def l2CoordinateEquiv : Lp H 2 μ ≃ₗᵢ[ℂ] Lp K 2 μ :=
  LinearIsometryEquiv.ofSurjective (l2CoordinateIsometry μ e) (l2CoordinateIsometry_surjective μ e)

theorem l2CoordinateEquiv_ae (f : Lp H 2 μ) :
    l2CoordinateEquiv μ e f =ᵐ[μ] fun x => e (f x) :=
  l2CoordinateIsometry_ae μ e f

end

end KadisonKastler

end OAI
