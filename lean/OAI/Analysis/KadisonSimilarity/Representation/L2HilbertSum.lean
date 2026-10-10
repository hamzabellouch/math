import OAI.Analysis.KadisonSimilarity.Representation.LocalizedL2Bound
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! The Hilbert sum of scalar L² spaces over one measure is the L² space
of the coordinate Hilbert space. The construction uses actual L² maps. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Lift a Hilbert isometry pointwise to L². -/
def l2MapIsometry (J : E →ₗᵢ[ℂ] F) : Lp E 2 μ →ₗᵢ[ℂ] Lp F 2 μ where
  toLinearMap := (J.toContinuousLinearMap.compLpL 2 μ).toLinearMap
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [J.toContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ) f] with x hx
    change ‖(J.toContinuousLinearMap.compLpL 2 μ) f x‖ ^ 2 = ‖f x‖ ^ 2
    rw [hx]
    change ‖J (f x)‖ ^ 2 = ‖f x‖ ^ 2
    rw [J.norm_map]

theorem l2MapIsometry_ae (J : E →ₗᵢ[ℂ] F) (f : Lp E 2 μ) :
    l2MapIsometry μ J f =ᵐ[μ] (fun x => J (f x)) :=
  J.toContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ) f

variable {ι : Type*} [DecidableEq ι]

abbrev ScalarHilbertCoordinates (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

def scalarCoordinateIsometry (i : ι) : ℂ →ₗᵢ[ℂ] ScalarHilbertCoordinates ι where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 i).toLinearMap
  norm_map' z := by
    change ‖lp.single (E := fun _ : ι => ℂ) 2 i z‖ = ‖z‖
    exact lp.norm_single (p := 2) (E := fun _ : ι => ℂ) (by norm_num) i z

def l2CoordinateIsometry (i : ι) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp (ScalarHilbertCoordinates ι) 2 μ :=
  l2MapIsometry μ (scalarCoordinateIsometry i)

def l2CoordinateProjection (i : ι) : Lp (ScalarHilbertCoordinates ι) 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).compLpL 2 μ

omit [DecidableEq ι] in
theorem l2CoordinateProjection_ae (i : ι) (f : Lp (ScalarHilbertCoordinates ι) 2 μ) :
    l2CoordinateProjection μ i f =ᵐ[μ] (fun x => f x i) :=
  (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).coeFn_compLpL (p := 2) (μ := μ) f

theorem l2Coordinate_inner (i : ι) (f : Lp ℂ 2 μ)
    (g : Lp (ScalarHilbertCoordinates ι) 2 μ) :
    ⟪l2CoordinateIsometry μ i f, g⟫_ℂ = ⟪f, l2CoordinateProjection μ i g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2MapIsometry_ae μ (scalarCoordinateIsometry i) f,
    l2CoordinateProjection_ae μ i g] with x hf hg
  change inner ℂ (l2MapIsometry μ (scalarCoordinateIsometry i) f x) (g x) = _
  rw [hf, hg]
  exact lp.inner_single_left (𝕜 := ℂ) i (f x) (g x)

theorem l2Coordinate_orthogonal : OrthogonalFamily ℂ (fun _ : ι => Lp ℂ 2 μ)
    (l2CoordinateIsometry μ) := by
  intro i j hij f g
  rw [l2Coordinate_inner, L2.inner_def]
  have hz : l2CoordinateProjection μ i (l2CoordinateIsometry μ j g) =ᵐ[μ] 0 := by
    filter_upwards [l2CoordinateProjection_ae μ i (l2CoordinateIsometry μ j g),
      l2MapIsometry_ae μ (scalarCoordinateIsometry j) g] with x hp hi
    rw [hp]
    change (l2MapIsometry μ (scalarCoordinateIsometry j) g x) i = 0
    rw [hi]
    change lp.single (E := fun _ : ι => ℂ) 2 j (g x) i = 0
    simp [lp.single_apply, hij.symm]
  calc
    _ = ∫ _x : Ω, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hz] with x hx
      simp only [hx, Pi.zero_apply, inner_zero_right]
    _ = 0 := integral_zero _ _

variable [Countable ι]

theorem l2Coordinate_isHilbertSum : IsHilbertSum ℂ (fun _ : ι => Lp ℂ 2 μ)
    (l2CoordinateIsometry μ) := by
  apply IsHilbertSum.mk (l2Coordinate_orthogonal μ)
  let M := (⨆ i : ι, LinearMap.range (l2CoordinateIsometry μ i).toLinearMap).closure
  suffices hM : M.toSubmodule = ⊤ by rw [show
    (⨆ i : ι, LinearMap.range (l2CoordinateIsometry μ i).toLinearMap).topologicalClosure =
      M.toSubmodule from rfl, hM]
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  change g = 0
  have hzero (i : ι) : l2CoordinateProjection μ i g = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← l2Coordinate_inner]
    apply hg
    exact Submodule.le_topologicalClosure _
      (Submodule.mem_iSup_of_mem i ⟨l2CoordinateProjection μ i g, rfl⟩)
  apply Lp.ext
  have hcoord (i : ι) : ∀ᵐ x ∂μ, g x i = 0 := by
    filter_upwards [l2CoordinateProjection_ae μ i g, Lp.coeFn_zero (E := ℂ) (p := 2) μ] with x hi hz
    rw [hzero i] at hi
    exact hi.symm.trans hz
  filter_upwards [eventually_countable_forall.mpr hcoord,
    Lp.coeFn_zero (E := ScalarHilbertCoordinates ι) (p := 2) μ] with x hx hz
  rw [hz]
  ext i
  exact hx i

def l2HilbertSumEquiv : Lp (ScalarHilbertCoordinates ι) 2 μ ≃ₗᵢ[ℂ]
    lp (fun _ : ι => Lp ℂ 2 μ) 2 := (l2Coordinate_isHilbertSum μ).linearIsometryEquiv

end KadisonSimilarity

end

end OAI
