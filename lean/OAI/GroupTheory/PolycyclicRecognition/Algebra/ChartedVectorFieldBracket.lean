import OAI.GroupTheory.PolycyclicRecognition.Algebra.RelatedVectorFieldBracket
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothIntegralCurve
import Mathlib.Geometry.Manifold.VectorField.LieBracket

namespace OAI

/-! # Lie brackets in vector-space charts

The source chart is used only locally. This bridges the differential of an
algebra-valued map with the intrinsic bracket of vector fields.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

def chartVectorField (x₀ : M) (V : (x : M) → TangentSpace (𝓘(ℝ, E)) x) : E → E :=
  mpullback (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm V

theorem mlieBracket_eq_chartBracket
    (V W : (x : M) → TangentSpace (𝓘(ℝ, E)) x) (x₀ : M) :
    mlieBracket (𝓘(ℝ, E)) V W x₀ =
      lieBracket ℝ (chartVectorField x₀ V) (chartVectorField x₀ W)
        (extChartAt (𝓘(ℝ, E)) x₀ x₀) := by
  unfold mlieBracket
  rw [mlieBracketWithin_apply, mfderiv_extChartAt_self]
  simp only [mfld_simps, mpullbackWithin_univ]
  change (ContinuousLinearMap.id ℝ E).inverse
    (lieBracketWithin ℝ (chartVectorField x₀ V) (chartVectorField x₀ W) univ
      (extChartAt (𝓘(ℝ, E)) x₀ x₀)) = _
  rw [ContinuousLinearMap.inverse_id]
  change lieBracketWithin ℝ (chartVectorField x₀ V) (chartVectorField x₀ W) univ
    (extChartAt (𝓘(ℝ, E)) x₀ x₀) = _
  rw [lieBracketWithin_univ]
  rfl

theorem differentiableAt_chartVectorField [CompleteSpace E]
    {V : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {x₀ : M}
    (hV : MDifferentiableAt (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓘(ℝ, E)) M)) x₀) :
    DifferentiableAt ℝ (chartVectorField x₀ V) (extChartAt (𝓘(ℝ, E)) x₀ x₀) := by
  have hh := (hV.mdifferentiableWithinAt (s := univ)).differentiableWithinAt_mpullbackWithin_vectorField
  apply differentiableWithinAt_univ.1
  simpa only [mfld_simps, mpullbackWithin_univ, chartVectorField] using hh

theorem fderiv_chart_comp
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt (𝓘(ℝ, E)) x₀).target) :
    fderiv ℝ (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm) y =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y) := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) x₀).symm y := by
    simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have hh : HasFDerivAt (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm)
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y)) y :=
    (((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi.hasMFDerivAt).hasFDerivAt
  exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := E) (F := F) hh

theorem mfderiv_chart_symm_base (x₀ : M) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm
      (extChartAt (𝓘(ℝ, E)) x₀ x₀) = ContinuousLinearMap.id ℝ E := by
  have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext x; simp
  have hh := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀)
  rw [hrange, mfderivWithin_univ] at hh
  exact hh

theorem chartVectorField_related
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {V : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {V' : F → F}
    (hrel : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (V x) = V' (f x))
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt (𝓘(ℝ, E)) x₀).target) :
    fderiv ℝ (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm) y (chartVectorField x₀ V y) =
      V' (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)) := by
  let φ := extChartAt (𝓘(ℝ, E)) x₀
  let D : E →L[ℝ] E := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y
  let B : E →L[ℝ] F := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm y)
  let v : E := V (φ.symm y)
  have hD : D.IsInvertible := by
    have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext x; simp
    have hh := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hy
    rw [hrange, mfderivWithin_univ] at hh
    exact hh
  rw [fderiv_chart_comp hf x₀ hy]
  change B (D (D.inverse v)) = V' (f (φ.symm y))
  exact (congrArg B (hD.self_apply_inverse v)).trans (hrel (φ.symm y))

theorem fderiv_chart_comp_base
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f) (x₀ : M) :
    fderiv ℝ (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm)
      (extChartAt (𝓘(ℝ, E)) x₀ x₀) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by
  have hh := fderiv_chart_comp hf x₀ (mem_extChartAt_target x₀)
  rw [mfderiv_chart_symm_base] at hh
  have hB : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f
      ((extChartAt (𝓘(ℝ, E)) x₀).symm (extChartAt (𝓘(ℝ, E)) x₀ x₀)) : E →L[ℝ] F) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by
    congr 1
    exact extChartAt_to_inv x₀
  exact hh.trans ((congrArg (fun B : E →L[ℝ] F => B.comp (ContinuousLinearMap.id ℝ E)) hB).trans
    (ContinuousLinearMap.comp_id _))

theorem mfderiv_mlieBracket_of_related [CompleteSpace E]
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {V W : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {V' W' : F → F}
    (hV : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hW : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hV' : Differentiable ℝ V') (hW' : Differentiable ℝ W')
    (hrelV : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (V x) = V' (f x))
    (hrelW : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (W x) = W' (f x))
    (x₀ : M) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ (mlieBracket (𝓘(ℝ, E)) V W x₀) =
      lieBracket ℝ V' W' (f x₀) := by
  let φ := extChartAt (𝓘(ℝ, E)) x₀
  let fbar : E → F := f ∘ φ.symm
  have hinv : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ x₀) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) x₀)
  have hbar : ContDiffAt ℝ 2 fbar (φ x₀) :=
    (((hf x₀).comp_of_eq hinv (extChartAt_to_inv x₀)).contDiffAt).of_le (by simp)
  have htarget : φ.target ∈ 𝓝 (φ x₀) := by
    simpa only [φ, mfld_simps, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x₀
  have hrv : ∀ᶠ y in 𝓝 (φ x₀),
      fderiv ℝ fbar y (chartVectorField x₀ V y) = V' (fbar y) :=
    eventually_of_mem htarget fun y hy => chartVectorField_related hf hrelV x₀ hy
  have hrw : ∀ᶠ y in 𝓝 (φ x₀),
      fderiv ℝ fbar y (chartVectorField x₀ W y) = W' (fbar y) :=
    eventually_of_mem htarget fun y hy => chartVectorField_related hf hrelW x₀ hy
  have hb := fderiv_lieBracket_of_related hbar
    (differentiableAt_chartVectorField ((hV x₀).mdifferentiableAt (by simp)))
    (differentiableAt_chartVectorField ((hW x₀).mdifferentiableAt (by simp)))
    (hV' _) (hW' _) hrv hrw
  let B : E →L[ℝ] F := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀
  have hbr := mlieBracket_eq_chartBracket V W x₀
  have hbase := fderiv_chart_comp_base hf x₀
  have hvalue : fbar (φ x₀) = f x₀ := congrArg f (extChartAt_to_inv x₀)
  exact (congrArg B hbr).trans
    ((congrArg (fun L : E →L[ℝ] F =>
      L (lieBracket ℝ (chartVectorField x₀ V) (chartVectorField x₀ W) (φ x₀)))
        hbase.symm).trans (hb.trans (congrArg (lieBracket ℝ V' W') hvalue)))

end PolycyclicRecognition

end

end OAI
