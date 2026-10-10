import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedVectorFieldBracket

namespace OAI

/-! # Brackets of related vector fields on manifolds

Both source and target charts are local. This extends the vector-space
calculation only as far as needed to differentiate Lie-group homomorphisms.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

theorem chartVectorField_apply_chart
    (x₀ : M) (V : (x : M) → TangentSpace (𝓘(ℝ, E)) x)
    {x : M} (hx : x ∈ (extChartAt (𝓘(ℝ, E)) x₀).source) :
    chartVectorField x₀ V (extChartAt (𝓘(ℝ, E)) x₀ x) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀) x (V x) := by
  have h₁ := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := 𝓘(ℝ, E)) hx
  have h₂ := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓘(ℝ, E)) hx
  have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext z; simp
  rw [hrange, mfderivWithin_univ] at h₁ h₂
  have hinv := ContinuousLinearMap.inverse_eq h₂ h₁
  unfold chartVectorField mpullback
  exact (congrArg (fun D : E →L[ℝ] E =>
    D (V ((extChartAt (𝓘(ℝ, E)) x₀).symm (extChartAt (𝓘(ℝ, E)) x₀ x)))) hinv).trans
      (congrArg (fun z : M =>
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀) x) (V z : E))
        ((extChartAt (𝓘(ℝ, E)) x₀).left_inv hx))

theorem fderiv_double_chart
    {f : M → N} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt (𝓘(ℝ, E)) x₀).target)
    (hfy : f ((extChartAt (𝓘(ℝ, E)) x₀).symm y) ∈
      (extChartAt (𝓘(ℝ, F)) (f x₀)).source) :
    fderiv ℝ (extChartAt (𝓘(ℝ, F)) (f x₀) ∘ f ∘
        (extChartAt (𝓘(ℝ, E)) x₀).symm) y =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (extChartAt (𝓘(ℝ, F)) (f x₀))
        (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y))).comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y)) := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) x₀).symm y := by
    simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have ho : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F))
      (extChartAt (𝓘(ℝ, F)) (f x₀)) (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)) :=
    mdifferentiableAt_extChartAt (by simpa only [mfld_simps] using hfy)
  let D : E →L[ℝ] F :=
    (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (extChartAt (𝓘(ℝ, F)) (f x₀))
      (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)) : F →L[ℝ] F).comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f ((extChartAt (𝓘(ℝ, E)) x₀).symm y) :
        E →L[ℝ] F).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm y))
  have hd : HasFDerivAt (extChartAt (𝓘(ℝ, F)) (f x₀) ∘ f ∘
      (extChartAt (𝓘(ℝ, E)) x₀).symm) D y :=
    (ho.hasMFDerivAt.comp y
      (((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi.hasMFDerivAt)).hasFDerivAt
  exact hd.fderiv

theorem mfderiv_mlieBracket_of_manifold_related [CompleteSpace E] [CompleteSpace F]
    {f : M → N} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {V W : (x : M) → TangentSpace (𝓘(ℝ, E)) x}
    {V' W' : (y : N) → TangentSpace (𝓘(ℝ, F)) y}
    (hV : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hW : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hV' : ContMDiff (𝓘(ℝ, F)) ((𝓘(ℝ, F)).prod (𝓘(ℝ, F))) ∞
      (fun y => (⟨y, V' y⟩ : TangentBundle (𝓘(ℝ, F)) N)))
    (hW' : ContMDiff (𝓘(ℝ, F)) ((𝓘(ℝ, F)).prod (𝓘(ℝ, F))) ∞
      (fun y => (⟨y, W' y⟩ : TangentBundle (𝓘(ℝ, F)) N)))
    (hrelV : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (V x) = V' (f x))
    (hrelW : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (W x) = W' (f x))
    (x₀ : M) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ (mlieBracket (𝓘(ℝ, E)) V W x₀) =
      mlieBracket (𝓘(ℝ, F)) V' W' (f x₀) := by
  let φ := extChartAt (𝓘(ℝ, E)) x₀
  let ψ := extChartAt (𝓘(ℝ, F)) (f x₀)
  let fbar : E → F := ψ ∘ f ∘ φ.symm
  have hinv : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ x₀) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) x₀)
  have heq : (f ∘ φ.symm) (φ x₀) = f x₀ := congrArg f (extChartAt_to_inv x₀)
  have hbar : ContDiffAt ℝ 2 fbar (φ x₀) := by
    apply ContDiffAt.of_le (n := ∞) _ (by simp)
    exact ((contMDiffAt_extChartAt (I := 𝓘(ℝ, F))).comp_of_eq
      ((hf x₀).comp_of_eq hinv (extChartAt_to_inv x₀)) heq).contDiffAt
  have htarget : φ.target ∈ 𝓝 (φ x₀) := by
    simpa only [φ, mfld_simps, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x₀
  have hsource : ψ.source ∈ 𝓝 (f x₀) := extChartAt_source_mem_nhds (f x₀)
  have himage : ∀ᶠ y in 𝓝 (φ x₀), f (φ.symm y) ∈ ψ.source := by
    apply (hf.continuous.continuousAt.comp hinv.continuousAt).preimage_mem_nhds
    rw [heq]
    exact hsource
  have hrelated (A : (x : M) → TangentSpace (𝓘(ℝ, E)) x)
      (B : (y : N) → TangentSpace (𝓘(ℝ, F)) y)
      (hrel : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (A x) = B (f x)) :
      ∀ᶠ y in 𝓝 (φ x₀), fderiv ℝ fbar y (chartVectorField x₀ A y) =
        chartVectorField (f x₀) B (fbar y) := by
    filter_upwards [htarget, himage] with y hy hfy
    have hD : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y).IsInvertible := by
      simpa only [φ, mfld_simps, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hy
    rw [show fbar = ψ ∘ f ∘ φ.symm from rfl, fderiv_double_chart hf x₀ hy hfy]
    change (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm y)))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm y))
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y)
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y).inverse (A (φ.symm y))))) = _
    rw [hD.self_apply_inverse, hrel]
    exact (chartVectorField_apply_chart (f x₀) B hfy).symm
  have hvalue : fbar (φ x₀) = ψ (f x₀) := congrArg ψ heq
  have hb := fderiv_lieBracket_of_related hbar
    (differentiableAt_chartVectorField ((hV x₀).mdifferentiableAt (by simp)))
    (differentiableAt_chartVectorField ((hW x₀).mdifferentiableAt (by simp)))
    (by rw [hvalue]; exact
      differentiableAt_chartVectorField ((hV' (f x₀)).mdifferentiableAt (by simp)))
    (by rw [hvalue]; exact
      differentiableAt_chartVectorField ((hW' (f x₀)).mdifferentiableAt (by simp)))
    (hrelated V V' hrelV) (hrelated W W' hrelW)
  have hbase : fderiv ℝ fbar (φ x₀) = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by
    have hh := fderiv_double_chart hf x₀ (mem_extChartAt_target x₀)
      (by simpa only [extChartAt_to_inv] using mem_extChartAt_source (I := 𝓘(ℝ, F)) (f x₀))
    have hpoint : φ.symm (φ x₀) = x₀ := extChartAt_to_inv x₀
    have hB : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm (φ x₀)) : E →L[ℝ] F) =
        mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by congr 1
    have hT : (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm (φ x₀))) : F →L[ℝ] F) =
        ContinuousLinearMap.id ℝ F := by
      have hp : (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm (φ x₀))) : F →L[ℝ] F) =
          mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f x₀) := by congr 1
      exact hp.trans (mfderiv_extChartAt_self (I := 𝓘(ℝ, F)))
    change fderiv ℝ fbar (φ x₀) =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm (φ x₀)))).comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm (φ x₀))).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm (φ x₀))) at hh
    rw [hT, hB, mfderiv_chart_symm_base] at hh
    change fderiv ℝ fbar (φ x₀) = (ContinuousLinearMap.id ℝ F).comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ : E →L[ℝ] F).comp
        (ContinuousLinearMap.id ℝ E)) at hh
    exact hh.trans (ContinuousLinearMap.ext fun _ => rfl)
  rw [hbase] at hb
  rw [mlieBracket_eq_chartBracket V W x₀, mlieBracket_eq_chartBracket V' W' (f x₀)]
  exact hb.trans (congrArg (lieBracket ℝ (chartVectorField (f x₀) V')
    (chartVectorField (f x₀) W')) (congrArg ψ heq))

end PolycyclicRecognition

end

end OAI
