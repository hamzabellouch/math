import OAI.Geometry.SurfaceImmersion.Geometry.NormalFrameTransport

namespace OAI

/-! Smooth transport and exact exterior pasting produce a genuine formal
differential for the original Euclidean surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma transportedNormalFrame_smoothOn {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : FrameTarget) {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {B : Base → Base →L[ℝ] FrameTarget} (hB : ContDiff ℝ ∞ B)
    {V : Set Base} (hV : V ⊆ normalFrameDomain φ a) :
    ContDiffOn ℝ ∞ (transportedNormalFrame φ a d B) V := by
  have hu := transverseDerivative_smooth hφ
  have hcross : ContDiff ℝ ∞ (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  have hframe : ContDiff ℝ ∞ (fun x => curveNormalLinear (transverseDerivative φ x) a) :=
    ((contDiff_const.smulRight hu).add contDiff_const).add (contDiff_const.smulRight hcross)
  have hc : ContDiffOn ℝ ∞ (longitudinalCoefficient φ a) V := by
    intro x hx
    have hi := (curveNormalLinear_invertible (normalFrameDomain_nonzero (hV hx))
      (normalFrameDomain_transverse (hV hx))).contDiffAt_map_inverse.comp x hframe.contDiffAt
    exact (hi.clm_apply ((coordinateDifferential_smooth hφ).clm_apply contDiff_const).contDiffAt).snd.contDiffWithinAt
  exact hframe.contDiffOn.clm_comp
    (((normalOutput_smooth.comp (hd.comp (contDiff_apply ℝ ℝ 1))).contDiffOn).clm_comp
      (hB.contDiffOn.clm_comp (longitudinalShear_smooth.comp_contDiffOn hc)))

theorem actual_relative_frame {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    (a : FrameTarget) {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {V : Set Base} (hV : IsOpen V) (hVF : V ⊆ normalFrameDomain φ a)
    (hdn : ∀ x ∈ V, d (x 1) ≠ 0) {G : Base → Base}
    (hG : EqOn G (axisNormalizedDefect d (normalDefect φ a)) V)
    (hfill : HasRelativeDefectFilling G V) :
    ∃ (A : Base → Base →L[ℝ] ProjectionTarget 3) (K : Set Base),
      ContDiff ℝ ∞ A ∧ IsCompact K ∧ K ⊆ V ∧
      tsupport (A-fderiv ℝ φ) ⊆ K ∧ (∀ x ∈ V, Function.Injective (A x)) := by
  obtain ⟨B,K,hB,hK,hKV,hBI,hBe⟩ := hfill
  let C := transportedNormalFrame φ a d B
  have hC : ContDiffOn ℝ ∞ C V := transportedNormalFrame_smoothOn hφ a hd hB hVF
  have hCI : ∀ x ∈ V, Function.Injective (C x) := by
    intro x hx
    exact transportedNormalFrame_injective (normalFrameDomain_nonzero (hVF hx))
      (normalFrameDomain_transverse (hVF hx)) (hdn x hx) (hBI x hx)
  have hCe : ∀ x ∈ V, x ∉ K → C x = coordinateDifferential φ x := by
    intro x hx hxK
    have hb : B x = defectFrame (axisNormalizedDefect d (normalDefect φ a)) x := by
      rw [hBe x hxK]
      unfold defectFrame
      rw [hG hx]
    change (curveNormalLinear (transverseDerivative φ x) a).comp
      ((normalOutput (d (x 1))).comp ((B x).comp (longitudinalShear (longitudinalCoefficient φ a x)))) = _
    rw [hb]
    exact transportedNormalFrame_exact φ a d x (normalFrameDomain_nonzero (hVF hx))
      (normalFrameDomain_transverse (hVF hx)) (hdn x hx)
  obtain ⟨D,hD,hDs,hDC,hDe⟩ := compact_relative_field (coordinateDifferential_smooth hφ)
    hV hC hK hKV hCe
  let E := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
  let A := fun x => E.comp (D x)
  have hA : ContDiff ℝ ∞ A := contDiff_const.clm_comp hD
  have hAe : ∀ x ∉ K, A x = fderiv ℝ φ x := by
    intro x hx
    dsimp [A,E]
    rw [hDe x hx]
    ext v
    simp [coordinateDifferential]
  refine ⟨A,K,hA,hK,hKV,?_,?_⟩
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp only [Pi.sub_apply,hAe x hxK,sub_self])
  · intro x hx
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.injective.comp
    rw [hDC hx]
    exact hCI x hx

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
