import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ShortForward
import OAI.Analysis.BiholderTransport.Convexity.ParametricShortLowerEnvelope
import OAI.Analysis.BiholderTransport.Contact.CoordinateScalarSupport

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma coordinateScalarSupport_hasFDerivAt {a : M} {b p : Model n}
    {v s l : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : HasDerivAt φ l v) :
    HasFDerivAt (fun w => coordinateScalarSupport a φ (((v,s),(b,p)),w))
      (l • riemannianCoordinateMetric a b p) b := by
  let L := riemannianCoordinateMetric a b p
  have hi := riemannianCoordinateMetric_isInvertible hb
  have hgrad : chartGradientVector a b (s • L)=
      s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p := by
    simp only [chartGradientVector,map_smul,L,hi.inverse_apply_self]
  have he : coordinateBackward a (-1,b,s • L)=movingNormal a (b,s • p) := by
    simp only [coordinateBackward,neg_neg,one_smul,map_smul,L,hi.inverse_apply_self]
  have hC := chartCost_gradient_at_contact hb (hgrad.symm ▸ hp)
  rw [he] at hC
  let c := chartCost (n := n) a (movingNormal a (b,s • p))
  let f := fun w => v+c b/s+(-s⁻¹)*c w
  have hf : HasFDerivAt f L b := by
    apply ((hC.const_mul (-s⁻¹)).const_add (v+c b/s)).congr_fderiv
    ext d
    simp only [_root_.smul_apply,smul_eq_mul,neg_apply]
    field_simp
  have hf0 : f b=v := by dsimp only [f]; ring
  have h : HasDerivAt φ l (f b) := hf0.symm ▸ hφ
  have H := h.comp_hasFDerivAt b hf
  have heq : (fun w => coordinateScalarSupport a φ (((v,s),(b,p)),w))=
      fun w => φ (f w) := by
    funext w
    dsimp only [coordinateScalarSupport,f,c,chartCost]
    congr 1
    ring
  rw [heq]
  exact H

omit [Nonempty M] in
lemma coordinateScalarSupport_shortForward {a : M} {b p : Model n}
    {v s l t : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : HasDerivAt φ l v) :
    shortForward a (fun w => coordinateScalarSupport a φ (((v,s),(b,p)),w)) (t,b)=
      extChartAt 𝓘(ℝ,Model n) a (movingNormal a (b,(t*l) • p)) := by
  rw [shortForward,(coordinateScalarSupport_hasFDerivAt hb hs hp hφ).fderiv]
  simp only [coordinateBackward,neg_neg,map_smul,
    (riemannianCoordinateMetric_isInvertible hb).inverse_apply_self,smul_smul,one_mul]

end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.exists_actual_center_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hmono : Monotone φ)
    {a : M} {b : Model n} (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {l τ : ℝ} (hφ : HasDerivAt φ l (v ((extChartAt 𝓘(ℝ,Model n) a).symm b)))
    (hl : 0<l) (hl1 : l<1) (hτ : τ≠0)
    {r : TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)}
    (hr : τ • r∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hmin : IsLocalMin (fun y => φ (v y)+
      cost y (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (τ • r))/τ)
        ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ∃ p : Model n,
      let y := (extChartAt 𝓘(ℝ,Model n) a).symm b
      let s := (1+l)/2
      let ψ := fun w => coordinateScalarSupport a φ ((((v y),s),(b,p)),w)
      0<s ∧ s<1 ∧
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ y p=
        l⁻¹ • r ∧
      l⁻¹ • r∈minimizingVectors y ∧
      contactGap v u y (movingNormal a (b,p))=0 ∧
      (∀ w,ψ w≤φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm w))) ∧
      ψ b=φ (v y) ∧
      shortForward a ψ (τ,b)=extChartAt 𝓘(ℝ,Model n) a (riemannianExp y (τ • r)) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let y := χ.symm b
  let T := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let p := T.continuousLinearMapAt ℝ y (l⁻¹ • r)
  have hy : y∈(chartAt (Model n) a).source := by
    simpa only [y,χ,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  have hp : T.symmL ℝ y p=l⁻¹ • r := Trivialization.symmL_continuousLinearMapAt _ hy _
  obtain ⟨hpm,hpc,hrreg⟩ := hmtw.modified_short_contact hu hv hdual hφ hl hl1 hτ hr hmin
  have hs : 0<(1+l)/2 := by linarith
  have hs1 : (1+l)/2<1 := by linarith
  have hpr : ((1+l)/2) • T.symmL ℝ y p∈injectivityDomain y := by
    rw [hp]
    exact contracted_minimizer_mem_injectivityDomain hpm hs hs1
  refine ⟨p,hs,hs1,hp,hpm,?_,?_,?_,?_⟩
  · rw [movingNormal_eq hb]
    change contactGap v u y (riemannianExp y (T.symmL ℝ y p))=0
    rw [hp]
    exact hpc
  · intro w
    dsimp only
    rw [coordinateScalarSupport_eq hb]
    change scalarCostSupport φ (v y) y (T.symmL ℝ y p) ((1+l)/2) (χ.symm w)≤φ (v (χ.symm w))
    rw [hp]
    exact scalarCostSupport_lower hu hdual hmono hpm hpc hs hs1 _
  · exact coordinateScalarSupport_self _ _ _ _ _ _
  · rw [coordinateScalarSupport_shortForward hb hs.ne' hpr hφ,movingNormal_eq hb,map_smul,hp,
      smul_smul]
    have he : τ*l*l⁻¹=τ := by field_simp
    rw [he]

end WeakMTWTransport

end

end OAI
