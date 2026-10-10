import Mathlib
import OAI.Geometry.CubicTorus.Curvature.TorusC2CMCAt

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_metric {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v w : Plane) :
    ⟪fderiv ℝ (normalGraph n g) y v,fderiv ℝ (normalGraph n g) y w⟫=
      ⟪v,w⟫+⟪gradient g y,v⟫*⟪gradient g y,w⟫ := by
  rw [normalGraph_fderiv_apply hg,normalGraph_fderiv_apply hg]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow,mul_zero,add_zero]
  have ho : ⟪normalPlaneEmbedding n v,n⟫=0 := by rw [real_inner_comm]; exact normalPlaneEmbedding_inner hn v
  have hi := (normalPlaneLinearIsometry n).inner_map_map v w
  change ⟪normalPlaneEmbedding n v,normalPlaneEmbedding n w⟫=⟪v,w⟫ at hi
  simp only [hi,ho,mul_zero,zero_add,mul_one]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_projection_differential {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    (normalPlaneCoordinates n).comp (fderiv ℝ (normalGraph n g) y)=
      ContinuousLinearMap.id ℝ Plane := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply,normalGraph_fderiv_apply hg,map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]
  rfl

lemma graphUnitNormalExtension_fderiv (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    fderiv ℝ (graphUnitNormalExtension a n g) x=
      -((fderiv ℝ (normalGraph n g) (normalPlaneCoordinates n (x-a))).comp
        ((graphShapeOperator g (normalPlaneCoordinates n (x-a))).comp
          (normalPlaneCoordinates n))) := by
  have hN : Differentiable ℝ (fun y ↦ graphSlopeNormal n (gradient g y)) :=
    ((graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)).differentiable (by simp)
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a)
  have hd := ((hN _).hasFDerivAt.comp x hp).fderiv
  change fderiv ℝ (graphUnitNormalExtension a n g) x=_ at hd
  rw [hd]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,neg_apply]
  exact graph_weingarten hn hg _ _

theorem graphUnitNormalExtension_curvature (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    coverTrace ((fderiv ℝ (graphUnitNormalExtension a n g) x).comp
      (fderiv ℝ (graphUnitNormalExtension a n g) x))=
        graphSquaredSecondFundamentalForm g (normalPlaneCoordinates n (x-a)) := by
  let y := normalPlaneCoordinates n (x-a)
  let J := fderiv ℝ (normalGraph n g) y
  let S := graphShapeOperator g y
  let P := normalPlaneCoordinates n
  have hPJ : P.comp J=ContinuousLinearMap.id ℝ Plane := normalGraph_projection_differential hn hg y
  rw [graphUnitNormalExtension_fderiv a hn hg]
  change coverTrace ((-(J.comp (S.comp P))).comp (-(J.comp (S.comp P))))=planeTraceSquare S
  have he : ((-(J.comp (S.comp P))).comp (-(J.comp (S.comp P))))=
      J.comp ((S.comp S).comp P) := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L : Plane →L[ℝ] Plane ↦ L (S (P v))) hPJ
    simp only [ContinuousLinearMap.comp_apply,neg_apply,map_neg,neg_neg,
      ContinuousLinearMap.id_apply] at h ⊢
    rw [h]
  rw [he,rectangular_trace,ContinuousLinearMap.comp_assoc,hPJ,
    ContinuousLinearMap.comp_id,planeTrace_square]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_eq_trace (F : Plane → Plane) (y : Plane) :
    planeDivergence F y=planeTrace (fderiv ℝ F y) := by
  simp only [planeDivergence,planeTrace,Fin.sum_univ_two]

lemma cmcFlux_gradient_fderiv {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    fderiv ℝ (fun z ↦ cmcFlux (gradient g z)) y=graphShapeOperator g y := by
  exact ((cmcFlux_hasFDerivAt (gradient g y)).comp y
    (((plane_gradient_contDiff hg).differentiable (by simp) y).hasFDerivAt)).fderiv

theorem graphUnitNormalExtension_divergence (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Cover) :
    divergence (graphUnitNormalExtension a n g) x=
      -planeDivergence (fun z ↦ cmcFlux (gradient g z))
        (normalPlaneCoordinates n (x-a)) := by
  rw [divergence_eq_coverTrace,graphUnitNormalExtension_fderiv a hn hg]
  have hneg (L : Cover →L[ℝ] Cover) : coverTrace (-L)= -coverTrace L := by
    simp [coverTrace,Finset.sum_neg_distrib]
  rw [hneg,rectangular_trace,ContinuousLinearMap.comp_assoc,
    normalGraph_projection_differential hn hg,ContinuousLinearMap.comp_id,
    planeDivergence_eq_trace,cmcFlux_gradient_fderiv hg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTrace_comp_comm (A B : Plane →L[ℝ] Plane) :
    planeTrace (A.comp B)=planeTrace (B.comp A) := by
  simp only [planeTrace,Fin.sum_univ_two,ContinuousLinearMap.comp_apply]
  rw [plane_decompose (B (EuclideanSpace.single 0 1)),
    plane_decompose (B (EuclideanSpace.single 1 1)),
    plane_decompose (A (EuclideanSpace.single 0 1)),
    plane_decompose (A (EuclideanSpace.single 1 1))]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma planeTraceSquare_comp_comm (A B : Plane →L[ℝ] Plane) :
    planeTraceSquare (A.comp B)=planeTraceSquare (B.comp A) := by
  rw [← planeTrace_square,← planeTrace_square]
  calc
    _ = planeTrace (A.comp ((B.comp A).comp B)) := by
      congr 1
    _ = planeTrace (((B.comp A).comp B).comp A) := planeTrace_comp_comm _ _
    _ = _ := by congr 1

lemma planeTraceSquare_symmetric {L : Plane →L[ℝ] Plane}
    (hL : ∀ v w : Plane,⟪L v,w⟫=⟪v,L w⟫) :
    0≤planeTraceSquare L ∧ (planeTrace L)^2≤2*planeTraceSquare L := by
  have hc : L (EuclideanSpace.single 0 1) 1=L (EuclideanSpace.single 1 1) 0 := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hL (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  simp only [planeTraceSquare,planeTrace,Fin.sum_univ_two,hc]
  constructor
  · nlinarith [sq_nonneg (L (EuclideanSpace.single 0 1) 0),
      sq_nonneg (L (EuclideanSpace.single 1 1) 0),sq_nonneg (L (EuclideanSpace.single 1 1) 1)]
  · nlinarith [sq_nonneg (L (EuclideanSpace.single 0 1) 0-L (EuclideanSpace.single 1 1) 1),
      sq_nonneg (L (EuclideanSpace.single 1 1) 0)]

theorem graph_curvature_nonnegative {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    0≤graphSquaredSecondFundamentalForm g y ∧
      (planeDivergence (fun z ↦ cmcFlux (gradient g z)) y)^2≤
        2*graphSquaredSecondFundamentalForm g y := by
  let p := gradient g y
  let L := fderiv ℝ (gradient g) y
  let C := cmcCompress p
  let D := (cmcWeight p)⁻¹ • (C.comp L)
  have hS : graphShapeOperator g y=C.comp D := by
    apply ContinuousLinearMap.ext
    intro v
    change cmcJacobian p (L v)=C (D v)
    change cmcJacobian p (L v)=C ((cmcWeight p)⁻¹ • C (L v))
    rw [map_smul]
    exact cmcJacobian_compress p (L v)
  have hB : ∀ v w : Plane,⟪(D.comp C) v,w⟫=⟪v,(D.comp C) w⟫ := by
    intro v w
    change ⟪(cmcWeight p)⁻¹ • C (L (C v)),w⟫=
      ⟪v,(cmcWeight p)⁻¹ • C (L (C w))⟫
    rw [real_inner_smul_left,real_inner_smul_right]
    congr 1
    rw [cmcCompress_symm,plane_hessian_symmetric hg,
      ← cmcCompress_symm]
  have hh := planeTraceSquare_symmetric hB
  unfold graphSquaredSecondFundamentalForm
  rw [hS,planeTraceSquare_comp_comm]
  refine ⟨hh.1,?_⟩
  rw [planeDivergence_eq_trace,cmcFlux_gradient_fderiv hg,hS,planeTrace_comp_comm]
  exact hh.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTraceSquare_symmetric_eq_zero {L : Plane →L[ℝ] Plane}
    (hL : ∀ v w : Plane,⟪L v,w⟫=⟪v,L w⟫) (hz : planeTraceSquare L=0) : L=0 := by
  have hc : L (EuclideanSpace.single 0 1) 1=L (EuclideanSpace.single 1 1) 0 := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hL (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  simp only [planeTraceSquare,hc] at hz
  have h00 : L (EuclideanSpace.single 0 1) 0=0 := by nlinarith [sq_nonneg (L (EuclideanSpace.single 1 1) 0),sq_nonneg (L (EuclideanSpace.single 1 1) 1)]
  have h10 : L (EuclideanSpace.single 1 1) 0=0 := by nlinarith [sq_nonneg (L (EuclideanSpace.single 0 1) 0),sq_nonneg (L (EuclideanSpace.single 1 1) 1)]
  have h11 : L (EuclideanSpace.single 1 1) 1=0 := by nlinarith [sq_nonneg (L (EuclideanSpace.single 0 1) 0),sq_nonneg (L (EuclideanSpace.single 1 1) 0)]
  apply ContinuousLinearMap.ext
  intro v
  rw [plane_decompose v,map_add,map_smul,map_smul]
  ext i
  fin_cases i <;> simp [h00,h10,h11,hc]

theorem graph_curvature_zero_fderiv_gradient {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    (hz : graphSquaredSecondFundamentalForm g y=0) :
    fderiv ℝ (gradient g) y=0 := by
  let p := gradient g y
  let L := fderiv ℝ (gradient g) y
  let C := cmcCompress p
  let D := (cmcWeight p)⁻¹ • (C.comp L)
  have hS : graphShapeOperator g y=C.comp D := by
    apply ContinuousLinearMap.ext
    intro v
    change cmcJacobian p (L v)=C ((cmcWeight p)⁻¹ • C (L v))
    rw [map_smul]
    exact cmcJacobian_compress p (L v)
  have hB : ∀ v w : Plane,⟪(D.comp C) v,w⟫=⟪v,(D.comp C) w⟫ := by
    intro v w
    change ⟪(cmcWeight p)⁻¹ • C (L (C v)),w⟫=⟪v,(cmcWeight p)⁻¹ • C (L (C w))⟫
    rw [real_inner_smul_left,real_inner_smul_right]
    congr 1
    rw [cmcCompress_symm,plane_hessian_symmetric hg,← cmcCompress_symm]
  have hzB : D.comp C=0 := by
    apply planeTraceSquare_symmetric_eq_zero hB
    change planeTraceSquare (graphShapeOperator g y)=0 at hz
    rwa [hS,planeTraceSquare_comp_comm] at hz
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : Plane →L[ℝ] Plane ↦ A (cmcStretch p v)) hzB
  change (cmcWeight p)⁻¹ • cmcCompress p (L (cmcCompress p (cmcStretch p v)))=0 at hv
  rw [cmcCompress_stretch] at hv
  have hv' : cmcCompress p (L v)=0 := (smul_eq_zero.mp hv).resolve_left (inv_ne_zero (cmcWeight_pos p).ne')
  have hh := congrArg (cmcStretch p) hv'
  simpa only [cmcStretch_compress,map_zero,zero_apply] using hh

theorem graph_curvature_zero_affine {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r : ℝ} (hr : 0<r)
    (hz : ∀ y∈Metric.ball (0 : Plane) r,graphSquaredSecondFundamentalForm g y=0) :
    ∀ y∈Metric.ball (0 : Plane) r,g y=g 0+⟪gradient g 0,y⟫ := by
  have h0 : (0 : Plane)∈Metric.ball (0 : Plane) r := Metric.mem_ball_self hr
  have hd := (plane_gradient_contDiff hg).differentiable (by simp)
  have hgrad (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : gradient g y=gradient g 0 := by
    apply (convex_ball (0 : Plane) r).is_const_of_fderivWithin_eq_zero hd.differentiableOn _ hy h0
    intro z hz'
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hz']
    exact graph_curvature_zero_fderiv_gradient hg z (hz z hz')
  let F : Plane → ℝ := fun y ↦ g 0+⟪gradient g 0,y⟫
  have hF : Differentiable ℝ F := fun _ ↦ ((innerSL ℝ (gradient g 0)).hasFDerivAt.const_add (g 0)).differentiableAt
  refine Metric.isOpen_ball.eqOn_of_fderiv_eq (convex_ball (0 : Plane) r).isPreconnected
    (hg.differentiable (by simp)).differentiableOn hF.differentiableOn ?_ h0 ?_
  · intro z hz'
    change fderiv ℝ g z=fderiv ℝ (fun y ↦ g 0+(innerSL ℝ (gradient g 0)) y) z
    rw [((innerSL ℝ (gradient g 0)).hasFDerivAt.const_add (g 0)).fderiv]
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ g z v=⟪gradient g 0,v⟫
    rw [← inner_gradient_left,hgrad z hz']
  · simp only [inner_zero_right,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_graph_normal_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
      (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1})
      (_hb : ∀ x,‖F x‖≤1) := normalCoverMeasure_local_flux hE hμ hF hs hO
  have h := cutoff_graph_patch_normal_ae (hE.preimage measurable_quotientMap) a hn hg hc
    hgraph (normalMeasure_cutoff_saturation hμ _) hflux hφ hsφ hφU hφO hφR hφb
  have hO : MeasurableSet {z : BlowupNormalBundle | ∀ i,0<z.1 i ∧ z.1 i<1} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun z : BlowupNormalBundle ↦ z.1 i) := by fun_prop
    exact (measurableSet_lt measurable_const hm).inter
      (measurableSet_lt hm measurable_const)
  have h' : ∀ᵐ z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle),
      0<φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
    have hh := (ae_restrict_iff' hO).mp h
    filter_upwards [hh] with z hz hpos
    exact hz (hφO (subset_tsupport _ (show φ z.1≠0 from hpos.ne'))) hpos
  have hm : (normalCoverMeasure μ : Measure BlowupNormalBundle)=
      Measure.map normalCoverMap (μ : Measure NormalBundle) := FiniteMeasure.toMeasure_map μ normalCoverMap
  rw [hm] at h'
  exact ae_of_ae_map continuous_normalCoverMap.measurable.aemeasurable h'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def translateNormal (a : Cover) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (quotientMap z.1-quotientMap a),z.2)

lemma measurable_translateNormal (a : Cover) : Measurable (translateNormal a) := by
  exact (measurable_cubeRepresentative.comp ((measurable_quotientMap.comp
    (measurable_subtype_coe.comp measurable_fst)).sub measurable_const)).prodMk measurable_snd

lemma translateNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (a : Cover) (z : NormalBundle) :
    F (translateNormal a z).1=F ((z.1 : Cover)-a) := by
  change F (representative (quotientMap z.1-quotientMap a))=F ((z.1 : Cover)-a)
  rw [← quotientMap_sub]
  exact periodic_representative hp _

theorem isNormalMeasure_translation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (a : Cover) :
    IsNormalMeasure ((fun z ↦ z+quotientMap a) ⁻¹' E) (μ.map (translateNormal a)) := by
  constructor
  · have hm : ((μ.map (translateNormal a)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_translateNormal a)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_translation_measurable hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (translateNormal a) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_translateNormal a).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_translation hF a hE]
    have hG : AdmissibleField (fun x ↦ F (x-a)) := by
      simpa only [sub_eq_add_neg] using admissible_translate hF (-a)
    rw [← hμ.2 _ hG]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪(z.2 : Cover),F (translateNormal a z).1⟫=⟪(z.2 : Cover),F ((z.1 : Cover)-a)⟫
      rw [translateNormal_periodic_eval hF.2.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcGraphJacobi (g φ ψ : Plane → ℝ) : ℝ :=
  graphJacobiForm (fun y ↦ cmcJacobian (gradient g y))
    (fun y ↦ cmcWeight (gradient g y)) φ ψ

lemma cmcGraphJacobi_div_transform {g f ψ : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    cmcGraphJacobi g (fun y ↦ f y/cmcWeight (gradient g y)) ψ=
      ∫ y,⟪gradient f y,cmcJacobian (gradient g y)
        (gradient (fun z ↦ cmcWeight (gradient g z)*ψ z) y)⟫ := by
  have hp := plane_gradient_contDiff hg
  have hq := cmcWeight_contDiff.comp hp
  have he (y : Plane) : cmcWeight (gradient g y)*(f y/cmcWeight (gradient g y))=f y := by
    exact mul_div_cancel₀ _ (cmcWeight_pos _).ne'
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (gradient g y)) :=
    cmcJacobian_contDiff.comp hp
  have hq' : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcWeight (gradient g y)) := hq
  have hquot : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f y/cmcWeight (gradient g y)) :=
    hf.div hq (fun y ↦ (cmcWeight_pos _).ne')
  have ht := graphJacobiForm_transform hA
    (fun y v w ↦ (cmcJacobian_symmetric (gradient g y) v w).trans (real_inner_comm _ _)) hq'
    hquot hψ hc
  have hefun : (fun z ↦ cmcWeight (gradient g z)*(f z/cmcWeight (gradient g z)))=f := funext he
  rw [hefun] at ht
  exact ht

theorem LinearCMCEquation.normal_jacobi {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆U) :
    cmcGraphJacobi g (fun y ↦ f y/cmcWeight (gradient g y)) ψ=0 := by
  rw [cmcGraphJacobi_div_transform hg hf hψ hc]
  have hq := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  have hh := hw (fun y ↦ cmcWeight (gradient g y)*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  simp only [sub_zero,← inner_gradient_left] at hh
  convert hh using 1
  congr 1
  funext y
  rw [cmcJacobian_symmetric,real_inner_comm]

theorem cmcGraphJacobi_vertical {g ψ : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    cmcGraphJacobi g (fun y ↦ 1/cmcWeight (gradient g y)) ψ=0 := by
  rw [cmcGraphJacobi_div_transform hg contDiff_const hψ hc]
  simp [gradient]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_graph_extension {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨fun y ↦ b y*g y,?_,?_⟩
  · exact contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  · intro y hy
    change b y*g y=g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

theorem WeakCMCGraph.coordinate_jacobi_chart {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (f : Plane → ℝ) (r : ℝ),0<r ∧ r≤R ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      EqOn f g (Metric.ball 0 r) ∧
      (∀ i : Fin 2,LinearCMCEquation (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))
        (gradient f) (fun _ ↦ 0) (Metric.ball 0 r)) ∧
      ∀ i : Fin 2,∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 r →
        cmcGraphJacobi f (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1)/
          cmcWeight (gradient f y)) ψ=0 := by
  obtain ⟨f,hfc,hfe⟩ := smooth_graph_extension hR hgc
  have he : f=ᶠ[𝓝 0]g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : Plane)∈Metric.ball 0 (R/2) by simp; linarith)] with y hy
    exact hfe hy
  have hgc0 : ContDiffAt ℝ (⊤ : ℕ∞) g 0 := hgc.contDiffAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  have hnear (i : Fin 2) : LinearCMCEquationNear
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f) (fun _ ↦ 0) := by
    have hh := hw.directional_linear_near hg hK hR (hgc.of_le (by simp))
      (ContDiffAt.holderJet (n := 2) (hgc0.of_le (by
        change ((3 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)))
      (EuclideanSpace.single i 1) (by simp)
    apply hh.congr
    · exact (he.fderiv (𝕜 := ℝ)).mono fun _ hy ↦ congrArg (fun L : Plane →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hy
    · exact (he.fderiv (𝕜 := ℝ)).mono fun _ hy ↦ by simp only [gradient,hy]
    · exact EventuallyEq.rfl
  obtain ⟨r0,hr0,h0⟩ := hnear 0
  obtain ⟨r1,hr1,h1⟩ := hnear 1
  let r := min (R/2) (min r0 r1)
  have hr : 0<r := lt_min (by linarith) (lt_min hr0 hr1)
  have hrR : r≤R/2 := min_le_left _ _
  have hlin (i : Fin 2) : LinearCMCEquation (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i 1))
      (gradient f) (fun _ ↦ 0) (Metric.ball 0 r) := by
    fin_cases i
    · exact h0.mono (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))
    · exact h1.mono (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨f,r,hr,by linarith,hfc,hfe.mono (Metric.ball_subset_ball hrR),hlin,?_⟩
  intro i ψ hψ hc hs
  exact (hlin i).normal_jacobi hfc
    ((hfc.fderiv_right (by simp)).clm_apply contDiff_const) hψ hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_normal_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ (χ : Cover → ℝ) (N : Cover → Cover),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,χ (x+latticeVector m)=χ x) ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ x,0≤χ x) ∧ (∀ᶠ x in 𝓝 cubeCenter,χ x=1) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<χ z.1 → N z.1=(z.2 : Cover) := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,_,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,hf,hfg⟩ := smooth_graph_extension hr hgc
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x ((Metric.ball_subset_ball (by linarith)) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (by linarith : 0<r/2)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hdc (y : Plane) (hy : y∈Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hgC y hy).continuousAt_fderiv (by norm_num)
  have hNfg (x : Cover) (hx : x∈tsupport φ) :
      graphUnitNormalExtension cubeCenter n f x=graphUnitNormalExtension cubeCenter n g x := by
    have hp : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right]
      have hnorm : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR (hφU hx)
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt (hnorm.trans hRr)
    have he : f=ᶠ[𝓝 (normalPlaneCoordinates n (x-cubeCenter))]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hp] with y hy
      exact hfg hy
    simp only [graphUnitNormalExtension,gradient,he.fderiv_eq]
  have hsign : ∃ N0 : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N0 ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 → N0 z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hp : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨graphUnitNormalExtension cubeCenter n f,graphUnitNormalExtension_contDiff _ hn hf,?_⟩
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hp
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hp : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hp' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hp
      have hh := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hp' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh
      refine ⟨fun x ↦ -graphUnitNormalExtension cubeCenter n f x,
        (graphUnitNormalExtension_contDiff _ hn hf).neg,?_⟩
      filter_upwards [hm] with z hz hpos
      rw [hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨N0,hN0,hNae⟩ := hsign
  let ψ := radialHeightCutoff cubeCenter (ρ/4)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := radialDensityWeight_contDiff _ _ _
  have hsψ : HasCompactSupport ψ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hψs : tsupport ψ⊆Metric.closedBall cubeCenter (ρ/2) := by
    have hh := radialDensityWeight_tsupport (a := cubeCenter)
      (by positivity : 0≤2*(ρ/4)) (by positivity : 0<3*(ρ/4)^2)
    convert hh using 1
    congr 1
    ring_nf
  have hψφ (x : Cover) (hx : x∈tsupport ψ) : φ x=1 :=
    radialHeightCutoff_one hρ ((Metric.closedBall_subset_closedBall (by linarith)) (hψs hx))
  have hψO : tsupport ψ⊆{x | ∀ i,0<x i ∧ x i<1} :=
    hψs.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans (hρU.trans hUO))
  let F : Cover → Cover := fun x ↦ φ x • N0 x
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul hN0
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  refine ⟨latticePeriodize ψ,latticePeriodize F,latticePeriodize_contDiff hψ hsψ,
    latticePeriodize_contDiff hF hsF,latticePeriodize_periodic ψ,latticePeriodize_periodic F,?_,?_,?_⟩
  · intro x
    apply tsum_nonneg
    intro m
    exact radialDensityWeight_nonneg _ _ _ _
  · have he := latticePeriodize_eventuallyEq hsψ hψO
      (show ∀ i,0≤cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
    filter_upwards [he,Metric.ball_mem_nhds cubeCenter (by positivity : 0<ρ/4)] with x hx hb
    rw [hx]
    exact radialHeightCutoff_one (by positivity) (Metric.ball_subset_closedBall hb)
  · filter_upwards [hNae] with z hz hpos
    have he := (latticePeriodize_eventuallyEq hsψ hψO (compactCell_coordinates z.1)).eq_of_nhds
    rw [he] at hpos
    have hone := hψφ _ (subset_tsupport _ hpos.ne')
    rw [(latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • N0 z.1=(z.2 : Cover)
    rw [hone,one_smul]
    exact hz (by rw [hone]; norm_num)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cofactorOperator : (Cover →L[ℝ] Cover) →L[ℝ] (Cover →L[ℝ] Cover) :=
  ({toFun := fun L ↦ coverTrace L • ContinuousLinearMap.id ℝ Cover-L.adjoint,
    map_add' := by intro L M; simp only [coverTrace_add,map_add]; module,
    map_smul' := by intro a L; simp only [coverTrace_smul,map_smul,RingHom.id_apply]; module} :
      (Cover →L[ℝ] Cover) →ₗ[ℝ] (Cover →L[ℝ] Cover)).toContinuousLinearMap

@[simp] lemma cofactorOperator_apply (L : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorOperator L n=cofactorLinear L n := rfl

lemma cofactorLinear_smul (c : ℝ) (L : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorLinear (c • L) n=c • cofactorLinear L n := by
  change cofactorOperator (c • L) n=c • cofactorOperator L n
  rw [map_smul]
  rfl

lemma cofactorLinear_inner (L : Cover →L[ℝ] Cover) {n : Cover} (hn : ‖n‖=1) :
    ⟪n,cofactorLinear L n⟫=coverTrace L-⟪n,L n⟫ := by
  simp only [cofactorLinear,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one,ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

lemma cofactorQuadratic_smulRight (l : Cover →L[ℝ] ℝ) (v n : Cover) :
    cofactorQuadratic (l.smulRight v) n=0 := by
  have hc : (l.smulRight v).comp (l.smulRight v)=l v • l.smulRight v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      map_smul,smul_apply]
    module
  have ha : (l.smulRight v).adjoint ((l.smulRight v).adjoint n)=
      l v • (l.smulRight v).adjoint n := by
    have hh := congrArg (fun L : Cover →L[ℝ] Cover ↦ L.adjoint n) hc
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
      map_smul,starRingEnd_apply,star_trivial,smul_apply] using hh
  simp only [cofactorQuadratic,hc,coverTrace_smulRight,coverTrace_smul,ha]
  module

lemma cofactorLinear_coordinate {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point)
    (i : Fin 3) (n : Cover) :
    cofactorLinear (fderiv ℝ (fun y ↦ f y • EuclideanSpace.single i 1) point) n=
      coordinateNormalVelocity i f point n := by
  rw [fderiv_smul_const hf]
  have ha : ((fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ))).adjoint n=
      ⟪n,EuclideanSpace.single i 1⟫ • gradient f point := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.smulRight_apply,
      real_inner_smul_right,real_inner_smul_left,inner_gradient_left]
    ring
  simp only [cofactorLinear,coverTrace_smulRight,ha,coordinateNormalVelocity]

lemma cofactor_field_derivative {G : Cover → Cover} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (x n u v : Cover) :
    fderiv ℝ (fun p : Cover×Cover ↦ cofactorLinear (fderiv ℝ G p.1) p.2) (x,n) (u,v)=
      cofactorLinear (fderiv ℝ (fderiv ℝ G) x u) n+
        cofactorLinear (fderiv ℝ G x) v := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hfst : HasFDerivAt (fun p : Cover×Cover ↦ p.1) (ContinuousLinearMap.fst ℝ Cover Cover) (x,n) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun p : Cover×Cover ↦ p.2) (ContinuousLinearMap.snd ℝ Cover Cover) (x,n) := hasFDerivAt_snd
  have hd := ((cofactorOperator.hasFDerivAt.comp (x,n)
    ((hg.differentiable (by simp) x).hasFDerivAt.comp (x,n) hfst)).clm_apply
      hsnd).fderiv
  change fderiv ℝ (fun p : Cover×Cover ↦ cofactorOperator (fderiv ℝ G p.1) p.2) (x,n) (u,v)=_
  simp only [Function.comp_def] at hd
  rw [hd]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,cofactorOperator_apply]
  rw [add_comm]
  rfl

lemma derivative_transport {F G : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Cover) :
    fderiv ℝ (fun y ↦ fderiv ℝ G y (F y)) x=
      fderiv ℝ (fderiv ℝ G) x (F x)+(fderiv ℝ G x).comp (fderiv ℝ F x) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
  rw [fderiv_clm_apply (hg.differentiable (by simp) x)
    (hF.differentiable (by simp) x)]
  have hs : (fderiv ℝ (fderiv ℝ G) x).flip (F x)=fderiv ℝ (fderiv ℝ G) x (F x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (hG.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v (F x)
  rw [hs,add_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def variationField (a : Variation) (x : Cover) : Cover :=
  a.function x • EuclideanSpace.single a.coordinate 1

lemma variationField_smooth (a : Variation) : ContDiff ℝ (⊤ : ℕ∞) (variationField a) :=
  a.smooth.smul contDiff_const

lemma variationField_periodic (a : Variation) (m : Fin 3 → ℤ) (x : Cover) :
    variationField a (x+latticeVector m)=variationField a x := by
  simp only [variationField,a.periodic]

lemma chainVelocity_append (l : List Variation) (a : Variation) :
    chainVelocity (l++[a])=fun x ↦ chainVelocity l x+variationField a x := by
  funext x
  simp [chainVelocity,variationField,List.map_append]

lemma chainVelocity_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞) (chainVelocity l) := by
  induction l using List.reverseRecOn with
  | nil => exact contDiff_const
  | append_singleton l a ih => rw [chainVelocity_append]; exact ih.add (variationField_smooth a)

lemma chainVelocity_periodic (l : List Variation) (m : Fin 3 → ℤ) (x : Cover) :
    chainVelocity l (x+latticeVector m)=chainVelocity l x := by
  unfold chainVelocity
  congr 1
  apply List.map_congr_left
  intro a _
  rw [a.periodic]

def motionJet (l : List Variation) (x : Cover) : Cover×Cover :=
  l.foldl (fun j a ↦ (j.1+variationField a x,
    j.2+2 • fderiv ℝ (variationField a) x j.1)) (0,0)

lemma motionJet_append (l : List Variation) (a : Variation) (x : Cover) :
    motionJet (l++[a]) x=((motionJet l x).1+variationField a x,
      (motionJet l x).2+2 • fderiv ℝ (variationField a) x (motionJet l x).1) := by
  simp only [motionJet,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma motionJet_first (l : List Variation) (x : Cover) : (motionJet l x).1=chainVelocity l x := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih => simp only [motionJet_append,chainVelocity_append,ih]

lemma motionJet_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞) (motionJet l) := by
  induction l using List.reverseRecOn with
  | nil => exact contDiff_const
  | append_singleton l a ih =>
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (variationField a)) :=
      (variationField_smooth a).fderiv_right (by simp)
    simp_rw [show motionJet (l++[a])=(fun x ↦ ((motionJet l x).1+variationField a x,
      (motionJet l x).2+2 • fderiv ℝ (variationField a) x (motionJet l x).1)) from funext (motionJet_append l a)]
    exact (ih.fst.add (variationField_smooth a)).prodMk (ih.snd.add ((hd.clm_apply ih.fst).const_smul 2))

lemma motionJet_periodic (l : List Variation) (m : Fin 3 → ℤ) (x : Cover) :
    motionJet l (x+latticeVector m)=motionJet l x := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [motionJet_append,ih,variationField_periodic,
      fderiv_periodic (variationField_periodic a)]

lemma simultaneousMove_second_deriv (l : List Variation) (x : Cover) :
    deriv (deriv (fun t ↦ chainMove (simultaneousChain l t) x)) 0=(motionJet l x).2 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainMove,motionJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ variationField a (chainMove (simultaneousChain l t) x)) := (variationField_smooth a).comp hm
    have he : (fun t ↦ chainMove (simultaneousChain (l++[a]) t) x)=
        (fun t ↦ chainMove (simultaneousChain l t) x+t • variationField a (chainMove (simultaneousChain l t) x)) := by
      funext t
      simp [simultaneousChain,List.map_append,chainMove_append,chainMove,coordinateMove,variationField,smul_smul]
    rw [he,second_deriv_add_time_smul hm hf,ih,motionJet_append]
    dsimp only
    congr 2
    have hd : HasFDerivAt (variationField a) (fderiv ℝ (variationField a) x)
        (chainMove (simultaneousChain l 0) x) := by
      simpa only [simultaneousMove_zero] using
        ((variationField_smooth a).differentiable (by simp) x).hasFDerivAt
    simpa only [Function.comp_def,simultaneousMove_deriv,motionJet_first] using
      (hd.comp_hasDerivAt 0 (hm.differentiable (by simp) 0).hasDerivAt).deriv

lemma chainNormalVelocity_eq_cofactor (l : List Variation) (x n : Cover) :
    chainNormalVelocity l x n=cofactorLinear (fderiv ℝ (chainVelocity l) x) n := by
  induction l using List.reverseRecOn with
  | nil =>
    change 0=cofactorLinear (fderiv ℝ (fun _ : Cover ↦ (0 : Cover)) x) n
    simp [cofactorLinear]
  | append_singleton l a ih =>
    rw [chainVelocity_append,fderiv_fun_add ((chainVelocity_smooth l).differentiable (by simp) x)
      ((variationField_smooth a).differentiable (by simp) x),cofactorLinear_add,← ih]
    rw [show cofactorLinear (fderiv ℝ (variationField a) x) n=
      coordinateNormalVelocity a.coordinate a.function x n from
        cofactorLinear_coordinate (a.smooth.differentiable (by simp) x) a.coordinate n]
    simp [chainNormalVelocity,List.map_append]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def volumeQuadratic (L : Cover →L[ℝ] Cover) : ℝ :=
  (coverTrace L)^2-coverTrace (L.comp L)

lemma volumeQuadratic_add (L M : Cover →L[ℝ] Cover) :
    volumeQuadratic (L+M)=volumeQuadratic L+volumeQuadratic M+
      2*(coverTrace L*coverTrace M-coverTrace (M.comp L)) := by
  simp only [volumeQuadratic,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    coverTrace_add,coverTrace_comp_comm L M]
  ring

end CubicTorus
end
end
end

end OAI
