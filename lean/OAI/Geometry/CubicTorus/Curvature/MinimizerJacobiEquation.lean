import Mathlib
import OAI.Geometry.CubicTorus.Regularity.NormalRotationWeak

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_H1_jacobi_equation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (s : ℝ),‖n‖=1 ∧ 0<s ∧ f 0=0 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ y∈Metric.ball (0 : Plane) s,
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ z∈Metric.ball (0 : Cover) s,
        quotientMap (x+z)∈frontier (openRepresentative E) ↔
          normalGraph n f (normalPlaneCoordinates n z)=z) ∧
      LinearCMCEquationNear (fun y => cmcWeight (gradient f y)*
        F (quotientMap (x+normalGraph n f y))) (gradient f) (fun _ => 0) := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have he (z : Cover) : cubeCenter+z+a=x+z := by dsimp [a]; abel
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    dsimp [a]; congr 1; abel
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  have hNu' (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E')) :
      ∀ᶠ z in 𝓝 y,‖N' z‖=1 := by
    rw [frontier_openRepresentative_translation hE] at hy
    have hy' : quotientMap (y+a)∈frontier (openRepresentative E) := by
      simpa only [mem_preimage,quotientMap_add] using hy
    exact (continuous_add_const a).continuousAt.eventually (hNu (y+a) hy')
  let F' : Torus → ℝ := fun z => F (z+quotientMap a)
  have hF' : ContinuousOn F' (frontier (openRepresentative E')) := by
    apply hF.comp (continuous_add_const _).continuousOn
    intro z hz
    rwa [frontier_openRepresentative_translation hE] at hz
  obtain ⟨v,hv,hpull,hvh⟩ := surfaceH1_jacobi_translation_lift μ a N hN hp hu hhom
  have hvF : (v.1 : NormalBundle → ℝ)=ᵐ[(μ.map (translateNormal a) : Measure NormalBundle)]
      F' ∘ normalProjection := surfaceH1_translation_value μ a hpull hFm hFu
  obtain ⟨n,f,s,hn,hs,hf0,hf,hin,hcover,hreg⟩ :=
    isMinimizerAt_centered_H1_jacobi_equation hV hE' hmin' hc
      (isNormalMeasure_translation hE hμ a) N' hN' hae' hNu' hv hvh hF' hvF
  refine ⟨n,f,s,hn,hs,hf0,hf,?_,?_,?_⟩
  · intro y hy
    have hi := hin y hy
    rw [frontier_openRepresentative_translation hE] at hi
    simpa only [mem_preimage,← quotientMap_add,he] using hi
  · intro z hz
    have hc' := hcover z hz
    rw [frontier_openRepresentative_translation hE] at hc'
    simpa only [mem_preimage,← quotientMap_add,he] using hc'
  · simpa only [F',← quotientMap_add,he] using hreg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_H1_jacobi_zero_germs_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    IsClosed (frontier (openRepresentative E)∩relativeZeroNeighborhood
      (frontier (openRepresentative E)) F) := by
  let S := frontier (openRepresentative E)
  let Z := relativeZeroNeighborhood S F
  let D := S∩Z
  have hD : D⊆S := inter_subset_left
  apply isClosed_of_closure_subset
  intro a ha
  have haS : a∈S := closure_minimal hD isClosed_frontier ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rwa [hxa]
  obtain ⟨n,g,s,hn,hs,hg0,hg,hin,hcover,hlin⟩ :=
    isMinimizerAt_H1_jacobi_equation hV hE hmin hμ N hN hp hae hNu hu hhom hFm hF hFu x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hfc : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => F (φ y)) (Metric.ball 0 s) := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    apply isMinimizerAt_H1_jacobi_parametric_smooth hV hE hmin hμ N hN hp hae hNu hu hhom hFm hF hFu x hG.contDiffAt
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact hin z hz
  let v : Plane → ℝ := fun y => cmcWeight (gradient g y)*F (φ y)
  have hvc : ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 s) :=
    (cmcWeight_contDiff.comp (plane_gradient_contDiff hg)).contDiffOn.mul hfc
  obtain ⟨w,K,hw,_,_,hwv⟩ := smooth_graph_extension_compact hs hvc
  have hwe : w=ᶠ[𝓝 (0 : Plane)] v := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (half_pos hs)] with y hy
    exact hwv hy
  have hle : LinearCMCEquationNear w (gradient g) (fun _ => 0) :=
    hlin.congr hwe Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
  obtain ⟨r,hr,hle⟩ := hle
  let ε := min (s/2) r
  have hε : 0<ε := lt_min (half_pos hs) hr
  have hεs : ε ≤ s/2 := min_le_left _ _
  have hεr : ε≤r := min_le_right _ _
  have hεS : ε ≤ s := hεs.trans (by linarith)
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=cmcWeight (gradient g y)*F (φ y) := hwv (Metric.ball_subset_ball hεs hy)
  have hc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure hD
    (by filter_upwards [Metric.ball_mem_nhds (0 : Cover) hs] with z hz; exact (hcover z hz).mp)
    (by rwa [hxa])
  obtain ⟨y,hyD,hyd⟩ := Metric.mem_closure_iff.mp hc ε hε
  have hyb : y∈Metric.ball (0 : Plane) ε := by
    simpa only [Metric.mem_ball,dist_comm] using hyd
  have hO : IsOpen (φ ⁻¹' Z∩Metric.ball 0 ε) :=
    (isOpen_interior.preimage hφ).inter Metric.isOpen_ball
  have hyO : y∈φ ⁻¹' Z∩Metric.ball 0 ε := ⟨hyD.2,hyb⟩
  have hzeroO : φ ⁻¹' Z∩Metric.ball 0 ε⊆{z | w z=0} := by
    intro z hz
    change w z=0
    rw [hws z hz.2,relativeZeroNeighborhood_zero
      (hin z (Metric.ball_subset_ball hεS hz.2)) hz.1,mul_zero]
  have hpatch : (Metric.ball (0 : Plane) ε∩interior {z | w z=0}).Nonempty :=
    ⟨y,hyb,(hO.subset_interior_iff.mpr hzeroO) hyO⟩
  have hvan := (hle.mono (Metric.ball_subset_ball hεr)).unique_continuation hg hw
    Metric.isOpen_ball (convex_ball (0 : Plane) ε).isPreconnected hpatch
  refine ⟨haS,?_⟩
  rw [← hxa]
  apply quotient_graph_zero_germ
    (by filter_upwards [Metric.ball_mem_nhds (0 : Cover) hs] with z hz; exact (hcover z hz).mp)
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hε] with y hy
  have hz := hvan y hy
  rw [hws y hy] at hz
  exact (mul_eq_zero.mp hz).resolve_left (cmcWeight_pos _).ne'

theorem isMinimizerAt_H1_jacobi_unique_continuation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hpatch : (frontier (openRepresentative E)∩relativeZeroNeighborhood
      (frontier (openRepresentative E)) F).Nonempty) :
    ∀ a∈frontier (openRepresentative E),F a=0 := by
  exact preconnected_zero_of_closed_germ hconn
    (isMinimizerAt_H1_jacobi_zero_germs_closed hV hE hmin hμ N hN hp hae hNu hu hhom hFm hF hFu)
    hpatch

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_mean_zero_negative_point {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars)
    (hzero : surfaceMean μ (surfaceSmoothJet μ f)=0)
    {D : Set Torus} (hDm : MeasurableSet D)
    (hD : IsPositiveNodalPiece f
      (frontier (openRepresentative E)) D) (hDn : D.Nonempty) :
    ∃ a∈frontier (openRepresentative E),f.val (representative a)<0 := by
  classical
  by_contra! hn
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hpos := isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hDm hD hDn
  rw [surfaceMean_nodal] at hpos
  rw [surfaceMean_of_smooth] at hzero
  have hle : (∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle)) ≤
      ∫ z,f.val z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_mono_ae ((nodalSurfaceValue_memLp μ f D hDm).integrable (by norm_num))
      ((smoothScalarValue f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [hbd] with z hz
    by_cases hd : normalProjection z∈D
    · simp only [nodalSurfaceValue,indicator_of_mem (show z∈normalProjection ⁻¹' D from hd),
        smoothScalarValue,ContinuousMap.coe_mk,le_refl]
    · have hv : f.val (representative (normalProjection z))=f.val z.1 := periodic_representative f.property.2 _
      simpa only [nodalSurfaceValue,indicator_of_notMem (show z∉normalProjection ⁻¹' D from hd),
        smoothScalarValue,ContinuousMap.coe_mk,hv] using hn (normalProjection z) hz
  linarith

theorem isMinimizerAt_general_positive_nodal_not_disjoint {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u)
    (f : smoothPeriodicScalars)
    (hfmean : surfaceMean μ (surfaceSmoothJet μ f)=0)
    (hj : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) z=0)
    {D A : Set Torus}
    (hD : IsPositiveNodalPiece f
      (frontier (openRepresentative E)) D)
    (hA : IsPositiveNodalPiece f
      (frontier (openRepresentative E)) A)
    (hDn : D.Nonempty) (hAn : A.Nonempty) : ¬Disjoint D A := by
  intro hDA
  obtain ⟨hDm,hdmem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hD
  obtain ⟨hAm,hamem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hA
  let d := nodalSurfaceJet μ f D hDm
  let a := nodalSurfaceJet μ f A hAm
  let u := surfaceNodalBalance μ d a
  have hdnull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f D hDm hdmem hj
  have hanull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f A hAm hamem hj
  have hnull : surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 :=
    surfaceNodalBalance_null μ _ hdnull hanull (surfaceJacobiB_disjoint_nodal μ _ f f D A hDm hAm hDA)
  have humem : u∈surfaceH1 μ := surfaceNodalBalance_mem μ hdmem hamem
  have hmean : surfaceMean μ u=0 := surfaceNodalBalance_mean μ d a
  have hapos : 0<surfaceMean μ a := isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hAm hA hAn
  obtain ⟨b,hbS,hbneg⟩ := isMinimizerAt_mean_zero_negative_point hV hE hmin hμ f hfmean hDm hD hDn
  let U : Set Torus := {b | f.val (representative b)<0}
  have hU : IsOpen U := isOpen_lt (continuous_periodic_descent f.property.1.continuous f.property.2) continuous_const
  have hbU : b∈U := hbneg
  have hUD : Disjoint U D := by
    rw [Set.disjoint_left]
    intro x hx hd
    have hh := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hd
    exact (not_lt_of_ge hh.le) hx
  have hUA : Disjoint U A := by
    rw [Set.disjoint_left]
    intro x hx ha
    have hh := (positiveNodalPiece_superlevels f isClosed_frontier hA).2.1 x ha
    exact (not_lt_of_ge hh.le) hx
  have hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0 :=
    isMinimizerAt_H1_unused_patch_homogeneous hV hE hmin hμ _ hs humem hmean hnull
      hU ⟨b,hbU,hbS⟩ (surfaceNodalBalance_zero_patch μ
        (nodalSurfaceJet_zero_outside μ f D U hDm hUD)
        (nodalSurfaceJet_zero_outside μ f A U hAm hUA))
  let F := surfaceNodalBalanceValue μ f f D A hDm hAm
  have hzU : U⊆relativeZeroNeighborhood (frontier (openRepresentative E)) F := by
    apply hU.subset_interior_iff.mpr
    intro x hx
    right
    exact surfaceNodalBalanceValue_nonpos μ f hDm hAm hD hA (le_of_lt hx)
  have hvan := isMinimizerAt_H1_jacobi_unique_continuation hV hE hmin hμ N hN hp hae hNu
    humem hhom (surfaceNodalBalanceValue_measurable μ f f D A hDm hAm)
    (surfaceNodalBalanceValue_continuousOn μ f f hDm hAm hD hA)
    (surfaceNodalBalanceValue_ae μ f f D A hDm hAm) hS ⟨b,hbS,hzU hbU⟩
  obtain ⟨x,hx⟩ := hDn
  have hz := hvan x (hD.subset f hx)
  rw [surfaceNodalBalanceValue_on_left μ f f D A hDm hAm hDA hx] at hz
  have hfp := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hx
  exact (mul_pos hapos hfp).ne' hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.frontier_preconnected {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    IsPreconnected (frontier (openRepresentative E)) := by
  rw [← hr.boundary_range]
  apply isPreconnected_range
  exact continuous_quotientMap.comp ((coordinateSectionPoint_continuous_pair c).comp
    (continuous_fst.prodMk (hr.1.continuous.smul (unitAngle_continuous.comp continuous_snd))))

theorem TrueRadialTube.exists_rotation_nodal_restriction {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x)
      (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id)) ∧
      ∀ D A : Set Torus,
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨μ,N,hN,hNp,g,hg,hp,hμ,ha,hu,he,hmean,hj,hs⟩ := hr.exists_rotation_jacobi hV hE hm
  refine ⟨μ,N,hN,hNp,g,hg,hp,hμ,ha,he,?_⟩
  intro D A hD hA hDn hAn
  exact isMinimizerAt_general_positive_nodal_not_disjoint hV hE hm hr.frontier_preconnected
    hμ N hN hNp ha hu hs (periodicRotationNormalScalar g hg hp c N hN hNp)
    hmean hj hD hA hDn hAn

theorem TrueRadialTube.exists_rotation_nodal_restriction_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x)
      (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id)) ∧
      ∀ D A : Set Torus,
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  let E' := toMeasurable torusVolume E
  have he : E'=ᵐ[torusVolume] E := hm.1.1.toMeasurable_ae_eq
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hm' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae he).mpr hm
  have hopen : openRepresentative E'=openRepresentative E := openRepresentative_congr_ae he
  have hr' : TrueRadialTube E' c r := by simpa only [TrueRadialTube,hopen] using hr
  obtain ⟨μ,N,hN,hNp,g,hg,hp,hμ,ha,hgerm,hnodal⟩ :=
    hr'.exists_rotation_nodal_restriction hV hE' hm'
  refine ⟨μ,N,hN,hNp,g,hg,hp,hμ.congr_ae he,ha,hgerm,?_⟩
  simpa only [hopen] using hnodal

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem first_transition_nonstandard_rotation_nodal
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (G : Set Torus) (c : Cover) (r : ℝ × ℝ → ℝ),
      MeasurableSet G ∧ IsMinimizerAt (4*Real.pi/81) G ∧
      ¬SmallStandardRegion (4*Real.pi/81) G ∧ TrueRadialTube G c r ∧
      ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x)
      (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      IsNormalMeasure G μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id)) ∧
      ∀ D A : Set Torus,
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative G)) D →
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative G)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨G,c,r,hG,hmG,hnG,hr,_⟩ :=
    isMinimizerAt_first_transition_nonstandard_toroidal_reduction hmE hnstd
  refine ⟨G,c,r,hG,hmG,hnG,hr,?_⟩
  apply hr.exists_rotation_nodal_restriction _ hG hmG
  exact ⟨firstTransition_mem_Ioo_half.1,by linarith [firstTransition_mem_Ioo_half.2]⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace CubicTorus

lemma antitoneOn_deriv_nonpos_interior {f : ℝ → ℝ} {a b t : ℝ}
    (hm : AntitoneOn f (Icc a b)) (ht : t∈Ioo a b) : deriv f t≤0 := by
  rw [← derivWithin_of_isOpen isOpen_Ioo ht]
  exact (hm.mono Ioo_subset_Icc_self).derivWithin_nonpos

theorem antitone_ac_area_measure {f : ℝ → ℝ} (hc : Continuous f) {a b : ℝ}
    (hab : a≤b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hm : AntitoneOn f (Icc a b)) :
    Measure.map f ((volume.restrict (Ioo a b)).withDensity
      (fun t => ENNReal.ofReal (-deriv f t)))=volume.restrict (Ioo (f b) (f a)) := by
  have hi : Integrable (fun t => -deriv f t) (volume.restrict (Ioo a b)) :=
    (hf.intervalIntegrable_deriv.1.mono_set Ioo_subset_Ioc_self).neg
  let := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have hwd : Measurable (fun t => ENNReal.ofReal (-deriv f t)) :=
    (measurable_deriv f).neg.ennreal_ofReal
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro γ
  rw [integral_map hc.measurable.aemeasurable γ.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hwd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hconv : (∫ t in Ioo a b,(ENNReal.ofReal (-deriv f t)).toReal • γ (f t))=
      -(∫ t in a..b,γ (f t)*deriv f t) := by
    rw [intervalIntegral.integral_of_le hab,← integral_neg,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [ENNReal.toReal_ofReal (neg_nonneg.mpr (antitoneOn_deriv_nonpos_interior hm ht)),
      smul_eq_mul]
    ring
  rw [hconv,ac_substitution_boundedContinuous hf γ,← intervalIntegral.integral_symm,
    intervalIntegral.integral_of_le (hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc.symm

theorem antitone_ac_area_substitution {f : ℝ → ℝ} (hc : Continuous f) {a b : ℝ}
    (hab : a≤b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hm : AntitoneOn f (Icc a b)) {γ : ℝ → ℝ≥0∞} (hγ : Measurable γ) :
    (∫⁻ t in Ioo a b,γ (f t)*ENNReal.ofReal (-deriv f t))=
      ∫⁻ w in Ioo (f b) (f a),γ w := by
  have hwd : Measurable (fun t => ENNReal.ofReal (-deriv f t)) :=
    (measurable_deriv f).neg.ennreal_ofReal
  have hgf : Measurable (fun t => γ (f t)) := hγ.comp hc.measurable
  rw [← antitone_ac_area_measure hc hab hf hm,
    lintegral_map hγ hc.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hwd hgf]
  apply lintegral_congr
  intro t
  exact mul_comm _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_axial_area_substitution {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    {γ : ℝ → ℝ≥0∞} (hγ : Measurable γ) :
    (∫⁻ t in Ioo (chamberCorner s i) (chamberCorner s i+1/2),
      γ (axialSectionArea (openRepresentative E) i t)*
        ENNReal.ofReal (-deriv (axialSectionArea (openRepresentative E) i) t))=
      ∫⁻ w in Ioo (axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2))
        (axialSectionArea (openRepresentative E) i (chamberCorner s i)),γ w :=
  antitone_ac_area_substitution
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i) (by linarith)
    ((isMinimizerAt_absolutelyContinuous_axialSectionArea hV hE hm hμ hN hp ha hs hsg hH i).mono
      (chamber_interval_subset_unit s i))
    (isMinimizerAt_antitoneOn_axialSectionArea hV hE hm hμ hN hp ha hs hsg i) hγ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma closed_set_complete_line {S : Set Cover} (hS : IsClosed S) (v : Cover)
    (hloc : ∀ x∈S,∀ᶠ t : ℝ in 𝓝 0,x+t • v∈S)
    {x : Cover} (hx : x∈S) (t : ℝ) : x+t • v∈S := by
  let f : ℝ → Cover := fun s => x+s • v
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hclosed : IsClosed (f ⁻¹' S) := hS.preimage hf
  have hopen : IsOpen (f ⁻¹' S) := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    have ht : Tendsto (fun r : ℝ => r-s) (𝓝 s) (𝓝 0) := by
      have hc : Continuous (fun r : ℝ => r-s) := continuous_id.sub continuous_const
      simpa only [sub_self] using hc.tendsto s
    filter_upwards [ht.eventually (hloc (f s) hs)] with r hr
    change x+r • v∈S
    have he : f s+(r-s) • v=x+r • v := by dsimp [f]; rw [sub_smul]; abel
    rwa [he] at hr
  have he : f ⁻¹' S=univ := (show IsClopen (f ⁻¹' S) from ⟨hclosed,hopen⟩).eq_univ
    ⟨0,by change x+0 • v∈S; simpa using hx⟩
  have hh : t∈f ⁻¹' S := by rw [he]; trivial
  exact hh

lemma open_phase_line_invariant {U : Set Torus} (hU : IsOpen U) (v : Cover)
    (hline : ∀ x,quotientMap x∈frontier U → ∀ t : ℝ,
      quotientMap (x+t • v)∈frontier U) (x : Cover) (t : ℝ) :
    quotientMap (x+t • v)∈U ↔ quotientMap x∈U := by
  by_cases hx : quotientMap x∈frontier U
  · have hy := hline x hx t
    rw [hU.frontier_eq] at hx hy
    exact iff_of_false hy.2 hx.2
  · let f : ℝ → Torus := fun s => quotientMap (x+s • v)
    have hf : Continuous f := continuous_quotientMap.comp
      (continuous_const.add (continuous_id.smul continuous_const))
    have ha (s : ℝ) : f s∉frontier U := by
      intro hs
      have ht := hline (x+s • v) hs (-s)
      apply hx
      simpa only [neg_smul,add_neg_cancel_right] using ht
    simpa only [f,zero_smul,add_zero] using continuous_line_avoids_frontier hU hf ha t 0

theorem isMinimizerAt_zero_normal_flow {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) (hz : ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫=0) :
    (∀ x,quotientMap x∈frontier (openRepresentative E) → ∀ t : ℝ,
      quotientMap (x+t • v)∈frontier (openRepresentative E)) ∧
    (∀ x : Cover,∀ t : ℝ,quotientMap (x+t • v)∈openRepresentative E ↔
      quotientMap x∈openRepresentative E) ∧
    ∀ t : ℝ,(fun a : Torus => a+quotientMap (t • v)) ⁻¹' E =ᵐ[torusVolume] E := by
  let F := toMeasurable torusVolume E
  have he : F =ᵐ[torusVolume] E := hmE.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae he).mpr hmE
  have hor : openRepresentative F=openRepresentative E := openRepresentative_congr_ae he
  have hz' : ∀ x,quotientMap x∈frontier (openRepresentative F) → ⟪v,N x⟫=0 := by
    intro x hx
    have hh := hz (quotientMap x) (by simpa only [hor] using hx)
    simpa only [periodic_representative hp] using hh
  have hloc := isMinimizerAt_zero_normal_local_flow hV hF hmF (hμ.congr_ae he.symm) hN hp hae v hz'
  have hline' : ∀ x,quotientMap x∈frontier (openRepresentative F) → ∀ t : ℝ,
      quotientMap (x+t • v)∈frontier (openRepresentative F) := by
    intro x hx t
    exact closed_set_complete_line (isClosed_frontier.preimage continuous_quotientMap) v hloc hx t
  have hline : ∀ x,quotientMap x∈frontier (openRepresentative E) → ∀ t : ℝ,
      quotientMap (x+t • v)∈frontier (openRepresentative E) := by simpa only [hor] using hline'
  have hphase := open_phase_line_invariant (isOpen_openRepresentative E) v hline
  refine ⟨hline,hphase,?_⟩
  have haeE : openRepresentative E =ᵐ[torusVolume] E := by
    rw [← hor]
    exact (isMinimizerAt_openRepresentative_ae hV hF hmF).trans he
  intro t
  have heq : (fun a : Torus => a+quotientMap (t • v)) ⁻¹' openRepresentative E=openRepresentative E := by
    ext a
    simpa only [mem_preimage,quotientMap_add,quotientMap_representative] using hphase (representative a) t
  exact ((measurePreserving_add_right torusVolume _).quasiMeasurePreserving.preimage_ae_eq haeE).symm.trans
    ((Filter.EventuallyEq.of_eq heq).trans haeE)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_H1_jacobi_unique_continuation_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    (hpatch : (frontier (openRepresentative E)∩relativeZeroNeighborhood
      (frontier (openRepresentative E)) F).Nonempty) :
    ∀ a∈frontier (openRepresentative E),F a=0 := by
  let E' := toMeasurable torusVolume E
  have he : E'=ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hm' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae he).mpr hmin
  have hS : frontier (openRepresentative E')=frontier (openRepresentative E) :=
    congrArg frontier (openRepresentative_congr_ae he)
  have hNu' : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E') →
      ∀ᶠ y in 𝓝 x,‖N y‖=1 := by simpa only [hS] using hNu
  exact isMinimizerAt_H1_jacobi_unique_continuation hV hE' hm' (hμ.congr_ae he.symm)
    N hN hp hae hNu' hu hhom hFm (by simpa only [hS] using hF) hFu
    (by simpa only [hS] using hconn) (by simpa only [hS] using hpatch) |>
      (by simpa only [hS] using ·)

theorem isMinimizerAt_normal_unique_continuation_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (frontier (openRepresentative E)∩U).Nonempty)
    (hz : ∀ a∈frontier (openRepresentative E)∩U,⟪v,N (representative a)⟫=0) :
    ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫=0 := by
  let E' := toMeasurable torusVolume E
  have he : E'=ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hm' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae he).mpr hmin
  have hs : frontier (openRepresentative E')=frontier (openRepresentative E) :=
    congrArg frontier (openRepresentative_congr_ae he)
  have hh := isMinimizerAt_normal_unique_continuation hV hE' hm' (by simpa only [hs] using hS)
    (hμ.congr_ae he.symm) hN hp hae v hU (by simpa only [hs] using hpatch)
    (by simpa only [hs] using hz)
  simpa only [hs] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalGraph_regraph_transverse {m n ν : Cover} (hm : ‖m‖=1) (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0=0)
    (ht : ∀ v : Plane,⟪ν,fderiv ℝ (normalGraph m g) 0 v⟫=0)
    (htrans : ⟪ν,n⟫≠0) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),normalGraph m g
        (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f
        (normalPlaneCoordinates n (normalGraph m g y))=normalGraph m g y := by
  let G := normalGraph m g
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry m).contDiff.add (hg.smul contDiff_const)
  have hG0 : G 0=0 := by
    change (normalPlaneLinearIsometry m) 0+g 0 • m=0
    simp [hg0]
  let P : Plane → Plane := fun y => normalPlaneCoordinates n (G y)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (normalPlaneCoordinates n).contDiff.comp hG
  have hP0 : P 0=0 := by simp [P,hG0]
  have hder : fderiv ℝ P 0=(normalPlaneCoordinates n).comp (fderiv ℝ G 0) :=
    ((normalPlaneCoordinates n).hasFDerivAt.comp 0 (hG.differentiable (by simp) 0).hasFDerivAt).fderiv
  have hinj : Function.Injective (fderiv ℝ P 0) := by
    intro v w he
    have he' : fderiv ℝ G 0 v=fderiv ℝ G 0 w := by
      rw [hder] at he
      let z := fderiv ℝ G 0 v-fderiv ℝ G 0 w
      have hz : normalPlaneCoordinates n z=0 := by
        simp only [z,map_sub]
        exact sub_eq_zero.mpr he
      have hdec := normalPlane_decomposition hn z
      rw [hz] at hdec
      have hemb : normalPlaneEmbedding n (0 : Plane)=0 := by
        change (normalPlaneLinearIsometry n) 0=0
        exact map_zero _
      rw [hemb,zero_add] at hdec
      have hnz : ⟪ν,z⟫=0 := by
        change ⟪ν,fderiv ℝ (normalGraph m g) 0 v-fderiv ℝ (normalGraph m g) 0 w⟫=0
        rw [inner_sub_right,ht v,ht w,sub_self]
      have hcoef : ⟪n,z⟫=0 := by
        rw [← hdec,real_inner_smul_right] at hnz
        exact (mul_eq_zero.mp hnz).resolve_right htrans
      rw [hcoef,zero_smul] at hdec
      exact sub_eq_zero.mp hdec.symm
    have hh := congrArg (normalPlaneCoordinates m) he'
    simpa only [G,normalGraph_fderiv_apply hg,map_add,map_smul,normalPlaneCoordinates_embedding,
      normalPlaneCoordinates_normal hm,smul_zero,add_zero] using hh
  obtain ⟨q,R,hR,hq0,hq,hpq,hqp⟩ := plane_smooth_local_inverse hP hP0 hinj
  let f₀ : Plane → ℝ := fun y => ⟪n,G (q y)⟫
  have hf₀ : ContDiffOn ℝ (⊤ : ℕ∞) f₀ (Metric.ball 0 R) :=
    contDiffOn_const.inner ℝ (hG.comp_contDiffOn hq)
  obtain ⟨f,hf,hff⟩ := smooth_graph_extension hR hf₀
  have hf0 : f 0=0 := by
    rw [hff (by simpa using half_pos hR)]
    simp [f₀,hq0,hG0]
  have heq : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n f y=G (q y) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (half_pos hR)] with y hy
    have hyR : y∈Metric.ball (0 : Plane) R := (Metric.ball_subset_ball (by linarith)) hy
    have hh := normalPlane_decomposition hn (G (q y))
    have hpq' : normalPlaneCoordinates n (G (q y))=y := hpq y hyR
    rw [hpq'] at hh
    simpa only [normalGraph,hff hy,f₀] using hh
  refine ⟨f,hf,hf0,?_,?_⟩
  · filter_upwards [heq] with y hy
    rw [hy,normalPlaneCoordinates_graph hm]
  · have htP : Tendsto P (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa [hP0] using hP.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [htP.eventually heq,hqp] with y hy hqy
    change normalGraph n f (P y)=G y
    rw [hy,hqy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_transverse_graph_cover {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {x n : Cover} (hx : quotientMap x∈frontier (openRepresentative E))
    (hn : ‖n‖=1) (ht : ⟪N x,n⟫≠0) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨m,g,σ,hm,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmE hμ hN hp hae x hx
  have hcenter : N x=σ • graphSlopeNormal m (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  have htan (v : Plane) : ⟪N x,fderiv ℝ (normalGraph m g) 0 v⟫=0 := by
    rw [hcenter,real_inner_smul_left,normalGraph_derivative_tangent hm hg,mul_zero]
  obtain ⟨f,hf,hf0,hforward,hback⟩ := normalGraph_regraph_transverse hm hn hg hg0 htan ht
  have hc := normalGraph_regraph_cover hf hg hf0 hg0 hforward hback
  refine ⟨f,hf,hf0,?_⟩
  filter_upwards [hcover,hc] with v hv hvc
  exact hv.trans hvc

end CubicTorus

end
end

end OAI
