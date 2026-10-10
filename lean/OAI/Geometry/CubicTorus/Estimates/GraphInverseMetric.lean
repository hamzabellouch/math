import Mathlib
import OAI.Geometry.CubicTorus.Estimates.ChainAcceleration

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (φ : Cover → ℝ) (N : Cover → Cover),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m y,φ (y+latticeVector m)=φ y) ∧
      (∀ m y,N (y+latticeVector m)=N y) ∧
      (∀ y,0≤φ y) ∧ (∀ᶠ y in 𝓝 x,φ y=1) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 → N z.1=(z.2 : Cover) := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    dsimp [a]
    congr 1
    abel
  obtain ⟨φ,N,hφ,hN,hφp,hNp,hpos,hnear,hpatch⟩ :=
    actual_centered_normal_patch hV hE' hmin' hc (isNormalMeasure_translation hE hμ a)
  refine ⟨fun y ↦ φ (y-a),fun y ↦ N (y-a),
    hφ.comp (contDiff_id.sub contDiff_const),hN.comp (contDiff_id.sub contDiff_const),
    ?_,?_,fun y ↦ hpos _,?_,?_⟩
  · intro m y
    change φ ((y+latticeVector m)-a)=φ (y-a)
    rw [add_sub_right_comm,hφp]
  · intro m y
    change N ((y+latticeVector m)-a)=N (y-a)
    rw [add_sub_right_comm,hNp]
  · have ht : Tendsto (fun y : Cover ↦ y-a) (𝓝 x) (𝓝 cubeCenter) := by
      have he : x-a=cubeCenter := by dsimp [a]; abel
      have ht0 : Tendsto (fun y : Cover ↦ y-a) (𝓝 x) (𝓝 (x-a)) :=
        (continuous_id.sub continuous_const).tendsto x
      rwa [he] at ht0
    exact ht.eventually hnear
  · have hh := ae_of_ae_map (measurable_translateNormal a).aemeasurable hpatch
    filter_upwards [hh] with z hz
    change (0<φ (translateNormal a z).1 → N (translateNormal a z).1=(z.2 : Cover)) at hz
    simpa only [translateNormal_periodic_eval hφp,translateNormal_periodic_eval hNp] using hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_global_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) := by
  classical
  let K : Set Cover := closedFundamentalCube ∩ quotientMap ⁻¹' frontier (openRepresentative E)
  have hK : IsCompact K := isCompact_closedFundamentalCube.inter_right
    (isClosed_frontier.preimage continuous_quotientMap)
  have hpatch (x : K) := isMinimizerAt_normal_patch hV hE hmin hμ x.1 x.2.2
  choose φ N hφ hN hφp hNp hφn hnear hae using hpatch
  let U : K → Set Cover := fun x ↦ interior {y | φ x y=1}
  have hU : ∀ x : K,(x : Cover)∈U x := fun x ↦ mem_interior_iff_mem_nhds.mpr (hnear x)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U (fun _ ↦ isOpen_interior)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x,hx⟩,hU ⟨x,hx⟩⟩)
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hcover : ∀ᵐ z ∂(μ : Measure NormalBundle),∃ i : s,φ i.1 z.1=1 := by
    filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU]
      with z hz
    have hzK : (z.1 : Cover)∈K := ⟨z.1.property,hz⟩
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hs hzK)
    have hi1 : (z.1 : Cover)∈{y : Cover | φ i y=1} := interior_subset hzi
    exact ⟨⟨i,hi⟩,hi1⟩
  exact finite_normal_patch_gluing (fun i : s ↦ φ i.1) (fun i : s ↦ N i.1)
    (fun i ↦ hφ i.1) (fun i ↦ hN i.1) (fun i ↦ hφp i.1) (fun i ↦ hNp i.1)
    (fun i ↦ hφn i.1) hcover (fun i ↦ hae i.1)

namespace Periodic

theorem isMinimizerAt_global_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,hμ,hs⟩ := isMinimizerAt_normal_CMC_stability hV hE hmin
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hmin hμ
  obtain ⟨hH,hstab⟩ := hs N hN hp hn
  refine ⟨μ,H,N,hμ,hN,hp,?_,hstab⟩
  filter_upwards [hn,hH] with z hz he
  exact ⟨hz.1,hz.2,he⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem continuous_periodic_descent {Y : Type*} [TopologicalSpace Y]
    {F : Cover → Y} (hF : Continuous F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    Continuous (fun a : Torus ↦ F (representative a)) := by
  let q : CompactCell → Torus := fun z ↦ quotientMap z
  have hq : Continuous q := continuous_quotientMap.comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro a
    exact ⟨cubeRepresentative a,quotientMap_representative a⟩
  apply (hq.isClosedMap.isQuotientMap hq hs).continuous_iff.mpr
  have he : (fun a : Torus ↦ F (representative a)) ∘ q = fun z : CompactCell ↦ F z := by
    funext z
    exact periodic_representative hp z
  rw [he]
  exact hF.comp continuous_subtype_val

theorem isMinimizerAt_periodic_ae_eq_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {F G : Cover → Y} (hF : Continuous F) (hG : Continuous G)
    (hpF : ∀ m x,F (x+latticeVector m)=F x)
    (hpG : ∀ m x,G (x+latticeVector m)=G x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),F z.1=G z.1)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : F x=G x := by
  let S : Set Torus := {a | F (representative a)=G (representative a)}
  have hS : IsClosed S := isClosed_eq (continuous_periodic_descent hF hpF)
    (continuous_periodic_descent hG hpG)
  have hm : S∈ae (spatialNormalMeasure μ : Measure Torus) := by
    change ∀ᵐ a ∂Measure.map normalProjection (μ : Measure NormalBundle),a∈S
    apply (ae_map_iff normalProjection_continuous.measurable.aemeasurable hS.measurableSet).mpr
    filter_upwards [hae] with z hz
    change F (representative (quotientMap z.1))=G (representative (quotientMap z.1))
    simpa only [periodic_representative hpF,periodic_representative hpG] using hz
  have hh := Measure.support_subset_of_isClosed hS hm
  rw [isMinimizerAt_perimeter_support hV hE hmin hμ] at hh
  have he := hh hx
  change F (representative (quotientMap x))=G (representative (quotientMap x)) at he
  simpa only [periodic_representative hpF,periodic_representative hpG] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_normal_graph_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,_,_⟩ :=
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
    have hpp : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right]
      have hnorm : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR (hφU hx)
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt (hnorm.trans hRr)
    have he : f=ᶠ[𝓝 (normalPlaneCoordinates n (x-cubeCenter))]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hpp] with y hy
      exact hfg hy
    simp only [graphUnitNormalExtension,gradient,he.fderiv_eq]
  have hsign : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
        σ • graphUnitNormalExtension cubeCenter n f z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨1,Or.inl rfl,?_⟩
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hh
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [one_smul,hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hh' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hh
      have hh'' := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hh' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh''
      refine ⟨-1,Or.inr rfl,?_⟩
      filter_upwards [hm] with z hz hpos
      rw [neg_one_smul,hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨σ,hσ,hσae⟩ := hsign
  let F : Cover → Cover := fun x ↦ φ x • (σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ)
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0≤cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have heφ := latticePeriodize_eventuallyEq hsφ hφO
    (show ∀ coordinate,0≤cubeCenter coordinate ∧ cubeCenter coordinate≤1 by
      intro coordinate
      norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),
      latticePeriodize φ z.1 • N z.1=latticePeriodize F z.1 := by
    filter_upwards [hae,hσae] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsφ hφO (compactCell_coordinates z.1)).eq_of_nhds,
      (latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • N z.1=φ z.1 • (σ • graphUnitNormalExtension cubeCenter n f z.1)
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      simp only [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize φ x • N x=latticePeriodize F x :=
    isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      ((latticePeriodize_contDiff hφ hsφ).continuous.smul hN.continuous)
      (latticePeriodize_contDiff hF hsF).continuous
      (fun shift point ↦ congrArg₂ (· • ·)
        (latticePeriodize_periodic φ shift point) (hp shift point))
      (latticePeriodize_periodic F) hz x hx
  have hf0 : f 0=0 := (hfg (by simpa using (half_pos hr))).trans hg0
  have ht : Tendsto (fun y ↦ cubeCenter+normalGraph n f y) (𝓝 (0 : Plane)) (𝓝 cubeCenter) := by
    have hc : Continuous (fun y ↦ cubeCenter+normalGraph n f y) :=
      continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
        (hf.continuous.smul continuous_const))
    have hz : cubeCenter+normalGraph n f 0=cubeCenter := by
      simp only [normalGraph,hf0,zero_smul,add_zero]
      change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
      rw [map_zero,add_zero]
    simpa only [ContinuousAt,hz] using hc.continuousAt (x := 0)
  have hone : ∀ᶠ x in 𝓝 cubeCenter,φ x=1 := by
    filter_upwards [Metric.ball_mem_nhds cubeCenter hρ] with x hx
    exact radialHeightCutoff_one hρ (Metric.ball_subset_closedBall hx)
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_⟩
  ·
    filter_upwards [ht.eventually he,ht.eventually heφ,ht.eventually hone,
      Metric.ball_mem_nhds (0 : Plane) (half_pos hr)] with y hey heφy hoy hy
    have hgraph : normalGraph n f y=normalGraph n g y := by simp only [normalGraph,hfg hy]
    have hby : quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
      rw [quotientMap_add,hgraph]
      exact hi y ((Metric.ball_subset_ball (by linarith)) hy)
    have hnormal := hb _ hby
    rw [heφy,hey] at hnormal
    change φ (cubeCenter+normalGraph n f y) • N (cubeCenter+normalGraph n f y)=
      φ (cubeCenter+normalGraph n f y) • (σ • graphUnitNormalExtension cubeCenter n f
        (cubeCenter+normalGraph n f y)) at hnormal
    simp only [hoy,one_smul,graphUnitNormalExtension_graph cubeCenter hn f f y] at hnormal
    exact ⟨hnormal,hby⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Cover) (half_pos hr)] with v hv
    have hpv : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right] at hv ⊢
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt hv
    rw [hcover' v hv]
    simp only [normalGraph,hfg hpv]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_boundary_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        ‖N x‖=1 ∧ divergence N x=H) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hs⟩ := isMinimizerAt_global_normal_stability hV hE hmin
  refine ⟨μ,H,N,hμ,hN,hp,?_,?_,hs⟩
  · filter_upwards [hae] with z hz
    exact ⟨hz.1,hz.2.1⟩
  · intro x hx
    constructor
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hN.continuous.norm
        continuous_const (fun m y ↦ by rw [hp]) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hae] with z hz
      rw [hz.1,z.2.property]
    · apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ (continuous_divergence hN)
        continuous_const (divergence_periodic hp) (fun _ _ ↦ rfl) _ x hx
      filter_upwards [hae] with z hz
      exact hz.2.2

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_eventuallyEq {N : Cover → Cover} {x : Cover}
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) : regularizedNormal N=ᶠ[𝓝 x]N := by
  filter_upwards [hu] with y hy
  rw [regularizedNormal_eq (by rw [hy]; norm_num),hy,inv_one,one_smul]

namespace Periodic

theorem isMinimizerAt_tubular_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hboundary,hs⟩ := isMinimizerAt_boundary_normal_stability hV hE hmin
  have hR := regularizedNormal_contDiff hN
  have hrp : ∀ m x,regularizedNormal N (x+latticeVector m)=regularizedNormal N x := by
    intro m x
    simp only [regularizedNormal,hp]
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),
      regularizedNormal N=ᶠ[𝓝 (z.1 : Cover)]N := by
    filter_upwards [hae] with z hz
    exact regularizedNormal_eventuallyEq hz.2
  refine ⟨μ,H,regularizedNormal N,hμ,hR,hrp,?_,?_,?_⟩
  · filter_upwards [hae,he] with z hz hze
    exact hze.eq_of_nhds.trans hz.1
  · intro x hx
    refine ⟨regularizedNormal_unit_near hN.continuous (by rw [(hboundary x hx).1]; norm_num),?_⟩
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_divergence hR) (continuous_divergence hN)
      (divergence_periodic hrp) (divergence_periodic hp) _ x hx |>.trans (hboundary x hx).2
    filter_upwards [he] with z hz
    simp only [divergence_eq_coverTrace,hz.fderiv_eq]
  · intro f hf hfp hz
    have hq : normalExtensionJacobi μ f (regularizedNormal N)=normalExtensionJacobi μ f N := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      simp only [hz.fderiv_eq]
    rw [hq]
    exact hs f hf hfp hz

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_graph_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    dsimp [a]
    congr 1
    abel
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
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov⟩ := actual_centered_normal_graph_chart hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  have ht (v : Cover) : (cubeCenter+v)+a=x+v := by dsimp [a]; abel
  have htrans (v : Cover) : quotientMap (cubeCenter+v)∈frontier (openRepresentative E') ↔
      quotientMap (x+v)∈frontier (openRepresentative E) := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap (cubeCenter+v)+quotientMap a∈frontier (openRepresentative E) ↔ _
    rw [← quotientMap_add,ht]
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_⟩
  · filter_upwards [hm] with y hy
    refine ⟨?_,(htrans _).mp hy.2⟩
    have hh := hy.1
    change N ((cubeCenter+normalGraph n f y)+a)=_ at hh
    rwa [ht] at hh
  · filter_upwards [hcov] with v hv
    exact (htrans v).symm.trans hv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.classical_zero {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hU : IsOpen U)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U) :
    ∀ y∈U,planeDivergence (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) y=0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) :=
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)).clm_apply (plane_gradient_contDiff hf)
  have ht := classical_divergence_of_weak (H := 0) (hF.of_le (by simp)) hU
    (fun ψ hψ hc hs ↦ by simpa only [sub_zero,zero_mul] using hw ψ hψ hc hs)
  simpa only [neg_zero] using ht

theorem plane_weight_harmonic_potential {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (y : Plane)
    (hz : ∀ i : Fin 2,planeDivergence (fun z ↦ A z (gradient (fun w ↦ p w i) z)) y=0) :
    planeDivergence (fun z ↦ A z (gradient (fun w ↦ cmcWeight (p w)) z)) y=
      (⟪gradient (fun w ↦ p w 0) y,A y (gradient (fun w ↦ p w 0) y)⟫+
        ⟪gradient (fun w ↦ p w 1) y,A y (gradient (fun w ↦ p w 1) y)⟫-
        ⟪gradient (fun w ↦ cmcWeight (p w)) y,A y (gradient (fun w ↦ cmcWeight (p w)) y)⟫)/
        cmcWeight (p y) := by
  let q : Plane → ℝ := fun z ↦ cmcWeight (p z)
  let u : Fin 2 → Plane → ℝ := fun i z ↦ p z i
  let F : Fin 2 → Plane → Plane := fun i z ↦ A z (gradient (u i) z)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp hp
  have hu (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (u i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hp
  have hF (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (F i) := hA.clm_apply (plane_gradient_contDiff (hu i))
  have hquot (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ u i z/q z) :=
    (hu i).div hq (fun z ↦ (cmcWeight_pos _).ne')
  have hprod (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (u i z/q z) • F i z) :=
    (hquot i).smul (hF i)
  have hfield : (fun z ↦ A z (gradient q z))=
      (fun z ↦ (u 0 z/q z) • F 0 z+(u 1 z/q z) • F 1 z) := by
    funext z
    rw [plane_gradient_weight hp]
    simp only [F,u,q,map_smul,map_add,smul_add,smul_smul,div_eq_mul_inv]
    congr 1 <;> congr 1 <;> ring
  change planeDivergence (fun z ↦ A z (gradient q z)) y=_
  rw [hfield,planeDivergence_add
    ((hprod 0).differentiable (by simp) y)
    ((hprod 1).differentiable (by simp) y),
    planeDivergence_smul ((hquot 0).differentiable (by simp) y) ((hF 0).differentiable (by simp) y),
    planeDivergence_smul ((hquot 1).differentiable (by simp) y) ((hF 1).differentiable (by simp) y)]
  have hz' (i : Fin 2) : planeDivergence (F i) y=0 := hz i
  rw [hz' 0,hz' 1,mul_zero,mul_zero,zero_add,zero_add,
    plane_gradient_div ((hu 0).differentiable (by simp) y) (hq.differentiable (by simp) y) (cmcWeight_pos _).ne',
    plane_gradient_div ((hu 1).differentiable (by simp) y) (hq.differentiable (by simp) y) (cmcWeight_pos _).ne']
  have he := congrArg (fun v : Plane ↦ ⟪gradient q y,A y v⟫) (plane_gradient_weight hp y)
  change ⟪gradient q y,A y (gradient q y)⟫=_ at he
  simp only [map_smul,map_add,inner_smul_right,inner_add_right] at he
  change _=(⟪gradient (u 0) y,F 0 y⟫+⟪gradient (u 1) y,F 1 y⟫-
    ⟪gradient q y,A y (gradient q y)⟫)/q y
  rw [he]
  simp only [inner_sub_left,real_inner_smul_left]
  dsimp only [F,u,q]
  field_simp [(cmcWeight_pos (p y)).ne']
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphInverseMetric (p : Plane) : Plane →L[ℝ] Plane :=
  cmcWeight p • cmcJacobian p

lemma graphInverseMetric_identity (p v w : Plane) :
    ⟪graphInverseMetric p v,w⟫+⟪p,graphInverseMetric p v⟫*⟪p,w⟫=⟪v,w⟫ := by
  simp only [graphInverseMetric,smul_apply,real_inner_smul_left,inner_smul_right]
  rw [cmcJacobian_inner_slope,cmcJacobian_apply]
  simp only [inner_sub_left,real_inner_smul_left]
  field_simp [(cmcWeight_pos p).ne']
  ring

def graphTangentialGradient (n : Cover) (g φ : Plane → ℝ) (y : Plane) : Cover :=
  fderiv ℝ (normalGraph n g) y (graphInverseMetric (gradient g y) (gradient φ y))

lemma graphTangentialGradient_duality {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (φ : Plane → ℝ) (y v : Plane) :
    ⟪graphTangentialGradient n g φ y,fderiv ℝ (normalGraph n g) y v⟫=
      fderiv ℝ φ y v := by
  rw [graphTangentialGradient,normalGraph_metric hn hg,graphInverseMetric_identity,
    inner_gradient_left]

lemma graphTangentialGradient_inner {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (φ ψ : Plane → ℝ) (y : Plane) :
    ⟪graphTangentialGradient n g φ y,graphTangentialGradient n g ψ y⟫=
      cmcWeight (gradient g y)*⟪gradient φ y,cmcJacobian (gradient g y) (gradient ψ y)⟫ := by
  unfold graphTangentialGradient
  rw [normalGraph_metric hn hg,graphInverseMetric_identity]
  simp only [graphInverseMetric,smul_apply,inner_smul_right]

lemma cmc_graph_curvature_potential {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hU : IsOpen U)
    (hw : ∀ i : Fin 2,LinearCMCEquation
      (fun y ↦ fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ ↦ 0) U)
    {y : Plane} (hy : y∈U) :
    planeDivergence (fun z ↦ cmcJacobian (gradient g z)
      (gradient (fun w ↦ cmcWeight (gradient g w)) z)) y=
        graphSquaredSecondFundamentalForm g y := by
  rw [graphSquaredSecondFundamentalForm_formula hg]
  apply plane_weight_harmonic_potential (plane_gradient_contDiff hg)
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg))
  intro i
  simp_rw [plane_gradient_component]
  exact (hw i).classical_zero hg
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const) hU y hy

theorem cmcGraphJacobi_geometric {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {U : Set Plane} (hU : IsOpen U)
    (hw : ∀ i : Fin 2,LinearCMCEquation
      (fun y ↦ fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ ↦ 0) U)
    (φ ψ : Plane → ℝ) (hs : tsupport ψ⊆U) :
    cmcGraphJacobi g φ ψ=
      ∫ y,cmcWeight (gradient g y)*
        (⟪graphTangentialGradient n g φ y,graphTangentialGradient n g ψ y⟫-
          graphSquaredSecondFundamentalForm g y*φ y*ψ y) := by
  unfold cmcGraphJacobi graphJacobiForm
  apply integral_congr_ae
  filter_upwards [] with y
  rw [graphTangentialGradient_inner hn hg]
  by_cases hy : y∈U
  · rw [cmc_graph_curvature_potential hg hU hw hy]
    ring
  · have hψ : ψ y=0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (hs h))
    rw [hψ]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphInverseMetric_slope (p q : Plane) (c : ℝ) :
    graphInverseMetric p (q+c • p)=q+
      ((c-⟪p,q⟫)/(cmcWeight p)^2) • p := by
  rw [graphInverseMetric,smul_apply,cmcJacobian_apply]
  simp only [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,smul_sub,smul_smul,
    mul_inv_cancel₀ (cmcWeight_pos p).ne',one_smul]
  have he : c-cmcWeight p*(((cmcWeight p)^3)⁻¹*(⟪p,q⟫+c*‖p‖^2))=
      (c-⟪p,q⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ c*r) (cmcWeight_sq p)]
  rw [add_sub_assoc,← sub_smul,he]

lemma graph_metric_projection {n : Cover} (hn : ‖n‖=1) (p : Plane) (v : Cover) :
    normalPlaneEmbedding n (graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p))+
      ⟪p,graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p)⟫ • n=
        v-⟪graphSlopeNormal n p,v⟫ • graphSlopeNormal n p := by
  have he : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  have hi : ⟪graphSlopeNormal n p,v⟫=(cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫) := by
    rw [graphSlopeNormal_weight hn,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
  have hc : ⟪p,normalPlaneCoordinates n v⟫+
      ((⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2)*‖p‖^2=
        ⟪n,v⟫-(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*r) (cmcWeight_sq p)]
  rw [graphInverseMetric_slope,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hc,
    he,map_add,map_smul,hi,graphSlopeNormal_weight hn]
  have hr := normalPlaneCoordinates_reconstruct hn v
  change (normalPlaneLinearIsometry n).toContinuousLinearMap (normalPlaneCoordinates n v)+⟪n,v⟫ • n=v at hr
  conv_rhs => lhs; rw [← hr]

  have hq : (cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*(cmcWeight p)⁻¹=
      (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp
  simp only [smul_smul,smul_sub,hq,sub_smul,he]
  module

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_trace_square_invariance {n : Cover} (hn : ‖n‖=1)
    {D B : Cover →L[ℝ] Cover}
    (hD : ∀ v,⟪n,D v⟫=0) (hB : ∀ v,⟪n,B v⟫=0)
    (ht : ∀ v,⟪n,v⟫=0 → D v=B v) :
    coverTrace (D.comp D)=coverTrace (B.comp B) := by
  let w := D n-B n
  let R : Cover →L[ℝ] Cover := (innerSL ℝ n).smulRight w
  have hw : ⟪n,w⟫=0 := by rw [inner_sub_right,hD,hB,sub_self]
  have he : D=B+R := by
    apply ContinuousLinearMap.ext
    intro v
    have htv : ⟪n,v-⟪n,v⟫ • n⟫=0 := by
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
    change D v=B v+⟪n,v⟫ • (D n-B n)
    calc
      D v=D (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [map_sub,map_smul]; module
      _=B (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [ht _ htv]
      _=_ := by rw [map_sub,map_smul]; module
  have hBR : B.comp R=(innerSL ℝ n).smulRight (B w) := by
    apply ContinuousLinearMap.ext
    intro v
    exact map_smul B _ _
  have hRR : R.comp R=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change ⟪n,⟪n,v⟫ • w⟫ • w=0
    rw [real_inner_smul_right,hw,mul_zero,zero_smul]
  have hbr : coverTrace (B.comp R)=0 := by rw [hBR,coverTrace_smulRight]; exact hB w
  have hrb : coverTrace (R.comp B)=0 := by rw [coverTrace_comp_comm,hbr]
  rw [he,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add,coverTrace_add,coverTrace_add,coverTrace_add,hbr,hrb,hRR,
    coverTrace_zero,add_zero,zero_add,add_zero]

theorem graph_normal_extension_curvature (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hu : ∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    (hmatch : ∀ᶠ z in 𝓝 y,N (a+normalGraph n g z)=σ • graphSlopeNormal n (gradient g z)) :
    coverTrace ((fderiv ℝ N (a+normalGraph n g y)).comp
      (fderiv ℝ N (a+normalGraph n g y)))=graphSquaredSecondFundamentalForm g y := by
  let x := a+normalGraph n g y
  let K : Cover → Cover := fun v ↦ σ • graphUnitNormalExtension a n g v
  have hK : ContDiff ℝ (⊤ : ℕ∞) K :=
    (graphUnitNormalExtension_contDiff a hn hg).const_smul σ
  have hKu (v : Cover) : ‖K v‖=1 := by
    rcases hσ with rfl|rfl
    · simpa only [K,one_smul] using graphUnitNormalExtension_unit a hn g v
    · simpa only [K,neg_one_smul,norm_neg] using graphUnitNormalExtension_unit a hn g v
  have hm : (fun z ↦ N (a+normalGraph n g z))=ᶠ[𝓝 y](fun z ↦ K (a+normalGraph n g z)) := by
    filter_upwards [hmatch] with z hz
    simpa only [K,graphUnitNormalExtension_graph a hn g g z] using hz
  have hNx : N x=K x := hm.eq_of_nhds
  have hdN := smooth_unit_normal_derivative (hN.differentiable (by simp) x) hu
  have hdK := smooth_unit_normal_derivative (hK.differentiable (by simp) x)
    (Filter.Eventually.of_forall hKu)
  have hnD (v : Cover) : ⟪N x,fderiv ℝ N x v⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hdN,inner_zero_left]
  have hnB (v : Cover) : ⟪N x,fderiv ℝ K x v⟫=0 := by
    rw [hNx,← ContinuousLinearMap.adjoint_inner_left,hdK,inner_zero_left]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have hdmatch := hm.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (N ∘ fun z ↦ a+normalGraph n g z) y=
    fderiv ℝ (K ∘ fun z ↦ a+normalGraph n g z) y at hdmatch
  rw [((hN.differentiable (by simp) x).hasFDerivAt.comp y hΦ).fderiv,
    ((hK.differentiable (by simp) x).hasFDerivAt.comp y hΦ).fderiv] at hdmatch
  have ht (v : Cover) (hv : ⟪N x,v⟫=0) : fderiv ℝ N x v=fderiv ℝ K x v := by
    have hv' : ⟪graphSlopeNormal n (gradient g y),v⟫=0 := by
      rw [hNx] at hv
      change ⟪σ • graphUnitNormalExtension a n g x,v⟫=0 at hv
      rw [graphUnitNormalExtension_graph a hn g g y,real_inner_smul_left] at hv
      rcases hσ with rfl|rfl <;> simpa using hv
    let q := graphInverseMetric (gradient g y)
      (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
    have hvq : fderiv ℝ (normalGraph n g) y q=v := by
      rw [normalGraph_fderiv_apply hg]
      rw [graph_metric_projection hn,hv',zero_smul,sub_zero]
    have he := congrArg (fun L : Plane →L[ℝ] Cover ↦ L q) hdmatch
    simp only [ContinuousLinearMap.comp_apply] at he
    rw [← hvq]
    exact he
  rw [normal_trace_square_invariance (hu.self_of_nhds) hnD hnB ht]
  have hpot : coverTrace ((fderiv ℝ K x).comp (fderiv ℝ K x))=
      coverTrace ((fderiv ℝ (graphUnitNormalExtension a n g) x).comp
        (fderiv ℝ (graphUnitNormalExtension a n g) x)) := by
    rcases hσ with rfl|rfl
    · simp only [K,one_smul]
    · simp only [K,neg_one_smul]
      change coverTrace ((fderiv ℝ (-graphUnitNormalExtension a n g) x).comp
        (fderiv ℝ (-graphUnitNormalExtension a n g) x))=_
      rw [fderiv_neg,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,neg_neg]
  rw [hpot,graphUnitNormalExtension_curvature a hn hg]
  simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_trace_invariance {n : Cover} (hn : ‖n‖=1)
    {D B : Cover →L[ℝ] Cover}
    (hD : ∀ v,⟪n,D v⟫=0) (hB : ∀ v,⟪n,B v⟫=0)
    (ht : ∀ v,⟪n,v⟫=0 → D v=B v) :
    coverTrace D=coverTrace B := by
  let w := D n-B n
  let R : Cover →L[ℝ] Cover := (innerSL ℝ n).smulRight w
  have hw : ⟪n,w⟫=0 := by rw [inner_sub_right,hD,hB,sub_self]
  have he : D=B+R := by
    apply ContinuousLinearMap.ext
    intro v
    have htv : ⟪n,v-⟪n,v⟫ • n⟫=0 := by
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
    change D v=B v+⟪n,v⟫ • (D n-B n)
    calc
      D v=D (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [map_sub,map_smul]; module
      _=B (v-⟪n,v⟫ • n)+⟪n,v⟫ • D n := by rw [ht _ htv]
      _=_ := by rw [map_sub,map_smul]; module
  rw [he,coverTrace_add,coverTrace_smulRight]
  rw [innerSL_apply_apply,hw,add_zero]

end CubicTorus
end
end
end

end OAI
