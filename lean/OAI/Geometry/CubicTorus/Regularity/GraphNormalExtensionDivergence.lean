import Mathlib
import OAI.Geometry.CubicTorus.Estimates.GraphInverseMetric

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem graph_normal_extension_divergence (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hu : ∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    (hmatch : ∀ᶠ z in 𝓝 y,N (a+normalGraph n g z)=σ • graphSlopeNormal n (gradient g z)) :
    divergence N (a+normalGraph n g y)=
      -σ * planeDivergence (fun z ↦ cmcFlux (gradient g z)) y := by
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
  rw [divergence_eq_coverTrace]
  change coverTrace (fderiv ℝ N x)=_
  rw [normal_trace_invariance (hu.self_of_nhds) hnD hnB ht]
  have he : coverTrace (fderiv ℝ K x)=σ * divergence (graphUnitNormalExtension a n g) x := by
    rw [divergence_eq_coverTrace]
    rcases hσ with rfl|rfl
    · simp only [K,one_smul,one_mul]
    · simp only [K,neg_one_smul]
      change coverTrace (fderiv ℝ (-graphUnitNormalExtension a n g) x)=_
      rw [fderiv_neg]
      simp only [coverTrace,neg_apply,PiLp.neg_apply,
        Finset.sum_neg_distrib,neg_one_mul]
  rw [he,graphUnitNormalExtension_divergence a hn hg]
  simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_normal_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) := by
  obtain ⟨normal,height,sign,hnormal,hheight,hzero,hsign,hmatch,_⟩ :=
    actual_centered_normal_graph_chart hV hE hmin hcenter hμ hN hp hae
  exact ⟨normal,height,sign,hnormal,hheight,hzero,hsign,hmatch.mono fun _ hpoint ↦ hpoint.1⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      ∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) := by
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
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm⟩ := actual_centered_normal_geometry hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_⟩
  filter_upwards [hm] with y hy
  change N ((cubeCenter+normalGraph n f y)+a)=_ at hy
  have he : (cubeCenter+normalGraph n f y)+a=x+normalGraph n f y := by dsimp [a]; abel
  rwa [he] at hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_curvature_nonnegative {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    0≤coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)) := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm⟩ :=
    isMinimizerAt_normal_geometry hV hE hmin hμ hN hp hae x hx
  have hx0 : x+normalGraph n f 0=x := by
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simp [normalGraph,hf0,hz]
  have he := graph_normal_extension_curvature x hn hf (0 : Plane) hσ hN
    (by simpa only [hx0] using hu) hm
  rw [hx0] at he
  rw [he]
  exact (graph_curvature_nonnegative hf 0).1

namespace Periodic

theorem isMinimizerAt_curvature_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0≤coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs⟩ := isMinimizerAt_tubular_normal_stability hV hE hmin
  refine ⟨μ,H,N,hμ,hN,hp,hae,?_,hs⟩
  intro x hx
  exact ⟨(hb x hx).1,(hb x hx).2,
    isMinimizerAt_normal_curvature_nonnegative hV hE hmin hμ hN hp hae x hx (hb x hx).1⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localRadialSquared_lt_iff (a : Torus) (x : Cover) {r : ℝ}
    (hr : 0≤r) (hs : r≤1/4) :
    localRadialSquared a x<r^2 ↔ quotientMap x∈Metric.ball a r := by
  have he := periodic_representative (localRadialSquared_periodic a) x
  rw [← he]
  change quotientMap x∈sublevelRegion (localRadialSquared a) (r^2) ↔ _
  rw [sublevelRegion_localRadialSquared a hr hs]

theorem exists_periodic_local_cutoff (a : Torus) {U : Set Torus}
    (hU : IsOpen U) (ha : a∈U) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧ (∀ x,φ x∈Icc 0 1) ∧
      (∃ W : Set Torus,IsOpen W ∧ a∈W ∧
        ∀ x,quotientMap x∈W → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0 := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min (ε/4) (1/8 : ℝ)
  have hr : 0<r := lt_min (by positivity) (by norm_num)
  have hrsmall : 2*r≤1/4 := by dsimp [r]; linarith [min_le_right (ε/4) (1/8 : ℝ)]
  have hrε : 2*r<ε := by dsimp [r]; linarith [min_le_left (ε/4) (1/8 : ℝ)]
  let q := localRadialSquared a
  let φ : Cover → ℝ := fun x ↦ Real.smoothTransition ((r^2-q x)/(r^2/2))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := localRadialSquared_contDiff a
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const _)
  have hden : 0<r^2/2 := by positivity
  refine ⟨φ,hφ,?_,?_,?_,?_⟩
  · intro m x
    simp only [φ,q,localRadialSquared_periodic]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · refine ⟨Metric.ball a (r/2),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro x hx
    have hxq : q x<(r/2)^2 := (localRadialSquared_lt_iff a x (by positivity) (by linarith)).mpr hx
    have hn : ∀ᶠ y in 𝓝 x,q y<r^2/2 := hq.continuous.continuousAt.eventually_lt_const (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  · intro x hx
    have hnot : quotientMap x∉Metric.ball a (2*r) := fun hh ↦ hx (hεU (Metric.ball_subset_ball hrε.le hh))
    have hxq : (2*r)^2≤q x := le_of_not_gt (fun hh ↦ hnot ((localRadialSquared_lt_iff a x (by positivity) hrsmall).mp hh))
    have hn : ∀ᶠ y in 𝓝 x,r^2<q y := hq.continuous.continuousAt.eventually_const_lt (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

theorem exists_periodic_smooth_separator {A B : Set Torus} (hA : IsCompact A)
    (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧
      (∀ x,φ x∈Icc 0 1) ∧
      (∀ x,quotientMap x∈A → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      (∀ x,quotientMap x∈B → ∀ᶠ y in 𝓝 x,φ y=0) := by
  classical
  have hcut (a : A) := exists_periodic_local_cutoff a.1 hB.isOpen_compl
    (show a.1∈Bᶜ from fun hb ↦ Set.disjoint_left.mp hAB a.2 hb)
  choose φ hφ hp hb hW0 hzero using hcut
  choose W hW hWa hone using hW0
  obtain ⟨s,hs⟩ := hA.elim_finite_subcover W hW (fun a ha ↦ mem_iUnion.mpr ⟨⟨a,ha⟩,hWa ⟨a,ha⟩⟩)
  let ψ : Cover → ℝ := fun x ↦ 1-∏ a∈s,(1-φ a x)
  refine ⟨ψ,contDiff_const.sub (contDiff_prod (fun a _ ↦ contDiff_const.sub (hφ a))),?_,?_,?_,?_⟩
  · intro m x
    simp only [ψ,hp]
  · intro x
    have hn : 0≤∏ a∈s,(1-φ a x) := Finset.prod_nonneg fun a _ ↦ sub_nonneg.mpr (hb a x).2
    have hu : (∏ a∈s,(1-φ a x))≤1 := Finset.prod_le_one₀ (fun a _ ↦ sub_nonneg.mpr (hb a x).2)
      (fun a _ ↦ by linarith [(hb a x).1])
    exact ⟨by dsimp [ψ]; linarith,by dsimp [ψ]; linarith⟩
  · intro x hx
    obtain ⟨a,has,hxa⟩ := mem_iUnion₂.mp (hs hx)
    filter_upwards [hone a x hxa] with y hy
    dsimp [ψ]
    rw [Finset.prod_eq_zero has (by rw [hy,sub_self]),sub_zero]
  · intro x hx
    have hn : ∀ᶠ y in 𝓝 x,∀ a∈s,φ a y=0 := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro a ha
      exact hzero a x (by simpa using hx)
    filter_upwards [hn] with y hy
    dsimp [ψ]
    have he : (∏ a∈s,(1-φ a y))=1 := Finset.prod_eq_one (fun a ha ↦ by rw [hy a ha,sub_zero])
    rw [he,sub_self]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_normal_base {F : Cover → ℝ} (hF : Continuous F)
    (μ : FiniteMeasure NormalBundle) :
    Integrable (fun z : NormalBundle ↦ F z.1) (μ : Measure NormalBundle) :=
  (hF.comp normalEmbedding_continuous.fst).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma normal_curvature_continuous {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    Continuous (fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) :=
  coverTraceCLM.continuous.comp ((hN.continuous_fderiv (by simp)).clm_comp
    (hN.continuous_fderiv (by simp)))

theorem separated_boundary_curvature_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hq : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      0≤coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)))
    (hs : ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ m x,f (x+latticeVector m)=f x) →
      (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 → 0≤normalExtensionJacobi μ f N)
    {A B : Set Torus} (hA : IsClosed A) (hB : IsClosed B)
    (ha : A.Nonempty) (hb : B.Nonempty) (hAB : Disjoint A B)
    (hK : A∪B=frontier (openRepresentative E)) :
    ∀ x,quotientMap x∈frontier (openRepresentative E) →
      coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0 := by
  obtain ⟨φ,hφ,hp,hbφ,hφA,hφB⟩ := exists_periodic_smooth_separator hA.isCompact hB hAB
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hi := integrable_normal_base hφ.continuous μ
  have hj : Integrable (fun z : NormalBundle ↦ 1-φ z.1) (μ : Measure NormalBundle) :=
    integrable_normal_base (continuous_const.sub hφ.continuous) μ
  let I := ∫ z,φ z.1 ∂(μ : Measure NormalBundle)
  let J := ∫ z,1-φ z.1 ∂(μ : Measure NormalBundle)
  have hI0 : 0≤I := integral_nonneg fun z ↦ (hbφ z.1).1
  have hJ0 : 0≤J := integral_nonneg fun z ↦ sub_nonneg.mpr (hbφ z.1).2
  have hI : 0<I := by
    apply lt_of_le_of_ne hI0
    intro he
    have heae : ∀ᵐ z ∂(μ : Measure NormalBundle),φ z.1=0 :=
      (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle ↦ (hbφ z.1).1) hi).mp he.symm
    obtain ⟨a,ha⟩ := ha
    have hax : quotientMap (representative a)∈frontier (openRepresentative E) := by
      rw [quotientMap_representative,← hK]; exact Or.inl ha
    have hz := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous continuous_const
      hp (fun _ _ ↦ rfl) heae (representative a) hax
    have ho := (hφA (representative a) (by rwa [quotientMap_representative])).self_of_nhds
    linarith
  have hJ : 0<J := by
    apply lt_of_le_of_ne hJ0
    intro he
    have heae : ∀ᵐ z ∂(μ : Measure NormalBundle),1-φ z.1=0 :=
      (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle ↦ sub_nonneg.mpr (hbφ z.1).2) hj).mp he.symm
    obtain ⟨b,hb⟩ := hb
    have hbx : quotientMap (representative b)∈frontier (openRepresentative E) := by
      rw [quotientMap_representative,← hK]; exact Or.inr hb
    have hz := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (continuous_const.sub hφ.continuous) continuous_const
      (fun m x ↦ by simp only [Pi.sub_apply,hp]) (fun _ _ ↦ rfl) heae (representative b) hbx
    have ho := (hφB (representative b) (by rwa [quotientMap_representative])).self_of_nhds
    change 1-φ (representative b)=0 at hz
    linarith
  let c := I/(I+J)
  have hM : 0<I+J := add_pos hI hJ
  have hc0 : 0<c := div_pos hI hM
  have hc1 : c<1 := (div_lt_one hM).mpr (by linarith)
  have hmass : (μ : Measure NormalBundle).real univ=I+J := by
    have he : (μ : Measure NormalBundle).real univ=∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle) := by simp
    rw [he]
    rw [← integral_add hi hj]
    congr 1
    funext z
    ring
  let f : Cover → ℝ := fun x ↦ φ x-c
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hφ.sub contDiff_const
  have hfp : ∀ m x,f (x+latticeVector m)=f x := fun m x ↦ by dsimp [f]; rw [hp]
  have hfmean : (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 := by
    rw [show (fun z : NormalBundle ↦ f z.1)=(fun z ↦ φ z.1-c) from rfl,
      integral_sub hi (integrable_const _),integral_const,smul_eq_mul,hmass]
    change I-(I+J)*(I/(I+J))=0
    field_simp [hM.ne']
    ring
  have hfg : ∀ᵐ z ∂(μ : Measure NormalBundle),gradient f z.1=0 ∧ f z.1≠0 := by
    filter_upwards [hbd] with z hz
    rw [← hK] at hz
    change quotientMap z.1∈A∪B at hz
    rcases hz with hz|hz
    · have he : f=ᶠ[𝓝 (z.1 : Cover)] (fun _ ↦ 1-c) := by
        filter_upwards [hφA z.1 hz] with y hy
        dsimp [f]; rw [hy]
      refine ⟨?_,?_⟩
      · simp [gradient,he.fderiv_eq]
      · rw [he.self_of_nhds]; linarith
    · have he : f=ᶠ[𝓝 (z.1 : Cover)] (fun _ ↦ -c) := by
        filter_upwards [hφB z.1 hz] with y hy
        dsimp [f]; rw [hy,zero_sub]
      refine ⟨?_,?_⟩
      · simp [gradient,he.fderiv_eq]
      · rw [he.self_of_nhds]; exact neg_ne_zero.mpr hc0.ne'
  let q : Cover → ℝ := fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))
  have hqc : Continuous q := normal_curvature_continuous hN
  have hqp : ∀ m x,q (x+latticeVector m)=q x := by
    intro m x
    simp only [q,fderiv_periodic hpN]
  have hqae : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤q z.1 := by
    filter_upwards [hbd] with z hz
    exact hq z.1 hz
  have him := integrable_normal_base ((hf.continuous.pow 2).mul hqc) μ
  have hnn : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤(f z.1)^2*q z.1 := by
    filter_upwards [hqae] with z hz
    exact mul_nonneg (sq_nonneg _) hz
  have he : normalExtensionJacobi μ f N= -(∫ z,(f z.1)^2*q z.1 ∂(μ : Measure NormalBundle)) := by
    rw [normalExtensionJacobi,← integral_neg]
    apply integral_congr_ae
    filter_upwards [hfg] with z hz
    simp only [hz.1,inner_zero_right,zero_smul,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),zero_sub,q]
  have hint : (∫ z,(f z.1)^2*q z.1 ∂(μ : Measure NormalBundle))=0 := by
    have hh := hs f hf hfp hfmean
    rw [he] at hh
    exact le_antisymm (by linarith) (integral_nonneg_of_ae hnn)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn him).mp hint
  have hqzero : ∀ᵐ z ∂(μ : Measure NormalBundle),q z.1=0 := by
    filter_upwards [hzero,hfg] with z hz hfz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hfz.2)
  intro x hx
  exact isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hqc continuous_const
    hqp (fun _ _ ↦ rfl) hqzero x hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma closed_not_preconnected_split {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsClosed K) (hc : ¬IsPreconnected K) :
    ∃ A B : Set X,IsClosed A ∧ IsClosed B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A∪B=K := by
  rw [isPreconnected_closed_iff] at hc
  push Not at hc
  obtain ⟨A,B,hA,hB,hcov,ha,hb,hno⟩ := hc
  refine ⟨K∩A,K∩B,hK.inter hA,hK.inter hB,ha,hb,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hh : x∈K∩(A∩B) := ⟨hx.1,hx.2,hy.2⟩
    simp only [hno,Set.mem_empty_iff_false] at hh
  · ext x
    constructor
    · rintro (hx|hx) <;> exact hx.1
    · intro hx
      rcases hcov hx with hxa|hxb
      · exact Or.inl ⟨hx,hxa⟩
      · exact Or.inr ⟨hx,hxb⟩

namespace Periodic

theorem isMinimizerAt_connected_or_zero_curvature {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0≤coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N) ∧
      (IsPreconnected (frontier (openRepresentative E)) ∨
        ∀ x,quotientMap x∈frontier (openRepresentative E) →
          coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0) := by
  classical
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs⟩ := isMinimizerAt_curvature_stability hV hE hmin
  refine ⟨μ,H,N,hμ,hN,hp,hae,hb,hs,?_⟩
  by_cases hc : IsPreconnected (frontier (openRepresentative E))
  · exact Or.inl hc
  · obtain ⟨A,B,hA,hB,ha,hb',hd,hK⟩ := closed_not_preconnected_split isClosed_frontier hc
    exact Or.inr (separated_boundary_curvature_zero hV hE hmin hμ hN hp
      (fun x hx ↦ (hb x hx).2.2) hs hA hB ha hb' hd hK)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_mean_curvature_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    (divergence N x)^2≤2*coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)) := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm⟩ :=
    isMinimizerAt_normal_geometry hV hE hmin hμ hN hp hae x hx
  have hx0 : x+normalGraph n f 0=x := by
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simp [normalGraph,hf0,hz]
  have he := graph_normal_extension_curvature x hn hf (0 : Plane) hσ hN
    (by simpa only [hx0] using hu) hm
  have hm' := graph_normal_extension_divergence x hn hf (0 : Plane) hσ hN
    (by simpa only [hx0] using hu) hm
  rw [hx0] at he hm'
  rw [he,hm']
  rcases hσ with rfl|rfl <;> simpa only [neg_one_mul,neg_neg,one_mul,neg_sq] using
    (graph_curvature_nonnegative hf 0).2

namespace Periodic

theorem isMinimizerAt_connected_or_minimal_flat {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          H^2≤2*coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N) ∧
      (IsPreconnected (frontier (openRepresentative E)) ∨
        H=0 ∧ ∀ x,quotientMap x∈frontier (openRepresentative E) →
          coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0) := by
  classical
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs,hcf⟩ :=
    isMinimizerAt_connected_or_zero_curvature hV hE hmin
  have hbound (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      H^2≤2*coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)) := by
    rw [← (hb x hx).2.1]
    exact isMinimizerAt_mean_curvature_bound hV hE hmin hμ hN hp hae x hx (hb x hx).1
  refine ⟨μ,H,N,hμ,hN,hp,hae,fun x hx ↦ ⟨(hb x hx).1,(hb x hx).2.1,hbound x hx⟩,hs,?_⟩
  by_cases hc : IsPreconnected (frontier (openRepresentative E))
  · exact Or.inl hc
  · have hq := hcf.resolve_left hc
    obtain ⟨A,B,hA,hB,⟨a,ha⟩,hb',hd,hK⟩ := closed_not_preconnected_split isClosed_frontier hc
    have hxa : quotientMap (representative a)∈frontier (openRepresentative E) := by
      rw [quotientMap_representative,← hK]
      exact Or.inl ha
    have hh := hbound (representative a) hxa
    rw [hq _ hxa,mul_zero] at hh
    exact Or.inr ⟨by nlinarith [sq_nonneg H],hq⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_zero_curvature_locally_plane {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hq : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∃ m : Cover,‖m‖=1 ∧ ∀ᶠ v in 𝓝 (0 : Cover),
      quotientMap (a+v)∈frontier (openRepresentative E) ↔ ⟪m,v⟫=0 := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmin hμ hN hp hae a ha
  have hz : ∀ᶠ y in 𝓝 (0 : Plane),graphSquaredSecondFundamentalForm f y=0 := by
    filter_upwards [hm,hm.eventually_nhds] with y hy hym
    have he := graph_normal_extension_curvature a hn hf y hσ hN
      (hu _ hy.2) (hym.mono fun z hz ↦ hz.1)
    exact he.symm.trans (hq _ hy.2)
  obtain ⟨r,hr,hrz⟩ := Metric.mem_nhds_iff.mp hz
  have hfaff := graph_curvature_zero_affine hf hr (fun y hy ↦ hrz hy)
  refine ⟨graphSlopeNormal n (gradient f 0),graphSlopeNormal_unit hn _,?_⟩
  filter_upwards [hcov,Metric.ball_mem_nhds (0 : Cover) hr] with v hv hvr
  have hcoords : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) r := by
    rw [Metric.mem_ball,dist_zero_right] at hvr ⊢
    exact (normalPlaneCoordinates_norm_le _ _).trans_lt hvr
  rw [hv,normalGraph_coordinates_eq_iff hn,hfaff _ hcoords,hf0,zero_add]
  rw [graphSlopeNormal_weight hn,real_inner_smul_left,inner_sub_left,
    normalPlaneEmbedding_inner_coordinates hn,mul_eq_zero]
  simp only [inv_eq_zero,ne_of_gt (cmcWeight_pos _),false_or,sub_eq_zero]
  exact eq_comm

theorem isMinimizerAt_zero_curvature_local_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hq : ∀ x,quotientMap x∈frontier (openRepresentative E) →
      coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ‖N a‖=1 ∧ ∀ᶠ v in 𝓝 (0 : Cover),
      (quotientMap (a+v)∈frontier (openRepresentative E) ↔ ⟪N a,v⟫=0) ∧
      (quotientMap (a+v)∈frontier (openRepresentative E) → N (a+v)=N a) := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmin hμ hN hp hae a ha
  have hz : ∀ᶠ y in 𝓝 (0 : Plane),graphSquaredSecondFundamentalForm f y=0 := by
    filter_upwards [hm,hm.eventually_nhds] with y hy hym
    have he := graph_normal_extension_curvature a hn hf y hσ hN
      (hu _ hy.2) (hym.mono fun z hz ↦ hz.1)
    exact he.symm.trans (hq _ hy.2)
  obtain ⟨r,hr,hrz⟩ := Metric.mem_nhds_iff.mp hz
  have hfaff := graph_curvature_zero_affine hf hr (fun y hy ↦ hrz hy)
  have hgrad (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : gradient f y=gradient f 0 := by
    apply (convex_ball (0 : Plane) r).is_const_of_fderivWithin_eq_zero
      ((plane_gradient_contDiff hf).differentiable (by simp)).differentiableOn _ hy (Metric.mem_ball_self hr)
    intro z hz'
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hz']
    exact graph_curvature_zero_fderiv_gradient hf z (hrz hz')
  have hNa : N a=σ • graphSlopeNormal n (gradient f 0) := by
    have hh := hm.self_of_nhds.1
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simpa only [normalGraph,hf0,hz,zero_smul,add_zero] using hh
  have hct : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  refine ⟨(hu a ha).self_of_nhds,?_⟩
  filter_upwards [hcov,Metric.ball_mem_nhds (0 : Cover) hr,hct.eventually hm] with v hv hvr hmv
  have hcoords : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) r := by
    rw [Metric.mem_ball,dist_zero_right] at hvr ⊢
    exact (normalPlaneCoordinates_norm_le _ _).trans_lt hvr
  constructor
  · rw [hv,normalGraph_coordinates_eq_iff hn,hfaff _ hcoords,hf0,zero_add,hNa,
      real_inner_smul_left]
    have he : ⟪gradient f 0,normalPlaneCoordinates n v⟫=⟪n,v⟫ ↔
        ⟪graphSlopeNormal n (gradient f 0),v⟫=0 := by
      rw [graphSlopeNormal_weight hn,real_inner_smul_left,inner_sub_left,
        normalPlaneEmbedding_inner_coordinates hn,mul_eq_zero]
      simp only [inv_eq_zero,ne_of_gt (cmcWeight_pos _),false_or,sub_eq_zero]
      exact eq_comm
    rcases hσ with rfl|rfl <;> simpa only [one_mul,neg_one_mul,neg_eq_zero] using he
  · intro hb
    calc
      N (a+v)=N (a+normalGraph n f (normalPlaneCoordinates n v)) :=
        congrArg (fun t ↦ N (a+t)) (hv.mp hb).symm
      _=σ • graphSlopeNormal n (gradient f (normalPlaneCoordinates n v)) := hmv.1
      _=N a := by rw [hgrad _ hcoords,hNa]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem closed_flat_set_contains_plane {S : Set Cover} (hS : IsClosed S)
    {N : Cover → Cover} (hN : Continuous N)
    (hloc : ∀ a∈S,∀ᶠ v in 𝓝 (0 : Cover),
      (a+v∈S ↔ ⟪N a,v⟫=0) ∧ (a+v∈S → N (a+v)=N a))
    {a : Cover} (ha : a∈S) (b : Cover) (hb : ⟪N a,b-a⟫=0) :
    b∈S ∧ N b=N a := by
  let P : Set Cover := {x | ⟪N a,x⟫=⟪N a,a⟫}
  have hPc : Convex ℝ P :=
    (convex_singleton (⟪N a,a⟫ : ℝ)).linear_preimage (innerSL ℝ (N a)).toLinearMap
  let : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hPc.isPreconnected
  let T : Set P := {x | (x : Cover)∈S ∧ N x=N a}
  have hTc : IsClosed T := (hS.preimage continuous_subtype_val).inter
    (isClosed_eq (hN.comp continuous_subtype_val) continuous_const)
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have ht : Tendsto (fun y : P ↦ (y : Cover)-(x : Cover)) (𝓝 x) (𝓝 (0 : Cover)) := by
      have hc : Continuous (fun y : P ↦ (y : Cover)-(x : Cover)) := continuous_subtype_val.sub continuous_const
      simpa only [sub_self] using hc.tendsto x
    filter_upwards [ht.eventually (hloc x hx.1)] with y hy
    have hv : ⟪N x,(y : Cover)-(x : Cover)⟫=0 := by
      rw [hx.2,inner_sub_right]
      exact sub_eq_zero.mpr (y.property.trans x.property.symm)
    have hadd : (x : Cover)+((y : Cover)-(x : Cover))=(y : Cover) := by abel
    have hys := hy.1.mpr hv
    change (y : Cover)∈S ∧ N y=N a
    have hyN : N (y : Cover)=N (x : Cover) := by simpa only [hadd] using hy.2 hys
    exact ⟨by simpa only [hadd] using hys,hyN.trans hx.2⟩
  have hTu : T=univ := (show IsClopen T from ⟨hTc,hTo⟩).eq_univ ⟨⟨a,rfl⟩,ha,rfl⟩
  have hbp : b∈P := by
    change ⟪N a,b⟫=⟪N a,a⟫
    rw [inner_sub_right,sub_eq_zero] at hb
    exact hb
  have hmem : (⟨b,hbp⟩ : P)∈T := by rw [hTu]; trivial
  exact hmem

namespace Periodic

theorem isMinimizerAt_connected_or_complete_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) → ‖N a‖=1) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ᶠ v in 𝓝 (0 : Cover),
            (quotientMap (a+v)∈frontier (openRepresentative E) ↔ ⟪N a,v⟫=0) ∧
            (quotientMap (a+v)∈frontier (openRepresentative E) → N (a+v)=N a)) ∧
        ∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈frontier (openRepresentative E) ∧ N b=N a := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs,hcf⟩ :=
    isMinimizerAt_connected_or_zero_curvature hV hE hmin
  rcases hcf with hc|hq
  · exact Or.inl hc
  · have hloc := isMinimizerAt_zero_curvature_local_normal hV hE hmin hμ hN hp hae
      (fun x hx ↦ (hb x hx).1) hq
    refine Or.inr ⟨N,hN,hp,fun a ha ↦ (hloc a ha).1,fun a ha ↦ (hloc a ha).2,?_⟩
    intro a ha b hb
    exact closed_flat_set_contains_plane (isClosed_frontier.preimage continuous_quotientMap)
      hN.continuous (fun a ha ↦ (hloc a ha).2) ha b hb

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
