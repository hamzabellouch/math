import Mathlib
import OAI.Geometry.CubicTorus.Estimates.NodalBalanceValue

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_one_sign_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover)
    {U : Set Torus} (hU : IsOpen U)
    (hpos : ∀ a∈frontier (openRepresentative E)∩U,0≤⟪v,N (representative a)⟫)
    {a : Torus} (ha : a∈frontier (openRepresentative E)∩U)
    (hz : ⟪v,N (representative a)⟫=0) :
    ∀ b∈frontier (openRepresentative E),⟪v,N (representative b)⟫=0 := by
  let S := frontier (openRepresentative E)
  let F : Torus → ℝ := fun b => ⟪v,N (representative b)⟫
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rw [hxa]; exact ha.1
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hG0 : G 0=0 := by
    change (normalPlaneLinearIsometry n) 0+g 0 • n=0
    simp only [map_zero,hg0,zero_smul,add_zero]
  have hφ0 : φ 0=a := by simp only [φ,hG0,add_zero,hxa]
  have hmU : ∀ᶠ y in 𝓝 (0 : Plane),
      (N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S) ∧ φ y∈U :=
    hm.and (hφ.continuousAt.eventually (by rw [hφ0]; exact hU.mem_nhds ha.2))
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hmU
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε≤r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := normalTranslationNumerator_contDiff n hg v σ
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=cmcWeight (gradient g y)*F (φ y) := by
    change w y=cmcWeight (gradient g y)*⟪v,N (representative (φ y))⟫
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _,(hb y hy).1.1]
    exact normalTranslationNumerator_weight hn g v σ y
  have hzero : ∀ y∈Metric.ball (0 : Plane) ε,w y=0 := by
    apply (normalTranslationNumerator_linear n hg v σ hlin |>.mono
      (Metric.ball_subset_ball hεr)).nonneg_zero hg hw Metric.isOpen_ball
      (convex_ball (0 : Plane) ε).isPreconnected
      (fun y hy => hgrad y (Metric.ball_subset_ball hεr hy))
    · intro y hy
      rw [hws y hy]
      exact mul_nonneg (cmcWeight_pos _).le (hpos _ ⟨(hb y hy).1.2,(hb y hy).2⟩)
    · exact Metric.mem_ball_self hε
    · rw [hws 0 (Metric.mem_ball_self hε),hφ0]
      change cmcWeight _*⟪v,N (representative a)⟫=0
      rw [hz,mul_zero]
  have hag : a∈relativeZeroNeighborhood S F := by
    rw [← hxa]
    apply quotient_graph_zero_germ (hcover.mono fun z hz => hz.mp)
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) hε] with y hy
    have hh := hzero y hy
    rw [hws y hy] at hh
    exact (mul_eq_zero.mp hh).resolve_left (cmcWeight_pos _).ne'
  exact preconnected_zero_of_closed_germ hS
    (isMinimizerAt_normal_zero_germs_closed hV hE hmin hμ hN hp hae v) ⟨a,ha.1,hag⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_coordinate_strict_or_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    (∀ a∈frontier (openRepresentative E),N (representative a) i=0) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0<N (representative a) i) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0) := by
  by_cases hall : ∀ a∈frontier (openRepresentative E),N (representative a) i=0
  · exact Or.inl hall
  right
  obtain hpos|hneg := isMinimizerAt_normal_coordinate_weak_sign hV hE hmE hμ hN hp hae i hs
  · left
    intro a ha
    apply lt_of_le_of_ne (hpos a ha)
    intro hza
    apply hall
    have hh := isMinimizerAt_normal_one_sign_zero hV hE hmE hc hμ hN hp hae
      (EuclideanSpace.single i 1) (coordinateHalf_open i) (fun b hb => by
        simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hpos b hb) ha
      (by simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hza.symm)
    simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hh
  · right
    intro a ha
    apply lt_of_le_of_ne (hneg a ha)
    intro hza
    apply hall
    have hh := isMinimizerAt_normal_one_sign_zero hV hE hmE hc hμ hN hp hae
      (-EuclideanSpace.single i 1) (coordinateHalf_open i) (fun b hb => by
        simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_nonneg] using hneg b hb) ha
      (by simp only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,hza,neg_zero])
    simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_eq_zero] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_normal_unit_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ‖N x‖=1 := by
  apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.norm continuous_const
    (fun m x => by rw [hp]) (fun _ _ => rfl)
  filter_upwards [hae] with z hz
  rw [hz,z.2.property]

theorem isMinimizerAt_reflection_vertex_excluded {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {a : Torus} (hv : ∀ i,coordinateSine i (representative a)=0) :
    a∉frontier (openRepresentative E) := by
  intro ha
  have hz : N (representative a)=0 := by
    ext i
    exact isMinimizerAt_normal_coordinate_seam_zero hV hE hmE hμ hN hp hae i (hs i) ha (hv i)
  have hu := isMinimizerAt_normal_unit_boundary hV hE hmE hμ hN.continuous hp hae
    (representative a) (by rwa [quotientMap_representative])
  rw [hz,norm_zero] at hu
  exact zero_ne_one hu

theorem isMinimizerAt_connected_reflection_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧
      IsNormalMeasure F μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ a : Torus,(∀ i,coordinateSine i (representative a)=0) → a∉frontier (openRepresentative F)) ∧
      ∀ i : Fin 3,(∀ a∈frontier (openRepresentative F),N (representative a) i=0) ∨
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,0<N (representative a) i) ∨
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,N (representative a) i<0) := by
  let E' := toMeasurable torusVolume E
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have he : E' =ᵐ[torusVolume] E := hmE.1.1.toMeasurable_ae_eq
  have hmE' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae he).mpr hmE
  have hc' : IsPreconnected (frontier (openRepresentative E')) := by rwa [openRepresentative_congr_ae he]
  obtain ⟨b,hb⟩ := isMinimizerAt_exists_coordinate_symmetries_measurable hV hE' hmE' hc'
  let F := (fun z : Torus => z+b) ⁻¹' E'
  have hF : MeasurableSet F := (continuous_add_const b).measurable hE'
  have hmF : IsMinimizerAt V F := isMinimizerAt_translation hmE' b
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    rw [frontier_openRepresentative_translation hE']
    exact (Homeomorph.addRight b).isPreconnected_preimage.mpr hc'
  obtain ⟨μ,N,hN,hp,hμ,hae,hnod⟩ := Periodic.isMinimizerAt_translation_nodal_count hV hmF hcF
  refine ⟨b,F,μ,N,hN,hp,hF,(measurePreserving_add_right torusVolume b).quasiMeasurePreserving.preimage_ae_eq he,
    hmF,hcF,hμ,hae,hb,?_,?_⟩
  · intro a ha
    exact isMinimizerAt_reflection_vertex_excluded hV hF hmF hμ hN hp hae hb ha
  · intro i
    let := hnod (EuclideanSpace.single i 1)
    exact isMinimizerAt_normal_coordinate_strict_or_zero hV hF hmF hcF hμ hN hp hae i (hb i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_tangent_line {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0=0)
    (v : Cover) (htan : ∀ᶠ y in 𝓝 (0 : Plane),
      ⟪v,graphSlopeNormal n (gradient g y)⟫=0) :
    ∀ᶠ t : ℝ in 𝓝 0,normalGraph n g (t • normalPlaneCoordinates n v)=t • v := by
  let p := normalPlaneCoordinates n v
  let c := ⟪n,v⟫
  have ht : Tendsto (fun t : ℝ => t • p) (𝓝 0) (𝓝 (0 : Plane)) := by
    have hc : Continuous (fun t : ℝ => t • p) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  have hd : ∀ᶠ t : ℝ in 𝓝 0,fderiv ℝ g (t • p) p=c := by
    filter_upwards [ht.eventually htan] with t ht
    have hw := normalTranslationNumerator_weight hn g v 1 (t • p)
    simp only [one_smul,ht,mul_zero,normalTranslationNumerator,one_mul] at hw
    rw [real_inner_comm n v,inner_gradient_right] at hw
    simp only [conj_trivial] at hw
    exact (sub_eq_zero.mp hw).symm
  obtain ⟨r,hr,hrd⟩ := Metric.eventually_nhds_iff.mp hd
  let f : ℝ → ℝ := fun t => g (t • p)-t*c
  have hf : Differentiable ℝ f :=
    ((hg.differentiable (by simp)).comp ((differentiable_id).smul_const p)).sub
      (differentiable_id.mul_const c)
  have hd0 : (Metric.ball (0 : ℝ) r).EqOn (deriv f) 0 := by
    intro t ht
    have he := (((hg.differentiable (by simp) (t • p)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const p)).sub ((hasDerivAt_id t).mul_const c)).deriv
    change deriv f t=0
    simpa only [f,Function.comp_def,id_eq,Pi.sub_def,one_smul,one_mul,hrd ht,sub_self] using he
  have hh : ∀ t∈Metric.ball (0 : ℝ) r,g (t • p)=t*c := by
    intro t ht
    have he := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℝ) r).isPreconnected
      hf.differentiableOn hd0 ht (show (0 : ℝ)∈Metric.ball 0 r by simpa using hr)
    change g (t • p)-t*c=g (0 • p)-0*c at he
    simpa only [zero_smul,hg0,zero_mul,sub_zero,sub_eq_zero] using he
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
  dsimp only [normalGraph]
  rw [hh t ht]
  change (normalPlaneLinearIsometry n) (t • p)+(t*c) • n=t • v
  rw [map_smul,mul_smul,← smul_add]
  exact congrArg (fun w : Cover => t • w) (normalPlaneCoordinates_reconstruct hn v)

theorem isMinimizerAt_zero_normal_local_flow {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∀ᶠ t : ℝ in 𝓝 0,quotientMap (x+t • v)∈frontier (openRepresentative E) := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hchart,hcov,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmE hμ hN hp hae x hx
  have htan : ∀ᶠ y in 𝓝 (0 : Plane),⟪v,graphSlopeNormal n (gradient g y)⟫=0 := by
    filter_upwards [hchart] with y hy
    have hh := hz _ hy.2
    rw [hy.1,inner_smul_right] at hh
    rcases hσ with rfl|rfl <;> simpa using hh
  have ht : Tendsto (fun t : ℝ => t • normalPlaneCoordinates n v) (𝓝 0) (𝓝 (0 : Plane)) := by
    have hc : Continuous (fun t : ℝ => t • normalPlaneCoordinates n v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  filter_upwards [normalGraph_tangent_line hn hg hg0 v htan,ht.eventually hchart] with t ht hc
  rw [← ht]
  exact hc.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_tangent_fderiv_zero (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {f : Cover → ℝ} (hf : DifferentiableAt ℝ f (a+normalGraph n g y))
    (hz : ∀ᶠ z in 𝓝 y,f (a+normalGraph n g z)=0)
    (v : Cover) (hv : ⟪graphSlopeNormal n (gradient g y),v⟫=0) :
    fderiv ℝ f (a+normalGraph n g y) v=0 := by
  let q := graphInverseMetric (gradient g y) (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
  have hj : fderiv ℝ (normalGraph n g) y q=v := by
    rw [normalGraph_fderiv_apply hg]
    dsimp [q]
    rw [graph_metric_projection hn,hv,zero_smul,sub_zero]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have he : (fun z => f (a+normalGraph n g z))=ᶠ[𝓝 y](fun _ => (0 : ℝ)) := hz
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (f ∘ fun z => a+normalGraph n g z) y=_ at hd
  rw [(hf.hasFDerivAt.comp y hΦ).fderiv] at hd
  simp only [fderiv_const_apply] at hd
  have hh := congrArg (fun L : Plane →L[ℝ] ℝ => L q) hd
  simpa only [ContinuousLinearMap.comp_apply,zero_apply,hj] using hh

theorem isMinimizerAt_tangent_fderiv_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {f : Cover → ℝ} (hf : Differentiable ℝ f)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → f x=0)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (v : Cover) (hv : ⟪N x,v⟫=0) : fderiv ℝ f x v=0 := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hchart,hcov,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmE hμ hN hp hae x hx
  have hx0 : x+normalGraph n g 0=x := by
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simp [normalGraph,hg0,hz]
  have hc : N x=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [hx0] using hchart.self_of_nhds.1
  have hv' : ⟪graphSlopeNormal n (gradient g 0),v⟫=0 := by
    rw [hc,real_inner_smul_left] at hv
    rcases hσ with rfl|rfl <;> simpa using hv
  have hz' : ∀ᶠ y in 𝓝 (0 : Plane),f (x+normalGraph n g y)=0 :=
    hchart.mono fun y hy => hz _ hy.2
  simpa only [hx0] using graph_tangent_fderiv_zero x hn hg 0 (hf _) hz' v hv'

theorem isMinimizerAt_axial_shape_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) : fderiv ℝ N x v=0 := by
  have hv : ⟪N x,v⟫=0 := by rw [real_inner_comm]; exact hz x hx
  have hn : ‖N x‖=1 := hu.self_of_nhds
  have hNt (w : Cover) : ⟪N x,fderiv ℝ N x w⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      smooth_unit_normal_derivative (hN.differentiable (by simp) x) hu,inner_zero_left]
  have hscalar : Differentiable ℝ (fun y => ⟪v,N y⟫) :=
    (innerSL ℝ v).differentiable.comp (hN.differentiable (by simp))
  have hd (w : Cover) (hw : ⟪N x,w⟫=0) : ⟪fderiv ℝ N x v,w⟫=0 := by
    rw [isMinimizerAt_shape_tangent_symmetric hV hE hmE hμ hN hp hae x hx v w hv hw]
    have hh := isMinimizerAt_tangent_fderiv_zero hV hE hmE hμ hN hp hae hscalar hz x hx w hw
    have he := (innerSL ℝ v).hasFDerivAt.comp x (hN.differentiable (by simp) x).hasFDerivAt
    rw [show (fun y => ⟪v,N y⟫)=(innerSL ℝ v) ∘ N from rfl,he.fderiv] at hh
    exact hh
  have hh := hd (fderiv ℝ N x v) (hNt v)
  exact inner_self_eq_zero.mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_symmetric_null_shape (L : Plane →L[ℝ] Plane)
    (hs : ∀ v w,⟪L v,w⟫=⟪v,L w⟫) {p : Plane} (hp : ‖p‖=1)
    (hz : L p=0) (w : Plane) : L w=planeTrace L • (w-⟪p,w⟫ • p) := by
  let a := L (EuclideanSpace.single 0 1) 0
  let b := L (EuclideanSpace.single 1 1) 0
  let d := L (EuclideanSpace.single 1 1) 1
  have hb : L (EuclideanSpace.single 0 1) 1=b := by
    have h := hs (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,mul_one,one_mul] using h
  have hc (q : Plane) : L q 0=a*q 0+b*q 1 ∧ L q 1=b*q 0+d*q 1 := by
    constructor
    · conv_lhs => rw [plane_decompose q]
      simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      dsimp [a,b]; ring
    · conv_lhs => rw [plane_decompose q]
      simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hb]
      dsimp [d]; ring
  have h0 : a*p 0+b*p 1=0 := by rw [← (hc p).1,hz]; rfl
  have h1 : b*p 0+d*p 1=0 := by rw [← (hc p).2,hz]; rfl
  have hn : (p 0)^2+(p 1)^2=1 := by
    have hh := real_inner_self_eq_norm_sq p
    rw [plane_inner_components,hp,one_pow] at hh
    nlinarith only [hh]
  have htr : planeTrace L=a+d := by simp only [planeTrace,Fin.sum_univ_two]; rfl
  have ha : a=(a+d)*(p 1)^2 := by
    linear_combination p 0*h0-p 1*h1-a*hn
  have hd : d=(a+d)*(p 0)^2 := by
    linear_combination p 1*h1-p 0*h0-d*hn
  have hb' : b= -(a+d)*p 0*p 1 := by
    linear_combination p 1*h0+p 0*h1-b*hn
  ext i
  fin_cases i
  · change L w 0=planeTrace L*(w 0-⟪p,w⟫*p 0)
    rw [plane_inner_components,htr,(hc w).1]
    linear_combination w 0*ha+w 1*hb'+(a+d)*w 0*hn
  · change L w 1=planeTrace L*(w 1-⟪p,w⟫*p 1)
    rw [plane_inner_components,htr,(hc w).2]
    linear_combination w 0*hb'+w 1*hd+(a+d)*w 1*hn

lemma normal_plane_trace {n : Cover} (hn : ‖n‖=1)
    (D : Cover →L[ℝ] Cover) (ht : ∀ w,⟪n,D w⟫=0) :
    planeTrace ((normalPlaneCoordinates n).comp (D.comp
      (normalPlaneLinearIsometry n).toContinuousLinearMap))=coverTrace D := by
  rw [← rectangular_trace]
  symm
  apply normal_trace_invariance hn ht
  · intro w
    exact ht _
  · intro w hw
    simp only [ContinuousLinearMap.comp_apply]
    change D w=D (normalPlaneEmbedding n (normalPlaneCoordinates n w))
    rw [normalPlaneEmbedding_coordinates_of_inner_zero hn hw]

lemma normal_axial_shape {n v : Cover} (hn : ‖n‖=1) (hv : ‖v‖=1)
    (hvn : ⟪n,v⟫=0) (D : Cover →L[ℝ] Cover)
    (ht : ∀ w,⟪n,D w⟫=0)
    (hs : ∀ z w,⟪n,z⟫=0 → ⟪n,w⟫=0 → ⟪D z,w⟫=⟪z,D w⟫)
    (hz : D v=0) (w : Cover) (hw : ⟪n,w⟫=0) :
    D w=coverTrace D • (w-⟪v,w⟫ • v) := by
  let P := normalPlaneCoordinates n
  let T := (normalPlaneLinearIsometry n).toContinuousLinearMap
  let L := P.comp (D.comp T)
  have hT (u : Plane) : T u=normalPlaneEmbedding n u := rfl
  have he (u : Cover) (hu : ⟪n,u⟫=0) : T (P u)=u :=
    normalPlaneEmbedding_coordinates_of_inner_zero hn hu
  have hPs (u : Plane) (z : Cover) : ⟪P z,u⟫=⟪z,T u⟫ := by
    rw [real_inner_comm,← normalPlaneEmbedding_inner_coordinates hn,real_inner_comm]
    rfl
  have hLs (u z : Plane) : ⟪L u,z⟫=⟪u,L z⟫ := by
    change ⟪P (D (T u)),z⟫=⟪u,P (D (T z))⟫
    rw [hPs,← normalPlaneEmbedding_inner_coordinates hn]
    exact hs _ _ (normalPlaneEmbedding_inner hn _) (normalPlaneEmbedding_inner hn _)
  have hp : ‖P v‖=1 := (normalPlaneCoordinates_norm_of_inner_zero hn hvn).trans hv
  have hz' : L (P v)=0 := by change P (D (T (P v)))=0; rw [he v hvn,hz,map_zero]
  have hh := plane_symmetric_null_shape L hLs hp hz' (P w)
  have htr : planeTrace L=coverTrace D := normal_plane_trace hn D ht
  have hi : ⟪P v,P w⟫=⟪v,w⟫ := by rw [hPs,he w hw]
  have hhd := congrArg T hh
  simp only [map_smul,map_sub,htr,hi] at hhd
  change T (P (D (T (P w))))=coverTrace D • (T (P w)-⟪v,w⟫ • T (P v)) at hhd
  simpa only [he w hw,he v hvn,he (D w) (ht w)] using hhd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialCenter (v : Cover) (H : ℝ) (N : Cover → Cover) (x : Cover) : Cover :=
  x-⟪v,x⟫ • v-H⁻¹ • N x

lemma axialCenter_fderiv {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (v : Cover) (H : ℝ) (w : Cover) :
    fderiv ℝ (axialCenter v H N) x w=w-⟪v,w⟫ • v-H⁻¹ • fderiv ℝ N x w := by
  have hh := ((hasFDerivAt_id x).sub ((innerSL ℝ v).hasFDerivAt.smul_const v)).sub
    (hN.hasFDerivAt.const_smul H⁻¹)
  change HasFDerivAt (axialCenter v H N) _ x at hh
  rw [hh.fderiv]
  rfl

theorem isMinimizerAt_axial_shape {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (w : Cover) (hw : ⟪N x,w⟫=0) :
    fderiv ℝ N x w=H • (w-⟪v,w⟫ • v) := by
  have hn := (hgeom x hx).1.self_of_nhds
  have htan (z : Cover) : ⟪N x,fderiv ℝ N x z⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      smooth_unit_normal_derivative (hN.differentiable (by simp) x) (hgeom x hx).1,inner_zero_left]
  have he := normal_axial_shape hn hv (by rw [real_inner_comm]; exact hz x hx)
    (fderiv ℝ N x) htan
    (isMinimizerAt_shape_tangent_symmetric hV hE hmE hμ hN hp hae x hx)
    (isMinimizerAt_axial_shape_zero hV hE hmE hμ hN hp hae v hz x hx (hgeom x hx).1) w hw
  rw [← divergence_eq_coverTrace,(hgeom x hx).2] at he
  exact he

theorem isMinimizerAt_axialCenter_local {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hH : H≠0)
    (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ z in 𝓝 a,quotientMap z∈frontier (openRepresentative E) →
      axialCenter v H N z=axialCenter v H N a := by
  obtain ⟨g,hg,hg0,hchart,hcov⟩ :=
    isMinimizerAt_tangent_CMC_chart hV hE hmE hμ hN hp hae hgeom a ha
  let X : Plane → Cover := fun y => a+normalGraph (N a) g y
  have hX : Differentiable ℝ X := fun y =>
    ((normalGraph_hasFDerivAt (n := N a) (hg.differentiable (by simp) y)).const_add a).differentiableAt
  have hC : Differentiable ℝ (axialCenter v H N) := by
    intro x
    exact (((hasFDerivAt_id x).sub ((innerSL ℝ v).hasFDerivAt.smul_const v)).sub
      ((hN.differentiable (by simp) x).hasFDerivAt.const_smul H⁻¹)).differentiableAt
  have hF := hC.comp hX
  obtain ⟨r,hr,hrc⟩ := Metric.eventually_nhds_iff.mp hchart
  have hd : ∀ y∈Metric.ball (0 : Plane) r,fderiv ℝ (axialCenter v H N ∘ X) y=0 := by
    intro y hy
    rw [fderiv_comp y (hC _) (hX y)]
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.comp_apply,zero_apply]
    rw [axialCenter_fderiv (hN.differentiable (by simp) _)]
    have ht : ⟪N (X y),fderiv ℝ X y w⟫=0 := by
      change ⟪N (a+normalGraph (N a) g y),fderiv ℝ (fun z => a+normalGraph (N a) g z) y w⟫=0
      rw [(hrc hy).1,fderiv_const_add]
      exact normalGraph_derivative_tangent ((hgeom a ha).1.self_of_nhds) hg y w
    rw [isMinimizerAt_axial_shape hV hE hmE hμ hN hp hae hv hz hgeom (X y) (hrc hy).2.1 _ ht,
      smul_smul,inv_mul_cancel₀ hH,one_smul,sub_self]
  have he (y : Plane) (hy : y∈Metric.ball 0 r) : axialCenter v H N (X y)=axialCenter v H N a := by
    have hh := (convex_ball (0 : Plane) r).is_const_of_fderivWithin_eq_zero hF.differentiableOn
      (fun z hz' => by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz']; exact hd z hz')
      hy (Metric.mem_ball_self hr)
    simpa only [Function.comp_apply,X,normalGraph_zero hg0,add_zero] using hh
  have hsub : Tendsto (fun z : Cover => z-a) (𝓝 a) (𝓝 (0 : Cover)) := by
    have hc : Continuous (fun z : Cover => z-a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  have hP : Tendsto (fun z : Cover => normalPlaneCoordinates (N a) (z-a)) (𝓝 a) (𝓝 (0 : Plane)) := by
    exact ((normalPlaneCoordinates (N a)).continuous.tendsto' _ _ (map_zero _)).comp hsub
  filter_upwards [hsub.eventually hcov,hP.eventually (Metric.ball_mem_nhds (0 : Plane) hr)] with z hz hy hzb
  have hgx := hz.mp (by simpa only [add_sub_cancel] using hzb)
  have hh := he _ hy
  simpa only [X,hgx,add_sub_cancel] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialProjection (v : Cover) : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover-(innerSL ℝ v).smulRight v

@[simp] lemma axialProjection_apply (v x : Cover) :
    axialProjection v x=x-⟪v,x⟫ • v := rfl

lemma axialProjection_self {v : Cover} (hv : ‖v‖=1) : axialProjection v v=0 := by
  simp [hv]

lemma axialProjection_tangent {v x : Cover} (hx : ⟪v,x⟫=0) : axialProjection v x=x := by simp [hx]

lemma axialProjection_inner {v n x : Cover} (hn : ⟪v,n⟫=0) :
    ⟪n,axialProjection v x⟫=⟪n,x⟫ := by
  simp only [axialProjection_apply,inner_sub_right,real_inner_smul_right,
    real_inner_comm v n,hn,mul_zero,sub_zero]

lemma axialProjection_inner_zero {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    ⟪v,axialProjection v x⟫=0 := by
  rw [axialProjection_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hv,one_pow,mul_one,sub_self]

lemma axialProjection_idempotent {v : Cover} (hv : ‖v‖=1) (x : Cover) :
    axialProjection v (axialProjection v x)=axialProjection v x :=
  axialProjection_tangent (axialProjection_inner_zero hv x)

def euclideanCylinder (v c : Cover) (R : ℝ) : Set Cover :=
  {x | ‖axialProjection v (x-c)‖=R}

lemma isClosed_euclideanCylinder (v c : Cover) (R : ℝ) : IsClosed (euclideanCylinder v c R) := by
  exact isClosed_eq (((axialProjection v).continuous.comp (continuous_id.sub continuous_const)).norm) continuous_const

lemma normal_squared_cylinder_difference {n v : Cover} (hn : ‖n‖=1) (hvn : ⟪v,n⟫=0)
    (g : Plane → ℝ) (c z : Cover) :
    ‖axialProjection v (z-c)‖^2-‖axialProjection v (normalGraph n g (normalPlaneCoordinates n z)-c)‖^2=
      (⟪n,z⟫-g (normalPlaneCoordinates n z))*(⟪n,z⟫+g (normalPlaneCoordinates n z)-2*⟪n,c⟫) := by
  let w := normalGraph n g (normalPlaneCoordinates n z)
  let k := ⟪n,z⟫-g (normalPlaneCoordinates n z)
  have he : z-c=(w-c)+k • n := by
    calc
      z-c=(normalPlaneEmbedding n (normalPlaneCoordinates n z)+⟪n,z⟫ • n)-c :=
        congrArg (fun q : Cover => q-c) (normalPlaneCoordinates_reconstruct hn z).symm
      _=(w-c)+k • n := by dsimp [w,k,normalGraph]; rw [sub_smul]; module
  have hi : ⟪n,axialProjection v (w-c)⟫=g (normalPlaneCoordinates n z)-⟪n,c⟫ := by
    rw [axialProjection_inner hvn,inner_sub_right]
    dsimp [w,normalGraph]
    rw [inner_add_right,normalPlaneEmbedding_inner hn,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hn,one_pow,mul_one,zero_add]
  rw [he,map_add,map_smul,axialProjection_tangent hvn,norm_add_sq_real]
  rw [real_inner_smul_right,real_inner_comm n (axialProjection v (w-c)),hi,
    norm_smul,Real.norm_eq_abs,hn,mul_one,sq_abs]
  dsimp [k,w]
  ring

lemma local_graph_cylinder_iff {n v : Cover} (hn : ‖n‖=1) (hvn : ⟪v,n⟫=0)
    {g : Plane → ℝ} (hg : Continuous g) (hg0 : g 0=0) {c : Cover} {R : ℝ}
    (hc : ⟪n,c⟫≠0)
    (hs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n g y∈euclideanCylinder v c R) :
    ∀ᶠ z in 𝓝 (0 : Cover),normalGraph n g (normalPlaneCoordinates n z)=z ↔
      z∈euclideanCylinder v c R := by
  have hct : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  have hnon : ∀ᶠ z in 𝓝 (0 : Cover),⟪n,z⟫+g (normalPlaneCoordinates n z)-2*⟪n,c⟫≠0 := by
    have ht : ContinuousAt (fun z : Cover => ⟪n,z⟫+g (normalPlaneCoordinates n z)-2*⟪n,c⟫) 0 := by fun_prop
    apply ht.eventually_ne
    simp only [inner_zero_right,map_zero,hg0,zero_add,zero_sub,neg_ne_zero,mul_ne_zero_iff]
    exact ⟨by norm_num,hc⟩
  filter_upwards [hct.eventually hs,hnon] with z hz hnz
  constructor
  · intro he
    rwa [← he]
  · intro he
    have hz0 : ‖axialProjection v (z-c)‖^2-
        ‖axialProjection v (normalGraph n g (normalPlaneCoordinates n z)-c)‖^2=0 := by
      change ‖axialProjection v (z-c)‖=R at he
      change ‖axialProjection v (normalGraph n g (normalPlaneCoordinates n z)-c)‖=R at hz
      rw [he,hz,sub_self]
    rw [normal_squared_cylinder_difference hn hvn,mul_eq_zero] at hz0
    exact (normalGraph_coordinates_eq_iff hn g z).mpr
      ((sub_eq_zero.mp (hz0.resolve_right hnz)).symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialCenter_transverse {v : Cover} (hv : ‖v‖=1) {N : Cover → Cover}
    (H : ℝ) {x : Cover} (hx : ⟪v,N x⟫=0) : ⟪v,axialCenter v H N x⟫=0 := by
  change ⟪v,axialProjection v x-H⁻¹ • N x⟫=0
  rw [inner_sub_right,axialProjection_inner_zero hv,real_inner_smul_right,hx,mul_zero,sub_zero]

lemma cylinder_center_translation {v : Cover} (hv : ‖v‖=1) {N : Cover → Cover}
    (H : ℝ) {a : Cover} (ha : ⟪v,N a⟫=0) (z : Cover) (R : ℝ) :
    a+z∈euclideanCylinder v (axialCenter v H N a) R ↔
      z∈euclideanCylinder v (-H⁻¹ • N a) R := by
  have he : axialProjection v (a+z-axialCenter v H N a)=
      axialProjection v (z-(-H⁻¹ • N a)) := by
    change axialProjection v (a+z-(axialProjection v a-H⁻¹ • N a))=_
    rw [map_sub,map_add,map_sub,map_smul,axialProjection_idempotent hv,
      axialProjection_tangent ha,map_sub,map_smul,axialProjection_tangent ha]
    module
  exact iff_of_eq (congrArg (fun w : Cover => ‖w‖=R) he)

theorem isMinimizerAt_axial_local_cylinder {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {H : ℝ} (hH : H≠0)
    (hgeom : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ z in 𝓝 a,
      (quotientMap z∈frontier (openRepresentative E) ↔
        z∈euclideanCylinder v (axialCenter v H N a) |H⁻¹|) ∧
      (quotientMap z∈frontier (openRepresentative E) →
        axialCenter v H N z=axialCenter v H N a) := by
  obtain ⟨g,hg,hg0,hchart,hcov⟩ :=
    isMinimizerAt_tangent_CMC_chart hV hE hmE hμ hN hp hae hgeom a ha
  have hn : ‖N a‖=1 := (hgeom a ha).1.self_of_nhds
  have hza := hz a ha
  have hcenter := isMinimizerAt_axialCenter_local hV hE hmE hμ hN hp hae hv hz hH hgeom a ha
  have hX : Tendsto (fun y => a+normalGraph (N a) g y) (𝓝 (0 : Plane)) (𝓝 a) := by
    have ht := (normalGraph_tendsto_zero (n := N a) hg hg0).const_add a
    simpa only [add_zero] using ht
  have hs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph (N a) g y∈euclideanCylinder v (-H⁻¹ • N a) |H⁻¹| := by
    filter_upwards [hchart,hX.eventually hcenter] with y hy hyc
    have he := hyc hy.2.1
    have hproj : axialProjection v (normalGraph (N a) g y-(-H⁻¹ • N a))=
        H⁻¹ • N (a+normalGraph (N a) g y) := by
      apply sub_eq_zero.mp
      calc
        _=axialCenter v H N (a+normalGraph (N a) g y)-axialCenter v H N a := by
          change axialProjection v (_-_) - _ =
            (axialProjection v (a+normalGraph (N a) g y)-H⁻¹ • N (a+normalGraph (N a) g y))-
              (axialProjection v a-H⁻¹ • N a)
          rw [map_sub,map_smul,axialProjection_tangent hza,map_add]
          module
        _=0 := sub_eq_zero.mpr he
    change ‖axialProjection v (_-_)‖=|H⁻¹|
    rw [hproj,norm_smul,Real.norm_eq_abs,(hgeom _ hy.2.1).1.self_of_nhds,mul_one]
  have hcn : ⟪N a,-H⁻¹ • N a⟫≠0 := by
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
    exact neg_ne_zero.mpr (inv_ne_zero hH)
  have hlocal := local_graph_cylinder_iff hn hza hg.continuous hg0 hcn hs
  have ht : Tendsto (fun z : Cover => z-a) (𝓝 a) (𝓝 (0 : Cover)) := by
    have hc : Continuous (fun z : Cover => z-a) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto a
  filter_upwards [ht.eventually hcov,ht.eventually hlocal,hcenter] with z hcovz hlocalz hcz
  refine ⟨?_,hcz⟩
  have hh := hcovz.trans hlocalz
  simpa only [add_sub_cancel] using hh.trans
    (cylinder_center_translation hv H hza (z-a) |H⁻¹|).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isPreconnected_euclideanCylinder {v : Cover} (hv : ‖v‖=1) (c : Cover) (R : ℝ) :
    IsPreconnected (euclideanCylinder v c R) := by
  let P : Set (ℝ × Plane) := univ ×ˢ Metric.sphere 0 R
  let F : ℝ × Plane → Cover := fun p => c+p.1 • v+normalPlaneEmbedding v p.2
  have hP : IsPreconnected P := isPreconnected_univ.prod
    (isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [Plane,finrank_euclideanSpace_fin]) 0 R)
  have hF : Continuous F := by
    exact (continuous_const.add (continuous_fst.smul continuous_const)).add
      ((normalPlaneLinearIsometry v).continuous.comp continuous_snd)
  have he : F '' P=euclideanCylinder v c R := by
    apply Subset.antisymm
    · rintro x ⟨⟨s,y⟩,hy,rfl⟩
      change ‖axialProjection v (c+s • v+normalPlaneEmbedding v y-c)‖=R
      rw [show c+s • v+normalPlaneEmbedding v y-c=s • v+normalPlaneEmbedding v y by abel,
        map_add,map_smul,axialProjection_self hv,smul_zero,zero_add,
        axialProjection_tangent (normalPlaneEmbedding_inner hv y),normalPlaneEmbedding_norm]
      simpa only [Metric.mem_sphere,dist_zero_right] using hy.2
    · intro x hx
      refine ⟨(⟪v,x-c⟫,normalPlaneCoordinates v (x-c)),⟨mem_univ _,?_⟩,?_⟩
      · simp only [Metric.mem_sphere,dist_zero_right]
        change ‖normalPlaneCoordinates v (x-c)‖=R
        rw [← normalPlaneEmbedding_norm v,normalPlaneEmbedding_coordinates hv]
        exact hx
      · change c+⟪v,x-c⟫ • v+normalPlaneEmbedding v (normalPlaneCoordinates v (x-c))=x
        have hh := normalPlaneCoordinates_reconstruct hv (x-c)
        calc
          _=c+(normalPlaneEmbedding v (normalPlaneCoordinates v (x-c))+⟪v,x-c⟫ • v) := by abel
          _=x := by rw [hh,add_sub_cancel]
  rw [← he]
  exact hP.image F hF.continuousOn

theorem closed_cylindrical_set_contains_cylinder {S : Set Cover} (hS : IsClosed S)
    {N : Cover → Cover} (hN : Continuous N) {v : Cover} (hv : ‖v‖=1) (H : ℝ)
    (hu : ∀ a∈S,‖N a‖=1) (hz : ∀ a∈S,⟪v,N a⟫=0)
    (hloc : ∀ a∈S,∀ᶠ z in 𝓝 a,
      (z∈S ↔ z∈euclideanCylinder v (axialCenter v H N a) |H⁻¹|) ∧
      (z∈S → axialCenter v H N z=axialCenter v H N a))
    {a : Cover} (ha : a∈S) (b : Cover)
    (hb : b∈euclideanCylinder v (axialCenter v H N a) |H⁻¹|) :
    b∈S ∧ axialCenter v H N b=axialCenter v H N a := by
  let c := axialCenter v H N a
  let P : Set Cover := euclideanCylinder v c |H⁻¹|
  have hPc := isPreconnected_euclideanCylinder hv c |H⁻¹|
  let : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hPc
  let T : Set P := {x | (x : Cover)∈S ∧ axialCenter v H N x=c}
  have hC : Continuous (axialCenter v H N) :=
    (continuous_id.sub (((innerSL ℝ v).continuous).smul continuous_const)).sub (hN.const_smul H⁻¹)
  have hTc : IsClosed T := (hS.preimage continuous_subtype_val).inter
    (isClosed_eq (hC.comp continuous_subtype_val) continuous_const)
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hloc x hx.1)] with y hy
    have hys : (y : Cover)∈S := hy.1.mpr (by rw [hx.2]; exact y.property)
    exact ⟨hys,(hy.2 hys).trans hx.2⟩
  have haP : a∈P := by
    change ‖axialProjection v (a-(axialProjection v a-H⁻¹ • N a))‖=|H⁻¹|
    rw [map_sub,map_sub,axialProjection_idempotent hv,map_smul,axialProjection_tangent (hz a ha),
      sub_sub_cancel,norm_smul,hu a ha,Real.norm_eq_abs,mul_one]
  have hTu : T=univ := (show IsClopen T from ⟨hTc,hTo⟩).eq_univ ⟨⟨a,haP⟩,ha,rfl⟩
  have hmem : (⟨b,hb⟩ : P)∈T := by rw [hTu]; trivial
  exact hmem

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateAxis_norm (i : Fin 3) : ‖(EuclideanSpace.single i 1 : Cover)‖=1 := by simp

lemma axialProjection_axis_apply (i : Fin 3) (x : Cover) (j : Fin 3) :
    axialProjection (EuclideanSpace.single i 1) x j=if j=i then 0 else x j := by
  simp only [axialProjection_apply,EuclideanSpace.inner_single_left,conj_trivial,one_mul,
    PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply]
  split_ifs with h
  · subst j; simp
  · simp

lemma axialProjection_axis_lattice (i : Fin 3) (m : Fin 3 → ℤ) :
    axialProjection (EuclideanSpace.single i 1) (latticeVector m)=
      latticeVector (fun j => if j=i then 0 else m j) := by
  ext j
  rw [axialProjection_axis_apply]
  simp only [latticeVector,PiLp.toLp_apply]
  split_ifs <;> simp_all

lemma axialCenter_axis_periodic {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (H : ℝ) :
    ∀ m x,quotientMap (axialCenter (EuclideanSpace.single i 1) H N (x+latticeVector m))=
      quotientMap (axialCenter (EuclideanSpace.single i 1) H N x) := by
  intro m x
  change quotientMap (axialProjection (EuclideanSpace.single i 1) (x+latticeVector m)-H⁻¹ • N (x+latticeVector m))=_
  rw [map_add,hp,show axialProjection (EuclideanSpace.single i 1) x+
      axialProjection (EuclideanSpace.single i 1) (latticeVector m)-H⁻¹ • N x=
      (axialProjection (EuclideanSpace.single i 1) x-H⁻¹ • N x)+
        axialProjection (EuclideanSpace.single i 1) (latticeVector m) by abel,
    axialProjection_axis_lattice,quotientMap_add,quotientMap_latticeVector,add_zero]
  rfl

lemma fin_three_other_coordinates (i : Fin 3) :
    ∃ j k : Fin 3,j≠i ∧ k≠i ∧ j≠k := by
  fin_cases i
  · exact ⟨1,2,by decide,by decide,by decide⟩
  · exact ⟨0,2,by decide,by decide,by decide⟩
  · exact ⟨0,1,by decide,by decide,by decide⟩

end CubicTorus

end
end

end OAI
