import Mathlib
import OAI.Geometry.BallPacking.Forms.SpatialOneForm

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open MeasureTheory Set Function
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem planar_fixed_support_integral_smooth {A : ℝ} {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → f (p,(x,y))=0) :
    ContDiff ℝ ∞ (fun p => ∫ z, f (p,z)) := by
  have hff : ContDiff ℝ ∞ (fun q : (P × ℝ) × ℝ => f (q.1.1,(q.2,q.1.2))) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => planarMarginal A (fun z => f (q.1,z)) q.2) :=
    (contDiff_parameter_segment_integral hff (-A)).comp (contDiff_id.prodMk contDiff_const)
  have hh : ContDiff ℝ ∞ (fun p => ∫ y in -A..A, planarMarginal A (fun z => f (p,z)) y) :=
    (contDiff_parameter_segment_integral hg (-A)).comp (contDiff_id.prodMk contDiff_const)
  have he : (fun p => ∫ y in -A..A, planarMarginal A (fun z => f (p,z)) y) =
      (fun p => ∫ z, f (p,z)) := by
    funext p
    have hfp : Continuous (fun z => f (p,z)) :=
      hf.continuous.comp (continuous_const.prodMk continuous_id)
    have hfc : HasCompactSupport (fun z => f (p,z)) := by
      apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (max A 0))
      intro z hz
      have hh : max A 0 < max |z.1| |z.2| := by
        simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hz
      exact hzero p z.1 z.2 ((lt_max_iff.mp ((le_max_left A 0).trans_lt hh)).imp le_of_lt le_of_lt)
    have hgm (y : ℝ) : planarMarginal A (fun z => f (p,z)) y = ∫ x, f (p,(x,y)) :=
      integral_eq_full_of_box_support (fun x hx => hzero p x y (Or.inl hx))
    have hgy (y : ℝ) (hy : A ≤ |y|) : planarMarginal A (fun z => f (p,z)) y=0 := by
      unfold planarMarginal
      have he : (fun x => f (p,(x,y))) = fun _ => (0:ℝ) := funext fun x => hzero p x y (Or.inr hy)
      rw [he,intervalIntegral.integral_zero]
    rw [integral_eq_full_of_box_support hgy]
    simp_rw [hgm]
    change (∫ y, ∫ x, f (p,(x,y))) = ∫ z : ℝ × ℝ, f (p,z)
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact (integral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (fun z => f (p,z)) (hfp.integrable_of_hasCompactSupport hfc)).symm
  rw [he] at hh
  exact hh

theorem exists_planar_unit_bump {A : ℝ} (hA : 0<A) :
    ∃ ρ : Plane → ℝ, ContDiff ℝ ∞ ρ ∧
      (∀ z, 0 ≤ ρ z) ∧ HasCompactSupport ρ ∧
      (∀ x y, A ≤ |x| ∨ A ≤ |y| → ρ (x,y)=0) ∧ (∫ z, ρ z)=1 := by
  let b : ContDiffBump (0:ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let r := b.normed volume
  have hrs : ContDiff ℝ ∞ r := b.contDiff_normed
  have hr0 (x : ℝ) (hx : A ≤ |x|) : r x=0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hh : |x|<A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hh
  let ρ : Plane → ℝ := fun z => r z.1*r z.2
  have hs : ContDiff ℝ ∞ ρ := (hrs.comp contDiff_fst).mul (hrs.comp contDiff_snd)
  have hz (x y : ℝ) (hxy : A ≤ |x| ∨ A ≤ |y|) : ρ (x,y)=0 := by
    rcases hxy with hx|hy
    · exact mul_eq_zero_of_left (hr0 x hx) _
    · exact mul_eq_zero_of_right _ (hr0 y hy)
  have hc : HasCompactSupport ρ := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) A)
    intro z hn
    have hh : A < max |z.1| |z.2| := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hn
    exact hz z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  refine ⟨ρ,hs,fun z => mul_nonneg (b.nonneg_normed (μ := volume) _) (b.nonneg_normed (μ := volume) _),hc,hz,?_⟩
  have hi := integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) ρ (hs.continuous.integrable_of_hasCompactSupport hc)
  change (∫ z : ℝ × ℝ, ρ z)=1
  rw [Measure.volume_eq_prod ℝ ℝ,hi]
  change (∫ x, ∫ y, r x*r y)=1
  simp_rw [integral_const_mul]
  rw [show (∫ y, r y)=1 from b.integral_normed]
  simp only [mul_one]
  exact b.integral_normed


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure SurfaceCoordinateBox (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M] where
  center : M
  point : Plane
  radius : ℝ
  radius_pos : 0 < radius
  closed_subset : Metric.closedBall point radius ⊆ (extChartAt 𝓘(ℝ,Plane) center).target

namespace SurfaceCoordinateBox

def carrier (B : SurfaceCoordinateBox M) : Set M :=
  (extChartAt 𝓘(ℝ,Plane) B.center).source ∩
    extChartAt 𝓘(ℝ,Plane) B.center ⁻¹' Metric.ball B.point B.radius

def compactCarrier (B : SurfaceCoordinateBox M) : Set M :=
  (extChartAt 𝓘(ℝ,Plane) B.center).symm '' Metric.closedBall B.point B.radius

theorem isOpen_carrier (B : SurfaceCoordinateBox M) : IsOpen B.carrier := by
  exact (continuousOn_extChartAt B.center).isOpen_inter_preimage
    (isOpen_extChartAt_source B.center) Metric.isOpen_ball

theorem isCompact_compactCarrier (B : SurfaceCoordinateBox M) : IsCompact B.compactCarrier := by
  exact (isCompact_closedBall B.point B.radius).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) B.center).mono B.closed_subset)

theorem compactCarrier_subset (B : SurfaceCoordinateBox M) :
    B.compactCarrier ⊆ (extChartAt 𝓘(ℝ,Plane) B.center).source := by
  rintro x ⟨y,hy,rfl⟩
  exact (extChartAt 𝓘(ℝ,Plane) B.center).map_target (B.closed_subset hy)

theorem carrier_subset_compactCarrier (B : SurfaceCoordinateBox M) :
    B.carrier ⊆ B.compactCarrier := by
  intro x hx
  exact ⟨extChartAt 𝓘(ℝ,Plane) B.center x,Metric.ball_subset_closedBall hx.2,
    (extChartAt 𝓘(ℝ,Plane) B.center).left_inv hx.1⟩

theorem nonempty_carrier (B : SurfaceCoordinateBox M) : B.carrier.Nonempty := by
  have hp : B.point ∈ (extChartAt 𝓘(ℝ,Plane) B.center).target :=
    B.closed_subset (Metric.mem_closedBall_self B.radius_pos.le)
  refine ⟨(extChartAt 𝓘(ℝ,Plane) B.center).symm B.point,
    (extChartAt 𝓘(ℝ,Plane) B.center).map_target hp,?_⟩
  change extChartAt 𝓘(ℝ,Plane) B.center ((extChartAt 𝓘(ℝ,Plane) B.center).symm B.point) ∈ Metric.ball B.point B.radius
  rw [(extChartAt 𝓘(ℝ,Plane) B.center).right_inv hp]
  exact Metric.mem_ball_self B.radius_pos

theorem exists_mem (x : M) : ∃ B : SurfaceCoordinateBox M, x ∈ B.carrier := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) x
  have hy := (extChartAt 𝓘(ℝ,Plane) x).map_source hx
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) x)
    _ hy
  have hs : Metric.closedBall (extChartAt 𝓘(ℝ,Plane) x x) (r/2) ⊆
      (extChartAt 𝓘(ℝ,Plane) x).target := by
    apply Subset.trans (Metric.closedBall_subset_ball (by linarith)) hrsub
  refine ⟨⟨x,extChartAt 𝓘(ℝ,Plane) x x,r/2,by positivity,hs⟩,hx,?_⟩
  exact Metric.mem_ball_self (by positivity)

theorem exists_compactCarrier_subset {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U) :
    ∃ B : SurfaceCoordinateBox M, x ∈ B.carrier ∧ B.compactCarrier ⊆ U := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) x
  have hy := (extChartAt 𝓘(ℝ,Plane) x).map_source hx
  have hS : IsOpen ((extChartAt 𝓘(ℝ,Plane) x).target ∩
      (extChartAt 𝓘(ℝ,Plane) x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hU
  have hxy : extChartAt 𝓘(ℝ,Plane) x x ∈
      (extChartAt 𝓘(ℝ,Plane) x).target ∩ (extChartAt 𝓘(ℝ,Plane) x).symm ⁻¹' U := by
    refine ⟨hy,?_⟩
    simpa only [mem_preimage,(extChartAt 𝓘(ℝ,Plane) x).left_inv hx] using hxU
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hS _ hxy
  have hs := (Metric.closedBall_subset_ball (x := extChartAt 𝓘(ℝ,Plane) x x)
    (show r/2<r by linarith)).trans hrsub
  let B : SurfaceCoordinateBox M :=
    ⟨x,extChartAt 𝓘(ℝ,Plane) x x,r/2,by positivity,hs.trans inter_subset_left⟩
  refine ⟨B,⟨hx,Metric.mem_ball_self (by dsimp [B]; positivity)⟩,?_⟩
  rintro z ⟨y,hy,rfl⟩
  exact (hs hy).2

theorem finite_partition [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
    {K : Set M} (hK : IsCompact K) :
    ∃ (s : Finset (SurfaceCoordinateBox M))
      (ρ : SmoothPartitionOfUnity s 𝓘(ℝ,Plane) M K),
        ρ.IsSubordinate (fun B => B.1.carrier) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun B : SurfaceCoordinateBox M => B.carrier)
    isOpen_carrier (fun x _ => mem_iUnion.mpr (exists_mem x))
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Plane) hK.isClosed
    (fun B : s => B.1.carrier) (fun B => B.1.isOpen_carrier) (by
      intro x hx
      obtain ⟨B,hBs,hxB⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨B,hBs⟩,hxB⟩)
  exact ⟨s,ρ,hρ⟩

end SurfaceCoordinateBox

end

section
open scoped ContDiff Topology
open Set
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialZeroExtension (S : Set E) (f : P × E → F) (q : P × E) : F := by
  classical
  exact if q.2 ∈ S then f q else 0

theorem spatialZeroExtension_smooth {S K : Set E} (hS : IsOpen S) (hK : IsClosed K)
    (hKS : K ⊆ S) {f : P × E → F} (hf : ContDiffOn ℝ ∞ f (univ ×ˢ S))
    (hz : ∀ p x, x ∈ S → x ∉ K → f (p,x)=0) :
    ContDiff ℝ ∞ (spatialZeroExtension S f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 ∈ S
  · have hs := hf.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _,hp⟩)
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hS.mem_nhds hp)] with q hq
    exact ite_eq_left hq
  · have hpk : p.2 ∉ K := fun hk => hp (hKS hk)
    apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hpk)] with q hq
    unfold spatialZeroExtension
    split_ifs with hqS
    · exact hz q.1 q.2 hqS hq
    · rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem spatialZeroExtension_zero {S K : Set E} {f : P × E → F}
    (hz : ∀ p x, x ∈ S → x ∉ K → f (p,x)=0) (p : P) {x : E} (hx : x ∉ K) :
    spatialZeroExtension S f (p,x)=0 := by
  unfold spatialZeroExtension
  split_ifs with hxS
  · exact hz p x hxS hx
  · rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem planar_skew_coefficient (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = -B v u) (u v : Plane) :
    B u v = B (1,0) (0,1)*planarArea u v := by
  have he := bilinear_skew_plane B u v
  rw [hB v u,hB (0,1) (1,0)] at he
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartTwoForm_change {Ω : ManifoldTwoForm Plane M} {c b : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) b).target)
    (hc : (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source) :
    chartTwoForm Ω b y =
      (chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackTwoForm_chart (Ω := fun _ => Ω) (p := (0,y)) hi hc
  simpa only [euclideanPullbackTwoForm,chartTwoForm,chartDifferential_inverse hy] using he

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartTwoForm_skew {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) (c : M) (y u v : Plane) :
    chartTwoForm Ω c y u v = -chartTwoForm Ω c y v u := by
  exact hΩ _ _ _

theorem chartTwoForm_density_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) b).target)
    (hc : (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source) :
    chartTwoForm Ω b y (1,0) (0,1) =
      (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det *
        chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y)) (1,0) (0,1) := by
  rw [chartTwoForm_change hy hc,ContinuousLinearMap.bilinearComp_apply,
    planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _), ← planar_det,mul_comm]

theorem chart_area_integral_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {K : Set M}
    (hK : IsCompact K)
    (hKb : K ⊆ (extChartAt 𝓘(ℝ,Plane) b).source)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K,
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det) :
    (∫ y in extChartAt 𝓘(ℝ,Plane) b '' K, chartTwoForm Ω b y (1,0) (0,1)) =
      ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K, chartTwoForm Ω c y (1,0) (0,1) := by
  let g : Plane → Plane := extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm
  have hyb {y : Plane} (hy : y ∈ extChartAt 𝓘(ℝ,Plane) b '' K) :
      y ∈ (extChartAt 𝓘(ℝ,Plane) b).target := by
    obtain ⟨x,hx,rfl⟩ := hy
    exact (extChartAt 𝓘(ℝ,Plane) b).map_source (hKb hx)
  have hyK {y : Plane} (hy : y ∈ extChartAt 𝓘(ℝ,Plane) b '' K) :
      (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ K := by
    obtain ⟨x,hx,rfl⟩ := hy
    simpa only [(extChartAt 𝓘(ℝ,Plane) b).left_inv (hKb hx)] using hx
  have hgs : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K, ContDiffAt ℝ ∞ g y := by
    intro y hy
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) b).mem_nhds (hyb hy))
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hKc (hyK hy))
    exact (ho.comp y hi).contDiffAt
  have hgi : InjOn g (extChartAt 𝓘(ℝ,Plane) b '' K) := by
    intro y hy z hz he
    apply (extChartAt 𝓘(ℝ,Plane) b).symm.injOn (hyb hy) (hyb hz)
    exact (extChartAt 𝓘(ℝ,Plane) c).injOn (hKc (hyK hy)) (hKc (hyK hz)) he
  have him : g '' (extChartAt 𝓘(ℝ,Plane) b '' K) = extChartAt 𝓘(ℝ,Plane) c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(extChartAt 𝓘(ℝ,Plane) b).symm z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨extChartAt 𝓘(ℝ,Plane) b x,⟨x,hx,rfl⟩,?_⟩
      exact congrArg (extChartAt 𝓘(ℝ,Plane) c) ((extChartAt 𝓘(ℝ,Plane) b).left_inv (hKb hx))
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) b).mono hKb)).measurableSet
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs y hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => chartTwoForm Ω c y (1,0) (0,1))
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) b).mono hKb)).measurableSet
  intro y hy
  dsimp only
  change chartTwoForm Ω b y (1,0) (0,1) =
    |(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det| •
      chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y)) (1,0) (0,1)
  rw [chartTwoForm_density_change hΩ (hyb hy) (hKc (hyK hy)),abs_of_pos (hpos y hy)]
  rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def extendedChartCoefficient (c : M) (Ω : P → ManifoldTwoForm Plane M) : P × Plane → ℝ :=
  spatialZeroExtension (extChartAt 𝓘(ℝ,Plane) c).target
    (fun q => chartTwoForm (Ω q.1) c q.2 (1,0) (0,1))

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem chartCoefficient_zero {c : M} {Ω : P → ManifoldTwoForm Plane M} {K : Set M}
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target)
    (hyk : y ∉ extChartAt 𝓘(ℝ,Plane) c '' K) :
    chartTwoForm (Ω p) c y (1,0) (0,1)=0 := by
  have hx : (extChartAt 𝓘(ℝ,Plane) c).symm y ∉ K := by
    intro hk
    exact hyk ⟨_,hk,(extChartAt 𝓘(ℝ,Plane) c).right_inv hy⟩
  simp only [chartTwoForm,hz p _ hx,ContinuousLinearMap.bilinearComp_apply,
    zero_apply]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem extendedChartCoefficient_zero {c : M} {Ω : P → ManifoldTwoForm Plane M} {K : Set M}
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) {y : Plane}
    (hy : y ∉ extChartAt 𝓘(ℝ,Plane) c '' K) : extendedChartCoefficient c Ω (p,y)=0 := by
  exact spatialZeroExtension_zero (fun p y hy hk => chartCoefficient_zero hz p hy hk) p hy

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in

theorem extendedChartCoefficient_smooth {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : ContDiffOn ℝ ∞ (fun q : P × Plane => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) : ContDiff ℝ ∞ (extendedChartCoefficient c Ω) := by
  have hcK := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)
  apply spatialZeroExtension_smooth (isOpen_extChartAt_target c) hcK.isClosed
  · rintro y ⟨x,hx,rfl⟩
    exact (extChartAt 𝓘(ℝ,Plane) c).map_source (hKc hx)
  · exact (hΩ.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  · intro p y hy hk
    exact chartCoefficient_zero hz p hy hk

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

theorem chartSupported_extendedCoefficient {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    {K : Set M} (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) :
    chartSupportedTwoForm c (fun y => extendedChartCoefficient c Ω (p,y) • planarArea) = Ω p := by
  funext x
  by_cases hx : x ∈ (extChartAt 𝓘(ℝ,Plane) c).source
  · have hy := (extChartAt 𝓘(ℝ,Plane) c).map_source hx
    unfold chartSupportedTwoForm extendedChartCoefficient spatialZeroExtension
    simp only [ite_eq_left hx,ite_eq_left hy]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,
      smul_eq_mul]
    rw [← planar_skew_coefficient _ (chartTwoForm_skew (hskew p) c _) ]
    exact chartTwoForm_apply_chart hx u v
  · unfold chartSupportedTwoForm
    rw [ite_eq_right hx,hz p x (fun hk => hx (hKc hk))]


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def chartMass (c : M) (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∫ y, extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)

theorem chartMass_eq_setIntegral {c : M} {Ω : ManifoldTwoForm Plane M} {K : Set M}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    chartMass c Ω = ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K, chartTwoForm Ω c y (1,0) (0,1) := by
  unfold chartMass
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => extendedChartCoefficient_zero (fun _ x hx => hz x hx) (0:ℝ) hy)]
  apply setIntegral_congr_fun
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)).measurableSet
  rintro y ⟨x,hx,rfl⟩
  exact ite_eq_left ((extChartAt 𝓘(ℝ,Plane) c).map_source (hKc hx))

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartMass_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {K : Set M}
    (hK : IsCompact K) (hKb : K ⊆ (extChartAt 𝓘(ℝ,Plane) b).source)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0)
    (hpos : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K,
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det) :
    chartMass b Ω = chartMass c Ω := by
  rw [chartMass_eq_setIntegral hK hKb hz,chartMass_eq_setIntegral hK hKc hz]
  exact chart_area_integral_change hΩ hK hKb hKc hpos

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in

theorem chartMass_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : ContDiffOn ℝ ∞ (fun q : P × Plane => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) : ContDiff ℝ ∞ (fun p => chartMass c (Ω p)) := by
  have hcK := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)
  obtain ⟨R,hR⟩ := hcK.isBounded.subset_closedBall (0:Plane)
  have hf := extendedChartCoefficient_smooth hΩ hK hKc hz
  change ContDiff ℝ ∞ (fun p => ∫ y, extendedChartCoefficient c Ω (p,y))
  apply planar_fixed_support_integral_smooth (A := max R 0+1) hf
  intro p x y hxy
  apply extendedChartCoefficient_zero hz p
  intro hxyK
  have hn : max |x| |y| ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using hR hxyK
  rcases hxy with hx|hy
  · have := (le_max_left |x| |y|).trans hn
    linarith [le_max_left R 0]
  · have := (le_max_right |x| |y|).trans hn
    linarith [le_max_left R 0]


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

@[simp] theorem chartOneForm_add (α β : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (α+β) c y = chartOneForm α c y + chartOneForm β c y := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

@[simp] theorem chartOneForm_smul (a : ℝ) (α : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (a • α) c y = a • chartOneForm α c y := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

@[simp] theorem chartOneForm_zero (c : M) (y : E) : chartOneForm (0 : ManifoldOneForm E M) c y=0 := rfl

@[simp] theorem chartTwoForm_add (Ω Λ : ManifoldTwoForm E M) (c : M) (y : E) :
    chartTwoForm (Ω+Λ) c y = chartTwoForm Ω c y + chartTwoForm Λ c y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp] theorem chartTwoForm_smul (a : ℝ) (Ω : ManifoldTwoForm E M) (c : M) (y : E) :
    chartTwoForm (a • Ω) c y = a • chartTwoForm Ω c y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp] theorem chartTwoForm_zero (c : M) (y : E) : chartTwoForm (0 : ManifoldTwoForm E M) c y=0 := rfl

theorem euclideanExteriorOneForm_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    euclideanExteriorOneForm (α+β) x =
      euclideanExteriorOneForm α x + euclideanExteriorOneForm β x := by
  rw [euclideanExteriorOneForm,fderiv_add hα hβ]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,add_apply]
  ring

theorem euclideanExteriorOneForm_smul (a : ℝ) {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) :
    euclideanExteriorOneForm (a • α) x = a • euclideanExteriorOneForm α x := by
  rw [euclideanExteriorOneForm,fderiv_const_smul hα]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,smul_apply,
    smul_eq_mul]
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
