import Mathlib
import OAI.Geometry.CubicTorus.Regularity.MinimalGraphDensity

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem strict_C1_cone_halfspace {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
      (ν : Measure BlowupNormalBundle) {z | z.1∈Metric.closedBall (0 : Cover) 1})
    (hcone : ∀ t : ℝ, 1≤t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (hC : ∀ p : Cover, ‖p‖<1 → p≠0 → p∈coverEssentialBoundary A → CoverC1BoundaryAt A p)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (h0 : (0 : Cover)∈coverEssentialBoundary A) :
    ∃ n : Cover, ‖n‖=1 ∧ ∀ᵐ x ∂(volume : Measure Cover), x∈Metric.ball (0 : Cover) 1 →
      (x∈A ↔ 0<⟪n,x⟫) := by
  have hposneg := h0 1 (by norm_num)
  have hpos : 0<volume (Metric.ball (0 : Cover) 1 ∩ A) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hposneg.1).1
  have hneg : 0<volume (Metric.ball (0 : Cover) 1 ∩ Aᶜ) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hposneg.2).1
  obtain ⟨p,hpn,hp0,hp⟩ := cover_boundary_nonzero hA (by norm_num : (0 : ℝ)<1) hpos hneg
  have hloc (q : Cover) (hq : q∈coverEssentialBoundary A) (hqn : ‖q‖<1) (hq0 : q≠0) :
      ∃ n : Cover, ‖n‖=1 ∧ ∀ᶠ x in 𝓝 q, x∈coverEssentialBoundary A ↔ ⟪n,x⟫=0 := by
    obtain ⟨a,n,g,R,ρ,hn,hg,hR,hρ,hgC,hsub,hgraph,hstat⟩ :=
      strict_C1_patch_stationary hA heq hflux hq hqn (hC q hqn hq0 hq)
    have hqR := hsub (Metric.mem_closedBall_self (by positivity : 0≤2*ρ))
    exact conical_stationary_patch_plane hcone hn hg hρ hgC hqR hq hqn hq0 hgraph hstat
  obtain ⟨n,hn,hall⟩ := closed_locally_planar_single_plane (coverEssentialBoundary_isClosed A) hloc hp hpn hp0
  rcases cover_boundary_plane_phases hA hn
    (fun x hx hb ↦ hall x (by simpa only [Metric.mem_ball,dist_zero_right] using hx) hb) hpos hneg with h|h
  · exact ⟨n,hn,h⟩
  · refine ⟨-n,by simpa using hn,?_⟩
    simpa only [inner_neg_left,neg_pos] using h

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quadratic_normal_closedBall_mass {ν : FiniteMeasure BlowupNormalBundle} {θ : ℝ}
    (hm : ∀ b : ℝ, 0<b → b<2 →
      (ν : Measure BlowupNormalBundle).real {z | z.1∈Metric.ball (0 : Cover) b}=θ*b^2) :
    (ν : Measure BlowupNormalBundle) {z | z.1∈Metric.closedBall (0 : Cover) 1}=ENNReal.ofReal θ := by
  have hl : θ≤(ν : Measure BlowupNormalBundle).real {z | z.1∈Metric.closedBall (0 : Cover) 1} := by
    have hh := measureReal_mono (μ := (ν : Measure BlowupNormalBundle))
      (show {z : BlowupNormalBundle | z.1∈Metric.ball (0 : Cover) 1} ⊆
        {z | z.1∈Metric.closedBall (0 : Cover) 1} from fun _ h ↦ Metric.ball_subset_closedBall h)
    simpa only [hm 1 (by norm_num) (by norm_num),one_pow,mul_one] using hh
  have hu : (ν : Measure BlowupNormalBundle).real {z | z.1∈Metric.closedBall (0 : Cover) 1}≤θ := by
    have ht : Tendsto (fun b : ℝ ↦ θ*b^2) (𝓝[>] 1) (𝓝 θ) := by
      have hh := (show ContinuousAt (fun b : ℝ ↦ θ*b^2) 1 by fun_prop).tendsto
      simpa using hh.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ)<2))] with b hb hb2
    have hh := measureReal_mono (μ := (ν : Measure BlowupNormalBundle))
      (show {z : BlowupNormalBundle | z.1∈Metric.closedBall (0 : Cover) 1} ⊆
        {z | z.1∈Metric.ball (0 : Cover) b} from fun _ h ↦ Metric.closedBall_subset_ball hb h)
    exact hh.trans_eq (hm b (by change 1 < b at hb; linarith) hb2)
  have he := le_antisymm hu hl
  rw [← he,Measure.real_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem isMinimizerAt_primary_halfspace {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    (r : ℕ → ℝ) (hr : ∀ i, 0<r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (n : Cover) (φ : ℕ → ℕ), ‖n‖=1 ∧ StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E cubeCenter (r (φ i)) x-
          (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) := by
  classical
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  obtain ⟨A,ν,θ,φ,hA,hθ,hφ,hconv,hper,hcomp,hcone,hm,hrad,hC,hflux⟩ :=
    isMinimizerAt_strict_C1_cone_blowup hV hE hmin hμ hH hcenter r hr hrlim
  have hconv1 : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E cubeCenter (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0) := by
    have hh := localL1_affine_tendsto
      (fun i ↦ measurable_blowupCharacteristic hE cubeCenter (r (φ i)))
      (fun i ↦ blowupCharacteristic_bound E cubeCenter (r (φ i)))
      (measurable_const.indicator hA) (cover_indicator_bound A) hconv (0 : Cover)
      (by norm_num : (0 : ℝ)<1)
      (by simpa only [one_mul] using (Metric.closedBall_subset_closedBall
        (by norm_num : (1 : ℝ)≤2) : Metric.closedBall (0 : Cover) 1 ⊆ Metric.closedBall (0 : Cover) 2))
    simpa only [one_smul,zero_add] using hh
  have h0 : (0 : Cover)∈coverEssentialBoundary A := by
    apply isMinimizerAt_rescaled_boundary_limit hV hE hmin (fun _ ↦ cubeCenter)
      (fun i ↦ r (φ i)) (fun i ↦ hr _) (hrlim.comp hφ.tendsto_atTop)
      (Eventually.of_forall (by simp)) hA hconv1 (fun _ ↦ 0)
      (by norm_num) tendsto_const_nhds
    apply Eventually.of_forall
    intro i
    simpa only [rescaledActualBoundary,mem_preimage,smul_zero,add_zero] using hcenter
  have heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
      (ν : Measure BlowupNormalBundle) {z | z.1∈Metric.closedBall (0 : Cover) 1} := by
    rw [hper 1 (by norm_num) (by norm_num),quadratic_normal_closedBall_mass hm]
    norm_num
  obtain ⟨n,hn,hhalf⟩ := strict_C1_cone_halfspace hA heq hcone hC hflux h0
  refine ⟨-n,φ,by simpa using hn,hφ,?_⟩
  apply localL1_limit_congr_ae_ball (f := A.indicator (fun _ ↦ (1 : ℝ))) _ hconv1
  filter_upwards [hhalf] with x hx hxb
  change (if x∈A then (1 : ℝ) else 0) = if x∈coverHalfspace (-n) then 1 else 0
  rw [propext (hx hxb)]
  simp only [coverHalfspace,mem_ofPred_eq,inner_neg_left,neg_lt_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_C1_graph {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r : ℝ), ‖n‖=1 ∧ 0<r ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
      (∀ y ∈ Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) := by
  classical
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  obtain ⟨R,hR,hcharts⟩ := MovingCenter.isMinimizerAt_moving_C1_graph hV hE hmin hcenter
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨δ,hδ,hchart⟩ := hcharts μ hμ N hN hp hu
  let e := δ/2
  have he : 0<e := half_pos hδ
  have heδ : e≤δ := by dsimp [e]; linarith
  let s : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have hs (i : ℕ) : 0<s i := by dsimp [s]; positivity
  have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n,φ,hn,hφ,hconv⟩ := isMinimizerAt_primary_halfspace hV hE hmin hcenter s hs hslim
  obtain ⟨η,hη,hsmall⟩ := isMinimizerAt_halfspace_L1_tilt_small hV hE hmin hμ hH hn
    (show 0<e^2/272^2 by positivity)
  have hlim := hslim.comp hφ.tendsto_atTop
  have hbound : 0 < min η (min (272*R) (min (272*δ*e^2) 1)) := by positivity
  obtain ⟨i,hi,hLi⟩ := ((hlim.eventually (Iio_mem_nhds hbound)).and
    (hconv.eventually (Iio_mem_nhds hη))).exists
  let t := s (φ i)
  have ht : 0<t := hs _
  have htη : t<η := hi.trans_le (min_le_left _ _)
  have htR : t/272≤R := by
    have hh := hi.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    change t < _ at hh
    linarith
  have hratio : (t/272)/e^2≤δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hi.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    change t < _ at hh
    linarith
  have ht1 : t<1 := hi.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let c : MovingCenter.InteriorCenter := ⟨cubeCenter,by simp⟩
  have htilt := hsmall c t ht htη hLi
  have hinterior : Metric.ball cubeCenter (t/8) ⊆ {x | ∀ j, 0<x j ∧ x j<1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := c) (by linarith))
  have htsp := spatial_tilt_le_blowupTilt hN hp hu cubeCenter n ht hinterior
  have hb : (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*(t/272)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (t/272)^2*e^2 := by
    rw [show 17*(t/272)=t/16 by ring]
    calc
      _ ≤ _ := htsp
      _ ≤ t^2*(e^2/272^2) := mul_le_mul_of_nonneg_left htilt.le (sq_nonneg _)
      _ = _ := by ring
  obtain ⟨g,hg,hgC,hinside,hcover⟩ := hchart cubeCenter (by simp) hcenter
    n (t/272) e hn (by positivity) htR he heδ hratio hb
  let r := (t/272)/1024
  have hr : 0<r := by dsimp [r]; positivity
  have hrepr0 := hcover cubeCenter ⟨hcenter,Metric.mem_ball_self (by positivity)⟩
  have hg0 : g 0=0 := by
    simp only [sub_self,map_zero] at hrepr0
    have hh := congrArg (fun x : Cover ↦ ⟪n,x⟫) hrepr0
    simpa only [normalGraph_inner hn,inner_zero_right] using hh
  refine ⟨n,g,r,hn,hr,hg,hg0,hgC,?_,?_⟩
  · intro y hy
    simpa only [quotientMap_add] using (hinside y hy).1
  · intro x hx
    constructor
    · intro hxb
      have hx' : cubeCenter+x∈Metric.ball cubeCenter ((t/272)/128) := by
        rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
        have hh : ‖x‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
        dsimp [r] at hh
        linarith
      simpa only [add_sub_cancel_left] using hcover (cubeCenter+x) ⟨hxb,hx'⟩
    · intro heq
      have hy : normalPlaneCoordinates n x∈Metric.ball (0 : Plane) r := by
        rw [Metric.mem_ball,dist_zero_right]
        exact (by simpa using (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0 : ‖normalPlaneCoordinates n x‖≤‖x‖).trans_lt
          (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
      have hh := (hinside (normalPlaneCoordinates n x) hy).1
      rw [heq] at hh
      simpa only [quotientMap_add] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeSupport_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    volumeSupport ((fun z ↦ z+b) ⁻¹' E) = (fun z ↦ z+b) ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : ((fun z ↦ z+b) ⁻¹' E) ∩ Metric.ball a r =
      (fun z ↦ z+b) ⁻¹' (E ∩ Metric.ball (a+b) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,dist_add_right]
  rw [he,Measure.real_def,Measure.real_def,
    volume_translation (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    openRepresentative ((fun z ↦ z+b) ⁻¹' E) =
      (fun z ↦ z+b) ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_translation hE.compl]
  rfl

lemma frontier_openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    frontier (openRepresentative ((fun z ↦ z+b) ⁻¹' E)) =
      (fun z ↦ z+b) ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_translation hE b]
  exact (Homeomorph.addRight b).preimage_frontier _ |>.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def TorusC1BoundaryAt (E : Set Torus) (a : Torus) : Prop :=
  ∃ (n : Cover) (g : Plane → ℝ) (r : ℝ), ‖n‖=1 ∧ 0<r ∧
    LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
    (∀ y∈Metric.ball (0 : Plane) r,
      a+quotientMap (normalGraph n g y)∈frontier (openRepresentative E)) ∧
    (∀ x∈Metric.ball (0 : Cover) r,
      a+quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x)

theorem isMinimizerAt_C1_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (a : Torus) (ha : a∈frontier (openRepresentative E)) : TorusC1BoundaryAt E a := by
  let b := a-quotientMap cubeCenter
  let F := (fun z : Torus ↦ z+b) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (continuous_add_const b).measurable
  have hminF : IsMinimizerAt V F := isMinimizerAt_translation hmin b
  have hbd : frontier (openRepresentative F)=(fun z : Torus ↦ z+b) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE b
  have hbase : quotientMap cubeCenter∈frontier (openRepresentative F) := by
    rw [hbd]
    change quotientMap cubeCenter+(a-quotientMap cubeCenter)∈frontier (openRepresentative E)
    convert ha using 1; abel
  obtain ⟨n,g,r,hn,hr,hg,hg0,hgC,hinside,hcover⟩ :=
    isMinimizerAt_centered_C1_graph hV hF hminF hbase
  have he (x : Cover) : quotientMap (cubeCenter+x)+b=a+quotientMap x := by
    rw [quotientMap_add]
    dsimp [b]
    abel
  refine ⟨n,g,r,hn,hr,hg,hg0,hgC,?_,?_⟩
  · intro y hy
    have hh := hinside y hy
    rw [hbd,mem_preimage,he] at hh
    exact hh
  · intro x hx
    have hh := hcover x hx
    rw [hbd,mem_preimage,he] at hh
    exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma torusVolume_lift_ball {E : Set Torus} (hE : MeasurableSet E)
    (x : Cover) (t : ℝ) (ht : Metric.ball x t ⊆ {y | ∀ i, 0<y i ∧ y i<1}) :
    torusVolume.real (E∩Metric.ball (quotientMap x) t)=
      volume.real ((quotientMap ⁻¹' E)∩Metric.ball x t) := by
  have hh := integral_blowupCharacteristic_ball_center hE (0 : Cover) x
    (by norm_num : (0 : ℝ)<1) t (by simpa only [one_smul,zero_add,one_mul] using ht)
  simp only [one_smul,zero_add,one_mul,one_pow] at hh
  rw [hh,← cover_integral_indicator_ball (hE.preimage measurable_quotientMap)]
  congr 1
  funext y
  classical
  by_cases hy : quotientMap y∈E <;>
    simp [blowupCharacteristic,characteristic,hy]

lemma coverEssentialBoundary_lift_iff {E : Set Torus} (hE : MeasurableSet E)
    {x : Cover} (hx : ∀ i, 0<x i ∧ x i<1) :
    x∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap x∈volumeSupport E ∩ volumeSupport Eᶜ := by
  have hO : IsOpen {y : Cover | ∀ i, 0<y i ∧ y i<1} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
        (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  have hs (t : ℝ) : Metric.ball x (min r t) ⊆ {y | ∀ i, 0<y i ∧ y i<1} :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hsub
  rw [mem_inter_iff,mem_volumeSupport_iff,mem_volumeSupport_iff]
  constructor
  · intro h
    constructor
    · intro t ht
      have hh := (h (min r t) (lt_min hr ht)).1
      rw [← torusVolume_lift_ball hE x (min r t) (hs t)] at hh
      exact hh.trans_le (measureReal_mono (μ := torusVolume)
        (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _))))
    · intro t ht
      have hh := (h (min r t) (lt_min hr ht)).2
      rw [← preimage_compl,← torusVolume_lift_ball hE.compl x (min r t) (hs t)] at hh
      exact hh.trans_le (measureReal_mono (μ := torusVolume)
        (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _))))
  · intro h t ht
    have h₁ := h.1 (min r t) (lt_min hr ht)
    have h₂ := h.2 (min r t) (lt_min hr ht)
    rw [torusVolume_lift_ball hE x (min r t) (hs t)] at h₁
    rw [torusVolume_lift_ball hE.compl x (min r t) (hs t),preimage_compl] at h₂
    have hmono (A : Set Cover) : volume.real (A∩Metric.ball x (min r t)) ≤
        volume.real (A∩Metric.ball x t) :=
      measureReal_mono (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_right _ _)))
    exact ⟨h₁.trans_le (hmono _),h₂.trans_le (hmono _)⟩

lemma isMinimizerAt_lifted_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {x : Cover} (hx : ∀ i, 0<x i ∧ x i<1) :
    x∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap x∈frontier (openRepresentative E) := by
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
  exact coverEssentialBoundary_lift_iff hE hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_phase_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (R ρ : ℝ) (U : Set Cover),
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ Metric.closedBall cubeCenter (2*ρ) ⊆ U ∧
      U ⊆ Metric.ball cubeCenter R ∧ U ⊆ {x | ∀ i, 0<x i ∧ x i<1} ∧
      (∀ x∈U, quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ((∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
       (∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))) := by
  obtain ⟨n,g,r,hn,hr,hg,hg0,hgC,hinside,hcover⟩ :=
    isMinimizerAt_centered_C1_graph hV hE hmin hcenter
  let R := r/2
  let s := min (r/4) (1/8)
  have hR : 0<R := half_pos hr
  have hs : 0<s := lt_min (by positivity) (by norm_num)
  have hsR : s<R := by dsimp [s,R]; exact (min_le_left _ _).trans_lt (by linarith)
  have hcell : Metric.ball cubeCenter s ⊆ {x | ∀ i, 0<x i ∧ x i<1} := by
    let c : MovingCenter.InteriorCenter := ⟨cubeCenter,by simp⟩
    apply Metric.ball_subset_closedBall.trans
    exact MovingCenter.closedBall_interior (c := c) (by
      have hh : s≤1/8 := min_le_right _ _
      linarith)
  have hb (x : Cover) (hx : x∈Metric.ball cubeCenter s) :
      quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter := by
    have hx' : x-cubeCenter∈Metric.ball (0 : Cover) r := by
      simp only [Metric.mem_ball,dist_zero_right]
      have hh : ‖x-cubeCenter‖<s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      have hsr : s<r := by dsimp [R] at hsR; linarith
      exact hh.trans hsr
    simpa only [add_sub_cancel] using hcover (x-cubeCenter) hx'
  have hlift (x : Cover) (hx : x∈Metric.ball cubeCenter s) :=
    isMinimizerAt_lifted_boundary hV hE hmin (hcell hx)
  have hp : cubeCenter∈coverEssentialBoundary (quotientMap ⁻¹' E) :=
    (hlift cubeCenter (Metric.mem_ball_self hs)).mpr hcenter
  obtain ⟨W,hW,hpW,hWU,hphase⟩ := cover_graph_boundary_phases
    (hE.preimage measurable_quotientMap) cubeCenter hn hg.continuous
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs)) hp
    (fun x hx ha ↦ (hb x hx).mp ((hlift x hx).mp ha))
  obtain ⟨t,ht,htW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let ρ := t/3
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  refine ⟨n,g,R,ρ,W,hn,hg,hg0,hR,hρ,?_,hW,?_,?_,hWU.trans hcell,
    fun x hx ↦ hb x (hWU hx),hphase.symm⟩
  · intro y hy
    apply hgC.contDiffAt
    apply Metric.isOpen_ball.mem_nhds
    apply Metric.closedBall_subset_ball _ hy
    dsimp [R]
    linarith
  · exact (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)).trans htW
  · exact hWU.trans (Metric.ball_subset_ball hsR.le)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_C1graph_CMC {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ {x | ∀ i, 0<x i ∧ x i<1} →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y∈Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i, 0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x, φ x∈Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsF : HasCompactSupport F)
    (hφF : ∀ x∈tsupport F, φ x=1) :
    (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
      (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=
      H*(∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫) := by
  let ν := normalCoverMeasure μ
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F⊆{x | ∀ i, 0<x i ∧ x i<1})
      (_hb : ∀ x, ‖F x‖≤1) := normalCoverMeasure_local_flux hE hμ hF hs hO
  have hsφF : tsupport F⊆tsupport φ := fun x hx ↦ subset_tsupport _ (by
    rw [Function.mem_support,hφF x hx]; exact one_ne_zero)
  have hFO := hsφF.trans hφO
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫<graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  rw [cutoff_C1graph_firstVariation (hE.preimage measurable_quotientMap) a hn hg hc hgraph
    (normalMeasure_cutoff_saturation hμ _) hflux hφ hsφ hφU hφO hφR hφb hF hsF hφF]
  rw [normalCoverMeasure_integral (continuous_blowupTangentTest hF)]
  change (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) = _
  rw [hCMC F hF hsF hFO]
  congr 1
  change (∫ z : NormalBundle, ⟪((normalCoverMap z).2 : Cover),F (normalCoverMap z).1⟫ ∂(μ : Measure NormalBundle)) = _
  rw [← normalCoverMeasure_integral (μ := μ) (f := fun z ↦ ⟪(z.2 : Cover),F z.1⟫) (by fun_prop)]
  rw [normalCoverMeasure_local_flux hE hμ hF hsF hFO,
    setIntegral_divergence_congr_local (hE.preimage measurable_quotientMap) hm hgraph
      (hsφF.trans hφU),setIntegral_graphSublevel_divergence a hn hg hc hF (hsφF.trans hφR)]

lemma reverseNormal_local_CMC {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D=H*directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F⊆{x | ∀ i, 0<x i ∧ x i<1}) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ.map reverseNormal : Measure NormalBundle))=
      (-H)*(∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ.map reverseNormal : Measure NormalBundle)) := by
  rw [FiniteMeasure.toMeasure_map,
    integral_map continuous_reverseNormal.measurable.aemeasurable
      (continuous_tangentialDivergence hF).aestronglyMeasurable,
    integral_map continuous_reverseNormal.measurable.aemeasurable
      (show Continuous (fun z : NormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) from by fun_prop).aestronglyMeasurable]
  change (∫ z : NormalBundle, tangentialDivergence F z.1 (-(z.2 : Cover)) ∂(μ : Measure NormalBundle)) =
    (-H)*(∫ z : NormalBundle, ⟪-(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle))
  simp_rw [tangentialDivergence_neg_normal,inner_neg_left,integral_neg,neg_mul_neg]
  exact weakCMC_local_identity hμ hH hF hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_CMC_graph {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (R ρ H : ℝ),
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      Metric.closedBall cubeCenter (2*ρ)⊆Metric.ball cubeCenter R ∧
      (∀ x∈Metric.closedBall cubeCenter (2*ρ), quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F⊆Metric.closedBall cubeCenter ρ →
        (∫ y : Plane, tangentialDivergence F (cubeCenter+normalGraph n g y)
          (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=
          H*(∫ y : Plane, ⟪graphAreaVector n g y,F (cubeCenter+normalGraph n g y)⟫) := by
  obtain ⟨n,g,R,ρ,U,hn,hg,hg0,hR,hρ,hgc,hU,hρU,hUR,hUO,hbd,hphase⟩ :=
    isMinimizerAt_centered_phase_patch hV hE hmin hcenter
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
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
    (hgc y hy).continuousAt_fderiv (by norm_num)
  rcases hphase with hphase|hphase
  · have hp : ∀ᵐ x : Cover ∂volume, x∈U →
        (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
      simpa only [graphSignedHeight,sub_neg] using hphase
    refine ⟨n,g,R,ρ,H,hn,hg,hg0,hR,hρ,hgc,hρU.trans hUR,
      fun x hx ↦ hbd x (hρU hx),?_⟩
    intro F hF hsF
    have hFs : HasCompactSupport F := (isCompact_closedBall cubeCenter ρ).of_isClosed_subset isClosed_closure hsF
    exact normalMeasure_C1graph_CMC hE hμ
      (fun F hF hc hs ↦ weakCMC_local_identity hμ hH hF hc hs)
      cubeCenter hn hg hdc hp hφ hsφ hφU hφO hφR hφb hF hFs
      (fun x hx ↦ radialHeightCutoff_one hρ (hsF hx))
  · have hp : ∀ᵐ x : Cover ∂volume, x∈U →
        (x∈(quotientMap ⁻¹' E) ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
    have hp' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hp
    have hμ' := isNormalMeasure_compl hE hμ
    refine ⟨n,g,R,ρ,-H,hn,hg,hg0,hR,hρ,hgc,hρU.trans hUR,
      fun x hx ↦ hbd x (hρU hx),?_⟩
    intro F hF hsF
    have hFs : HasCompactSupport F := (isCompact_closedBall cubeCenter ρ).of_isClosed_subset isClosed_closure hsF
    exact normalMeasure_C1graph_CMC hE.compl hμ'
      (fun F hF hc hs ↦ reverseNormal_local_CMC hμ hH hF hc hs)
      cubeCenter hn hg hdc hp' hφ hsφ hφU hφO hφR hφb hF hFs
      (fun x hx ↦ radialHeightCutoff_one hρ (hsF hx))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CMC_graph_weak_equation (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (H : ℝ) {p : Cover} {ρ : ℝ} (hρ : 0<ρ)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=
        H*(∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : ∀ y ∈ tsupport ψ, a+normalGraph n g y ∈ Metric.ball p (ρ/2)) :
    (∫ y : Plane, fderiv ℝ ψ y (gradient g y)/‖graphAreaVector n g y‖)=H*(∫ y : Plane, ψ y) := by
  let ζ := radialHeightCutoff p (ρ/2)
  let f := graphHeightExtension a n ψ
  let F : Cover → Cover := fun x ↦ (ζ x*f x) • n
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := radialDensityWeight_contDiff _ _ _
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := graphHeightExtension_contDiff a n hψ
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (hζ.mul hf).smul contDiff_const
  have hsF : tsupport F ⊆ Metric.closedBall p ρ := by
    have hsζ : tsupport ζ ⊆ Metric.closedBall p ρ := by
      have hh := radialDensityWeight_tsupport (a := p) (r := 2*(ρ/2))
        (ε := 3*(ρ/2)^2) (by positivity) (by positivity)
      convert hh using 1 <;> congr 1; ring
    apply Subset.trans _ hsζ
    apply closure_mono
    intro x hx
    by_contra hh
    exact hx (by simp [F,Function.notMem_support.mp hh])
  have he (y : Plane) : tangentialDivergence F (a+normalGraph n g y)
      (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖ =
      fderiv ℝ ψ y (gradient g y)/‖graphAreaVector n g y‖ := by
    let x := a+normalGraph n g y
    have hxy : normalPlaneCoordinates n (x-a)=y := by
      simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
    by_cases hy : y ∈ tsupport ψ
    · have hz : ζ =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
        radialHeightCutoff_eventually_one (by positivity) (hsψ y hy)
      have hFe : F =ᶠ[𝓝 x] (fun z ↦ f z • n) := by
        filter_upwards [hz] with z hz
        simp only [F,hz,one_mul]
      have hde := hFe.fderiv_eq (𝕜 := ℝ)
      have hte : tangentialDivergence F x (graphSlopeNormal n (gradient g y)) =
          tangentialDivergence (fun z ↦ f z • n) x (graphSlopeNormal n (gradient g y)) := by
        simp only [tangentialDivergence,divergence,hde]
      change tangentialDivergence F x _ * _ = _
      rw [hte]
      exact graph_vertical_variation a hn g (hψ.differentiable (by simp)) y
    · have hψ0 : ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hy
      have hf0 : f =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
        have hp := ((normalPlaneCoordinates n).continuous.comp (continuous_id.sub (continuous_const (y := a)))).tendsto x
        change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x)
          (𝓝 (normalPlaneCoordinates n (x-a))) at hp
        rw [hxy] at hp
        exact hp.eventually hψ0
      have hF0 : F =ᶠ[𝓝 x] (fun _ ↦ (0 : Cover)) := by
        filter_upwards [hf0] with z hz
        simp only [F,hz,mul_zero,zero_smul]
      have hd0 := hF0.fderiv_eq (𝕜 := ℝ)
      have hψd0 := hψ0.fderiv_eq (𝕜 := ℝ)
      change tangentialDivergence F x _ * _ = _
      simp [tangentialDivergence,divergence,hd0,hψd0]
  have hflux (y : Plane) : ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫=ψ y := by
    have hninner : ⟪graphAreaVector n g y,n⟫=1 := by
      have hz : ⟪normalPlaneEmbedding n (gradient g y),n⟫=0 :=
        (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn _)
      rw [graphAreaVector,inner_sub_left,real_inner_self_eq_norm_sq,hn,one_pow,hz,sub_zero]
    have hfgraph : f (a+normalGraph n g y)=ψ y := by
      simp only [f,graphHeightExtension,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
    simp only [F,inner_smul_right,hninner,mul_one,hfgraph]
    by_cases hy : y∈tsupport ψ
    · change radialHeightCutoff p (ρ/2) (a+normalGraph n g y)*ψ y=ψ y
      rw [radialHeightCutoff_one (by positivity) (Metric.ball_subset_closedBall (hsψ y hy)),one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy,mul_zero]
  simpa only [he,hflux] using hstat F hF hsF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcFlux (p : Plane) : Plane := (Real.sqrt (1+‖p‖^2))⁻¹ • p

def WeakCMCGraph (g : Plane → ℝ) (H : ℝ) (U : Set Plane) : Prop :=
  ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆U →
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g y)))=H*(∫ y, ψ y)

theorem isMinimizerAt_centered_weakCMC_graph {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r H : ℝ), ‖n‖=1 ∧ 0<r ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      WeakCMCGraph g H (Metric.ball 0 r) := by
  obtain ⟨n,g,R,ρ,H,hn,hg,hg0,hR,hρ,hgc,hρR,hbd,hCMC⟩ :=
    isMinimizerAt_centered_CMC_graph hV hE hmin hcenter
  let r := min (R/2) (ρ/4)
  have hr : 0<r := lt_min (by positivity) (by positivity)
  have hrR : r<R := (min_le_left _ _).trans_lt (by linarith)
  have hrρ : r≤ρ/4 := min_le_right _ _
  have hgb (y : Plane) : ‖normalGraph n g y‖≤(5/4)*‖y‖ := by
    have hh := (normalGraph_lipschitz hn hg).dist_le_mul y 0
    have hz : normalGraph n g 0=0 := by
      change normalPlaneLinearIsometry n 0+g 0 • n=0
      rw [map_zero,hg0,zero_smul,zero_add]
    rw [hz] at hh
    norm_num only [dist_zero_right,NNReal.coe_add,NNReal.coe_one,NNReal.coe_div,
      NNReal.coe_ofNat] at hh ⊢
    exact hh
  have hry (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) :
      cubeCenter+normalGraph n g y∈Metric.ball cubeCenter (ρ/2) := by
    rw [Metric.mem_ball,dist_self_add_left]
    have hyl : ‖y‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    have hh := hgb y
    nlinarith
  refine ⟨n,g,r,H,hn,hr,hg,hg0,?_,?_,?_,?_⟩
  · intro y hy
    exact (hgc y (Metric.ball_subset_closedBall ((Metric.ball_subset_ball hrR.le) hy))).contDiffWithinAt
  · intro y hy
    have hx := Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by linarith : ρ/2≤2*ρ)) (hry y hy))
    apply (hbd _ hx).mpr
    simp only [add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  · intro x hx
    have hx' : cubeCenter+x∈Metric.closedBall cubeCenter (2*ρ) := by
      rw [Metric.mem_closedBall,dist_self_add_left]
      have hh : ‖x‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
      linarith
    simpa only [add_sub_cancel_left] using hbd (cubeCenter+x) hx'
  · intro ψ hψ _hsψ hsψ
    have hh := CMC_graph_weak_equation cubeCenter hn g H hρ hCMC hψ (fun y hy ↦ hry y (hsψ hy))
    simpa only [cmcFlux,map_smul,smul_eq_mul,graphAreaVector_norm_sqrt hn,div_eq_mul_inv,
      mul_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcWeight (p : Plane) : ℝ := Real.sqrt (1+‖p‖^2)

def cmcJacobian (p : Plane) : Plane →L[ℝ] Plane :=
  (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane -
    ((cmcWeight p)^3)⁻¹ • (innerSL ℝ p).smulRight p

lemma cmcWeight_pos (p : Plane) : 0<cmcWeight p := by
  exact Real.sqrt_pos.2 (by positivity)
lemma cmcWeight_sq (p : Plane) : (cmcWeight p)^2=1+‖p‖^2 :=
  Real.sq_sqrt (by positivity)
lemma cmcWeight_ge_one (p : Plane) : 1≤cmcWeight p := by
  have hp := cmcWeight_sq p
  have hh := cmcWeight_pos p
  nlinarith [sq_nonneg ‖p‖]
lemma cmcWeight_le_two {p : Plane} (hp : ‖p‖≤1) : cmcWeight p≤2 := by
  have hh := cmcWeight_sq p
  nlinarith [sq_nonneg (cmcWeight p),norm_nonneg p]

lemma cmcWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcWeight := by
  apply (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
  intro p
  positivity

lemma cmcFlux_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcFlux :=
  (cmcWeight_contDiff.inv (fun p ↦ (cmcWeight_pos p).ne')).smul contDiff_id

lemma cmcWeight_hasFDerivAt (p : Plane) :
    HasFDerivAt cmcWeight ((cmcWeight p)⁻¹ • innerSL ℝ p) p := by
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1 : ℝ)+‖p‖^2≠0)
  change HasFDerivAt cmcWeight ((1/(2*cmcWeight p)) • (2 • innerSL ℝ p)) p at h
  have he : (1/(2*cmcWeight p)) • (2 • innerSL ℝ p) =
      (cmcWeight p)⁻¹ • innerSL ℝ p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  exact he ▸ h

lemma cmcFlux_hasFDerivAt (p : Plane) : HasFDerivAt cmcFlux (cmcJacobian p) p := by
  have h := ((hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt p (cmcWeight_hasFDerivAt p)).smul (hasFDerivAt_id p)
  have he : (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane +
      ((-((cmcWeight p)^2)⁻¹) • ((cmcWeight p)⁻¹ • innerSL ℝ p)).smulRight p =
      cmcJacobian p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cmcJacobian,add_apply,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,smul_smul]
    have hc : -((cmcWeight p)^2)⁻¹*(cmcWeight p)⁻¹*⟪p,v⟫ =
        -(((cmcWeight p)^3)⁻¹*⟪p,v⟫) := by field_simp
    rw [hc,neg_smul,sub_eq_add_neg]
  exact he ▸ h

lemma cmcJacobian_apply (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • v -
      (((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcJacobian,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcJacobian_self (p v : Plane) :
    ⟪v,cmcJacobian p v⟫=
      ((cmcWeight p)^2*‖v‖^2-⟪p,v⟫^2)/(cmcWeight p)^3 := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v p]
  field_simp

lemma cmcJacobian_coercive {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/8)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  have hs := cmcWeight_pos p
  have hsq := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  have h8 : (cmcWeight p)^3≤8 := by
    have hh := cmcWeight_le_two hp
    nlinarith [sq_nonneg (cmcWeight p-2)]
  rw [cmcJacobian_self,le_div_iff₀ (by positivity : 0<(cmcWeight p)^3)]
  have hh := mul_le_mul_of_nonneg_right h8 (sq_nonneg ‖v‖)
  nlinarith [sq_nonneg ⟪p,v⟫]

lemma cmcJacobian_norm_le {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcJacobian p v‖≤2*‖v‖ := by
  have hs := cmcWeight_ge_one p
  have hs0 := cmcWeight_pos p
  have hsi : (cmcWeight p)⁻¹≤1 := inv_le_one₀ hs0 |>.mpr hs
  have hs3 : ((cmcWeight p)^3)⁻¹≤1 := by
    apply (inv_le_one₀ (by positivity : 0<(cmcWeight p)^3)).mpr
    nlinarith [sq_nonneg (cmcWeight p-1)]
  rw [cmcJacobian_apply]
  calc
    _ ≤ ‖(cmcWeight p)⁻¹ • v‖ + ‖(((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = (cmcWeight p)⁻¹*‖v‖+((cmcWeight p)^3)⁻¹*|⟪p,v⟫| *‖p‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr hs0.le),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs0.le 3))]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _) hsi
      · apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hs3) (norm_nonneg _)).trans
        apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
        exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
          (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

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
