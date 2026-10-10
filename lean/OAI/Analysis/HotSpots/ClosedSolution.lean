import OAI.Analysis.HotSpots.Multiplier

namespace OAI

section ClosedChartTopology

noncomputable section
open Set Metric
open scoped Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma complex_maps_disk {z : ℂ} (hz : z ∈ ball 0 1) : c.F (complexIso z) ∈ Ω := by
  have hx : complexIso z ∈ disk := by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hz
  rw [← c.diskMap_agrees hx]
  exact c.diskMap.map_source hx

lemma complex_maps_closed {z : ℂ} (hz : z ∈ closedBall 0 1) : c.F (complexIso z) ∈ closure Ω := by
  apply c.maps_closed
  simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_closedBall_zero_iff,
    LinearIsometryEquiv.norm_map] using hz

lemma complex_maps_boundary (s : Circle) : c.F (complexIso (s:ℂ)) ∈ frontier Ω := by
  apply c.maps_boundary
  simp only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm,
    LinearIsometryEquiv.norm_map,Circle.norm_coe]

lemma complex_inverse_disk {x : Plane} (hx : x ∈ Ω) : complexIso.symm (c.G x) ∈ ball 0 1 := by
  have hh := c.diskMap.map_target hx
  change c.diskMap.symm x ∈ disk at hh
  rw [c.diskMap_inverse_agrees hx] at hh
  simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hh

lemma complex_inverse_boundary {x : Plane} (hx : x ∈ frontier Ω) : ‖complexIso.symm (c.G x)‖ = 1 := by
  have hh := c.inverse_maps_boundary hx
  simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_sphere_zero_iff_norm,
    LinearIsometryEquiv.norm_map] using hh

lemma complex_inverse_image (S : Set Plane) (hs : S ⊆ Ω) :
    (fun x => complexIso.symm (c.G x)) '' S = ball 0 1 ∩ (fun z => c.F (complexIso z)) ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨c.complex_inverse_disk (hs hx),?_⟩
    simpa only [mem_preimage,LinearIsometryEquiv.apply_symm_apply,c.right_inverse x (subset_closure (hs hx))] using hx
  · rintro ⟨hz,hx⟩
    refine ⟨c.F (complexIso z),hx,?_⟩
    have hd : complexIso z ∈ closure disk := by
      exact subset_closure (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hz)
    change complexIso.symm (c.G (c.F (complexIso z))) = z
    rw [c.left_inverse _ (c.source_eq.symm ▸ hd),LinearIsometryEquiv.symm_apply_apply]

lemma connected_complex_pull {v : Plane → ℝ} {P : Set ℝ}
    (hcon : IsConnected (Ω ∩ v ⁻¹' P)) :
    IsConnected (ball (0:ℂ) 1 ∩ (fun z => v (c.F (complexIso z))) ⁻¹' P) := by
  have hh := hcon.image (fun x => complexIso.symm (c.G x))
    (complexIso.symm.continuous.comp c.inverse_lipschitz.continuous).continuousOn
  rw [c.complex_inverse_image _ inter_subset_left] at hh
  convert hh using 1
  ext z
  constructor
  · rintro ⟨hz,hv⟩
    exact ⟨hz,c.complex_maps_disk hz,hv⟩
  · rintro ⟨hz,_,hv⟩
    exact ⟨hz,hv⟩


def circleBoundaryHomeomorph : Circle ≃ₜ frontier Ω := by
  classical
  let f : Circle → frontier Ω := fun s => ⟨c.F (complexIso (s:ℂ)),c.complex_maps_boundary s⟩
  let g : frontier Ω → Circle := fun x => ⟨complexIso.symm (c.G x),
    mem_sphere_zero_iff_norm.mpr (c.complex_inverse_boundary x.property)⟩
  have hleft : Function.LeftInverse g f := by
    intro s
    apply Subtype.ext
    have hd : complexIso (s:ℂ) ∈ closure disk := by
      simp only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_closedBall_zero_iff,
        LinearIsometryEquiv.norm_map,Circle.norm_coe,le_refl]
    change complexIso.symm (c.G (c.F (complexIso (s:ℂ)))) = (s:ℂ)
    rw [c.left_inverse _ (c.source_eq.symm ▸ hd),LinearIsometryEquiv.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    change c.F (complexIso (complexIso.symm (c.G x))) = x
    rw [LinearIsometryEquiv.apply_symm_apply,c.right_inverse x x.property.1]
  exact {
    toFun := f
    invFun := g
    left_inv := hleft
    right_inv := hright
    continuous_toFun := (c.lipschitz.continuous.comp (complexIso.continuous.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun := (complexIso.symm.continuous.comp (c.inverse_lipschitz.continuous.comp continuous_subtype_val)).subtype_mk _ }

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedChartTopology

section BoundaryCoordinateExtension

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



theorem boundary_scalar_extension {f : Boundary → ℝ} {B : ℝ≥0} (hf : LipschitzWith B f) :
    ∃ (g : Plane → ℝ) (A : ℝ≥0), LipschitzWith A g ∧ ∀ s : Boundary, g (c.F s) = f s := by
  classical
  let f' (x : Plane) := if h : ‖x‖ = 1 then f ⟨x,h⟩ else 0
  have hl : LipschitzOnWith B f' {x : Plane | ‖x‖ = 1} := by
    intro x hx y hy
    change ‖x‖ = 1 at hx
    change ‖y‖ = 1 at hy
    simpa only [f',dite_eq_left hx,dite_eq_left hy,Subtype.edist_eq] using hf ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,he⟩ := hl.extend_real
  refine ⟨g ∘ c.G,B*c.InvLip,hg.comp c.inverse_lipschitz,?_⟩
  intro s
  change g (c.G (c.F s)) = f s
  rw [c.left_inverse s (c.source_eq.symm ▸ (by simp only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_closedBall_zero_iff,s.property,le_refl]))]
  exact (he s.property).symm.trans (by simp only [f',dite_eq_left s.property])
end StrictHotSpots.Conformal.ClosedDiskChart
namespace StrictHotSpots.HilbertMultipliers
lemma coordinate_lipschitz {H S ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [PseudoMetricSpace S] (e : HilbertBasis ι ℝ H) {b : S → H} {B : ℝ≥0}
    (hb : LipschitzWith B b) (i : ι) : LipschitzWith B (fun s => inner ℝ (e i) (b s)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,← inner_sub_right]
  calc
    |inner ℝ (e i) (b s-b t)| ≤ ‖e i‖*‖b s-b t‖ := abs_real_inner_le_norm _ _
    _ = ‖b s-b t‖ := by rw [e.orthonormal.1 i,one_mul]
    _ ≤ B*dist s t := by simpa only [dist_eq_norm] using hb.dist_le_mul s t
end StrictHotSpots.HilbertMultipliers
end
end BoundaryCoordinateExtension

section GreenClosedContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma norm_le_of_mem_closure_disk {x : Plane} (hx : x ∈ closure disk) : ‖x‖ ≤ 1 := by
  simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
    mem_closedBall_zero_iff] using hx

lemma mem_disk_of_norm_lt {x : Plane} (hx : ‖x‖ < 1) : x ∈ disk := by
  simpa only [disk,mem_ball_zero_iff] using hx

lemma kernel_zero_left {x : Plane} (hx : ‖x‖ = 1) (y : Plane) : kernel x y = 0 := by
  simp [kernel_plane_formula,hx]

lemma kernel_continuousAt_left_closed {x y : Plane} (hx : x ∈ closure disk)
    (hy : y ∈ disk) (hxy : x ≠ y) : ContinuousAt (fun z => kernel z y) x := by
  have hx1 := norm_le_of_mem_closure_disk hx
  have hy1 : ‖y‖ < 1 := by simpa only [disk,mem_ball_zero_iff] using hy
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hy2 : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hn : ‖x-y‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  have ha : 1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2 ≠ 0 := by positivity
  simp_rw [kernel_plane_formula]
  fun_prop (disch := assumption)

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma kernel_memLp_closed (x : Plane) (hx : x ∈ closure disk) : MemLp (kernel x) 2 ν := by
  by_cases hi : ‖x‖ < 1
  · exact kernel_memLp_weighted hC hν x (mem_disk_of_norm_lt hi)
  · have hn : ‖x‖ = 1 := le_antisymm (norm_le_of_mem_closure_disk hx) (not_lt.mp hi)
    have he : kernel x = 0 := funext (kernel_zero_left hn)
    rw [he]
    exact MemLp.zero

include hC hν in
lemma kernel_uniform_three_bound_closed : ∃ B : ℝ≥0∞, B ≠ ∞ ∧
    ∀ x ∈ closure disk, eLpNorm (kernel x) 3 ν ≤ B := by
  obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_weighted hC hν
  refine ⟨B,hB,fun x hx => ?_⟩
  by_cases hi : ‖x‖ < 1
  · exact h x (mem_disk_of_norm_lt hi)
  · have hn : ‖x‖ = 1 := le_antisymm (norm_le_of_mem_closure_disk hx) (not_lt.mp hi)
    have he : kernel x = 0 := funext (kernel_zero_left hn)
    rw [he,eLpNorm_zero]
    exact bot_le


def closedRow (x : closure disk) : Lp ℝ 2 ν :=
  (kernel_memLp_closed hC hν x x.property).toLp (kernel x)

lemma closedRow_coe_ae (x : closure disk) : closedRow hC hν x =ᵐ[ν] kernel x :=
  (kernel_memLp_closed hC hν x x.property).coeFn_toLp



lemma closedRow_continuous [IsFiniteMeasure ν] : Continuous (closedRow hC hν) := by
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  simp only [Function.comp_def,closedRow]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => kernel (u n))
    (fun n => kernel_memLp_closed hC hν _ (u n).property) (kernel x)
    (kernel_memLp_closed hC hν _ x.property)).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (kernel_memLp_closed hC hν _ (u n).property).aestronglyMeasurable)
    (kernel_memLp_closed hC hν _ x.property)
  · obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_closed hC hν
    exact L2Limits.unifIntegrable_two_of_three
      (fun n => (kernel_memLp_closed hC hν _ (u n).property).aestronglyMeasurable)
      hB (fun n => h _ (u n).property)
  · have hne : ∀ᵐ y ∂ν, y ≠ (x:Plane) :=
      ((volume.restrict disk).ae_ne (x:Plane)).filter_mono
        (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    filter_upwards [ae_mem_disk hν,hne] with y hyd hyx
    exact (kernel_continuousAt_left_closed x.property hyd hyx.symm).tendsto.comp
      ((continuous_subtype_val.tendsto x).comp hu)

lemma green_integral_eq_closedInner (f : Lp ℝ 2 ν) (x : closure disk) :
    (∫ y, kernel x y*f y ∂ν) = inner ℝ (closedRow hC hν x) f := by
  rw [MeasurableL2Kernel.integral_mul_eq_inner
    (kernel_memLp_closed hC hν x x.property) (Lp.memLp f),Lp.toLp_coeFn]
  rfl

include hC hν in
lemma green_integral_continuousOn_closure [IsFiniteMeasure ν] (f : Lp ℝ 2 ν) :
    ContinuousOn (fun x : Plane => ∫ y, kernel x y*f y ∂ν) (closure disk) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun x : closure disk => ∫ y, kernel x y*f y ∂ν)
  simp_rw [green_integral_eq_closedInner hC hν]
  exact (closedRow_continuous hC hν).inner continuous_const

lemma green_integral_boundary (f : Lp ℝ 2 ν) {x : Plane} (hx : x ∈ frontier disk) :
    (∫ y, kernel x y*f y ∂ν) = 0 := by
  have hn : ‖x‖ = 1 := by
    simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
      mem_sphere_zero_iff_norm] using hx
  simp only [kernel_zero_left hn,zero_mul,integral_zero]

end StrictHotSpots.PlaneGreen
end
end GreenClosedContinuous

section BoundaryClosedSolution

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

def boundaryClosedPoisson (f : C(Boundary,ℝ)) : Plane → ℝ :=
  Douglas.closedPlanePoisson (boundaryAngleData f)

lemma boundaryClosedPoisson_interior (f : C(Boundary,ℝ)) {x : Plane} (hx : x ∈ disk) :
    boundaryClosedPoisson f x = poissonExtension f x :=
  (Douglas.closedPlanePoisson_eqOn (boundaryAngleData f) hx).trans
    (poissonExtension_eq_planePoisson f hx).symm

lemma boundaryClosedPoisson_trace (f : C(Boundary,ℝ)) (s : Boundary) :
    boundaryClosedPoisson f s = f s := by
  obtain ⟨t,rfl⟩ := angleBoundary.surjective s
  rw [angleBoundary_coe]
  exact Douglas.closedPlanePoisson_boundary (boundaryAngleData f) t

lemma boundaryClosedPoisson_continuousOn (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) : ContinuousOn (boundaryClosedPoisson f) (closure disk) :=
  Douglas.closedPlanePoisson_continuousOn (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf)

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)



def boundaryClosedSolution (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) (x : Plane) : ℝ :=
  boundaryClosedPoisson f x + ∫ y, kernel x y *
    (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
      (poissonL2 hν f.continuous.measurable hB)) y ∂ν

lemma boundaryClosedSolution_interior (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) {x : Plane} (hx : x ∈ disk) :
    boundaryClosedSolution hC hν f hB x = boundarySolutionValue hC hν f hB x := by
  exact congrArg (fun a => a + ∫ y, kernel x y *
    (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
      (poissonL2 hν f.continuous.measurable hB)) y ∂ν) (boundaryClosedPoisson_interior f hx)

lemma boundaryClosedSolution_continuousOn (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    ContinuousOn (boundaryClosedSolution hC hν f hB) (closure disk) :=
  (boundaryClosedPoisson_continuousOn f hf).add
    (green_integral_continuousOn_closure hC hν _)

lemma boundaryClosedSolution_trace (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) (s : Boundary) :
    boundaryClosedSolution hC hν f hB s = f s := by
  have hs : (s:Plane) ∈ frontier disk := by
    simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0), mem_sphere, dist_zero_right] using s.property
  rw [boundaryClosedSolution,green_integral_boundary _ hs,add_zero,boundaryClosedPoisson_trace]

lemma boundaryClosedSolution_value_ae (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (H1.value (boundarySolution hC hν f hf) : Plane → ℝ) =ᵐ[volume.restrict disk]
      boundaryClosedSolution hC hν f hB := by
  filter_upwards [boundarySolution_value_ae hC hν f hf hB,
    ae_restrict_mem diskOpen.measurableSet] with x hx hxd
  exact hx.trans (boundaryClosedSolution_interior hC hν f hB hxd).symm

lemma boundaryClosedSolution_hasH1Gradient (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    HasH1Gradient disk (boundaryClosedSolution hC hν f hB)
      (H1.grad (boundarySolution hC hν f hf)) :=
  (H1.hasH1Gradient _).congr (boundaryClosedSolution_value_ae hC hν f hf hB)
    Filter.EventuallyEq.rfl


lemma boundaryClosedSolution_K (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundaryClosedSolution hC hν f hB x =
      ∫ s, fullBoundaryK hC hν x s*f s ∂boundaryMeasure := by
  rw [boundaryClosedSolution_interior hC hν f hB x.property]
  exact boundarySolution_K hC hν hT f hB x

end StrictHotSpots.PlaneGreen
end
end BoundaryClosedSolution

section PhysicalClosedSolution

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma inverse_map_chartMeasure : (volume.restrict Ω).map c.G = chartMeasure c.diskMap c.d := by
  have hm : (chartMeasure c.diskMap c.d).map c.diskMap = volume.restrict Ω :=
    map_chartMeasure c.diskMap c.d c.diskMap_deriv
  rw [← hm,
    AEMeasurable.map_map_of_aemeasurable c.inverse_lipschitz.continuous.aemeasurable
      (chart_aemeasurable c.diskMap c.d)]
  have he : c.G ∘ c.diskMap =ᵐ[chartMeasure c.diskMap c.d] id := by
    filter_upwards [ae_chart_source c.diskMap c.d] with x hx
    change c.G (c.diskMap x)=x
    rw [c.diskMap_agrees hx]
    exact c.left_inverse x (c.source_eq.symm ▸ subset_closure hx)
  rw [Measure.map_congr he,Measure.map_id]

lemma pull_ae_to_physical {f g : Plane → ℝ}
    (h : f ∘ c.diskMap =ᵐ[chartMeasure c.diskMap c.d] g) :
    f =ᵐ[volume.restrict Ω] (g ∘ c.G) := by
  have hg : f ∘ c.diskMap =ᵐ[(volume.restrict Ω).map c.G] g :=
    c.inverse_map_chartMeasure.symm ▸ h
  have ha := ae_of_ae_map c.inverse_lipschitz.continuous.aemeasurable hg
  filter_upwards [ha,ae_restrict_mem c.diskMap.open_target.measurableSet] with y hy hyΩ
  have hi : c.diskMap (c.G y)=y := by
    rw [← c.diskMap_inverse_agrees hyΩ]
    exact c.diskMap.right_inv hyΩ
  simpa only [Function.comp_apply,hi] using hy

lemma physicalSolution_pull_ae (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hμ : 0 ≤ firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    (H1.value (c.physicalSolution hb hs hμ hw hl) : Plane → ℝ) ∘ c.diskMap
      =ᵐ[chartMeasure c.diskMap c.d]
        H1.value (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
          (c.datumTrace w hw.continuousOn) hl) := by
  have h := affine_value_ae c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 (Ω:=Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw)
    (c.pullDatum_comp_H1 hb hs hw) (c.datumCorrection hb hs hμ hw hl)
  have he : (c.pullDatum_comp_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val =
      boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl :=
    (congrArg (fun V : H1 disk => V+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  exact (chartPull_ae c.diskMap c.d c.diskMap_deriv _).symm.trans
    (h.trans (EventuallyEq.of_eq (congrArg (fun V : H1 disk => (H1.value V : Plane → ℝ)) he)))

lemma physicalSolution_closed_ae (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hμ : 0 ≤ firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) {M : ℝ}
    (hM : ∀ s : Boundary, ‖w (c.F s)‖ ≤ M) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    (H1.value (c.physicalSolution hb hs hμ hw hl) : Plane → ℝ)
      =ᵐ[volume.restrict Ω]
      (boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hM) ∘ c.G := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  apply c.pull_ae_to_physical
  exact (c.physicalSolution_pull_ae hb hs hμ hw hl).trans
    ((chartMeasure_ac c.diskMap c.d).ae_le
      (boundaryClosedSolution_value_ae c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl hM))

end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalClosedSolution

section BoundaryClosedConvergence

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryClosedSolution_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (fn : ℕ → C(Boundary,ℝ)) (f : C(Boundary,ℝ)) {M B : ℝ}
    (hm : ∀ n s, ‖fn n s‖ ≤ M) (hb : ∀ s, ‖f s‖ ≤ B)
    (ht : ∀ s, Tendsto (fun n => fn n s) atTop (𝓝 (f s))) (p : disk) :
    Tendsto (fun n => boundaryClosedSolution hC hν (fn n) (hm n) p)
      atTop (𝓝 (boundaryClosedSolution hC hν f hb p)) := by
  obtain ⟨A,hA,hAb⟩ := fullBoundaryK_bounded hC hν p
  have hn (s : Boundary) : ‖fullBoundaryK hC hν p s‖ ≤ A := by
    rw [Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
    exact hAb s
  simp only [boundaryClosedSolution_K hC hν hT]
  apply tendsto_integral_of_dominated_convergence (fun _ : Boundary => A*M)
  · intro n
    exact ((fullBoundaryK_measurable hC hν p).mul (fn n).continuous.measurable).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun s => (norm_mul _ _).trans_le
      (mul_le_mul (hn s) (hm n s) (norm_nonneg _) hA)
  · exact Eventually.of_forall fun s => (ht s).const_mul _

end StrictHotSpots.PlaneGreen
end
end BoundaryClosedConvergence

section PhysicalMultiplierClosed

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma scalarSolution_closed_ae {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    {M : ℝ} (hM : ∀ s : Boundary, ‖w (c.F s)‖ ≤ M) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    (H1.value (c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw) : Plane → ℝ)
      =ᵐ[volume.restrict Ω]
      (boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le)
        (c.datumTrace w hw.continuousOn) hM) ∘ c.G :=
  c.physicalSolution_closed_ae hΩ.2.2.1 hΩ.2.2.2.2 hμ.le hw _ hM

lemma scalarSolution_mul_tendsto {w b : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0} (hb : LipschitzWith B b) :
    Tendsto (fun n => c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ
      ((ambientSmooth_smooth (planeApproxBump n) hb).contDiffOn.mul hw)) atTop
      (𝓝 (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
        (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1))) := by
  let U := (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1
  have ht := (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD).continuous.continuousAt.tendsto.comp
    (smoothMul_tendsto_lipschitzMul hΩ.2.1 hΩ.2.2.1 hb U)
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have hen := smoothMul_smooth_closure hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2
    (ambientSmooth_smooth (planeApproxBump n) hb)
    (continuous_closure_memLp_top hΩ.2.1 hΩ.2.2.1
      (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
    (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb)) hw
  exact ((c.scalarSolution_eq_extension hΩ hμ hl hD
    ((ambientSmooth_smooth (planeApproxBump n) hb).contDiffOn.mul hw)).trans
      (congrArg (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD) hen.symm)).symm

def multiplierTrace {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b)
    (w : Plane → ℝ) (hw : ContinuousOn w (closure Ω)) : C(Boundary,ℝ) where
  toFun s := b (c.F s)*w (c.F s)
  continuous_toFun := (c.physical_boundary_lipschitz hb).continuous.mul (c.datumTrace w hw).continuous

include hΩ in
lemma multiplierTrace_lipschitz {b w : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b)
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ A : ℝ≥0, LipschitzWith A (c.multiplierTrace hb w hw.continuousOn) := by
  obtain ⟨D,hD⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hw
  exact boundary_smul_lipschitz (c.physical_boundary_lipschitz hb) hD

lemma physical_lipschitzMul_closed_ae {w b : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0} (hb : LipschitzWith B b)
    {A : ℝ} (hA : ∀ s, ‖c.multiplierTrace hb w hw.continuousOn s‖ ≤ A) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    (H1.value (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
      (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1)) : Plane → ℝ)
      =ᵐ[volume.restrict Ω]
      (boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le)
        (c.multiplierTrace hb w hw.continuousOn) hA) ∘ c.G := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let hn (n : ℕ) := (ambientSmooth_smooth (planeApproxBump n) hb).contDiffOn.mul hw
  let fn (n : ℕ) := c.datumTrace _ (hn n).continuousOn
  obtain ⟨M,hM,hMb⟩ := c.smooth_physical_boundary_bound hΩ hb
  obtain ⟨W,hW,hWb⟩ := boundary_continuous_bound (c.datumTrace w hw.continuousOn).continuous
  have hMW (n : ℕ) (s : Boundary) : ‖fn n s‖ ≤ M*W := by
    change ‖ambientSmooth (planeApproxBump n) b (c.F s)*w (c.F s)‖ ≤ M*W
    rw [norm_mul]
    exact mul_le_mul (hMb n s) (hWb s) (norm_nonneg _) hM
  have ht (s : Boundary) : Tendsto (fun n => fn n s) atTop
      (𝓝 (c.multiplierTrace hb w hw.continuousOn s)) :=
    (ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb (c.F s)).mul_const _
  have he (n : ℕ) := c.scalarSolution_closed_ae hΩ hμ (hn n) (hMW n)
  have hv := H1.value.continuous.continuousAt.tendsto.comp
    (c.scalarSolution_mul_tendsto hΩ hμ hl hD hw hb)
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [hφae,ae_all_iff.mpr he,ae_restrict_mem hΩ.2.1.measurableSet] with x hx hxe hxΩ
  have hxD : c.G x ∈ disk := by
    rw [← c.diskMap_inverse_agrees hxΩ]
    exact c.diskMap.map_target hxΩ
  have hk := boundaryClosedSolution_tendsto c.densityBound_ne_top (c.density_bound hμ.le)
    (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ) fn (c.multiplierTrace hb w hw.continuousOn)
    hMW hA ht ⟨c.G x,hxD⟩
  apply tendsto_nhds_unique hx
  exact (hk.comp hφ.tendsto_atTop).congr' (Eventually.of_forall fun n => (hxe (φ n)).symm)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalMultiplierClosed


end OAI
