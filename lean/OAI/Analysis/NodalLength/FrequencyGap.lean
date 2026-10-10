import OAI.Analysis.NodalLength.Eigenfunctions

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Bundle
open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Bundle
open Set Filter Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory

namespace SharpNodal.Profiles
open Carleman InnerProductSpace
lemma poissonKernel_bounds {w z : ℂ} (hw : ‖w‖<1/2) (hz : ‖z‖=1) :
    1/4≤poissonKernel 0 w z ∧ poissonKernel 0 w z≤4 := by
  have ht:=norm_sub_le z w
  have hl:=norm_sub_norm_le z w
  rw [hz] at ht hl
  have hdn : 0<‖z-w‖:=by linarith
  have hsqlo : 1/4≤‖z-w‖^2:=by nlinarith
  have hsqhi : ‖z-w‖^2≤9/4:=by nlinarith [norm_nonneg w,norm_nonneg (z-w)]
  simp only [poissonKernel_def,sub_zero,hz,one_pow]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hdn)).mpr
    nlinarith [norm_nonneg w]
  · apply (div_le_iff₀ (sq_pos_of_pos hdn)).mpr
    nlinarith [sq_nonneg ‖w‖]

lemma harmonic_harnack {h : ℂ → ℝ} (hh : HarmonicOnNhd h (closedBall 0 1))
    (hn : ∀z∈sphere (0:ℂ) 1,0≤h z) {x y : ℂ}
    (hx : x∈ball 0 (1/2)) (hy : y∈ball 0 (1/2)) : h x≤16*h y := by
  have hcont:=hh.continuousOn.mono sphere_subset_closedBall
  have hcont' : ContinuousOn h (sphere 0 |(1:ℝ)|) := by simpa only [abs_one] using hcont
  have hi : CircleIntegrable h 0 1 := hcont'.circleIntegrable'
  have hker (w : ℂ) (hw:w∈ball 0 (1/2)) :
      CircleIntegrable (poissonKernel 0 w • h) 0 1 := by
    have hne (z : ℂ) (hz:z∈sphere 0 1) : z-w≠0 := by
      have hw':=mem_ball_zero_iff.mp hw
      have hz':=mem_sphere_zero_iff_norm.mp hz
      intro he
      have he':z=w:=sub_eq_zero.mp he
      rw [he'] at hz'; linarith
    apply ContinuousOn.circleIntegrable'
    simp only [abs_one]
    change ContinuousOn (poissonKernel 0 w * h) (sphere 0 1)
    apply ContinuousOn.mul _ hcont
    have hfun : poissonKernel 0 w = (fun z=>(‖z‖^2-‖w‖^2)/‖z-w‖^2) := by
      funext z; simp only [poissonKernel_def,sub_zero]
    rw [hfun]
    exact (continuous_norm.continuousOn.pow 2 |>.sub continuousOn_const).div
      ((continuous_id.sub continuous_const).norm.continuousOn.pow 2)
      (fun z hz=>pow_ne_zero _ (norm_ne_zero_iff.mpr (hne z hz)))
  have hb (w : ℂ) (hw:w∈ball 0 (1/2)) :
      (1/4)*h 0≤h w ∧ h w≤4*h 0 := by
    have hf : Real.circleAverage (poissonKernel 0 w * h) 0 1 = h w := by
      simpa only [smul_eq_mul] using hh.circleAverage_poissonKernel_smul (ball_subset_ball (by norm_num : (1/2:ℝ)≤1) hw)
    have hhabs : HarmonicOnNhd h (closedBall 0 |(1:ℝ)|) := by simpa only [abs_one] using hh
    have hm : Real.circleAverage h 0 1=h 0:=hhabs.circleAverage_eq
    constructor
    · have hi' : CircleIntegrable ((1/4:ℝ) • h) 0 1:=hi.smul (1/4)
      have he:=Real.circleAverage_mono hi' (hker w hw) (fun z hz=>by
        have hz' : ‖z‖=1:=by simpa using mem_sphere.mp hz
        exact mul_le_mul_of_nonneg_right (poissonKernel_bounds (mem_ball_zero_iff.mp hw) hz').1 (hn z (by simpa using hz)))
      simpa only [Real.circleAverage_smul,smul_eq_mul,hm,hf] using he
    · have hi' : CircleIntegrable ((4:ℝ) • h) 0 1:=hi.smul 4
      have he:=Real.circleAverage_mono (hker w hw) hi' (fun z hz=>by
        have hz' : ‖z‖=1:=by simpa using mem_sphere.mp hz
        exact mul_le_mul_of_nonneg_right (poissonKernel_bounds (mem_ball_zero_iff.mp hw) hz').2 (hn z (by simpa using hz)))
      simpa only [Real.circleAverage_smul,smul_eq_mul,hm,hf] using he
  have hxx:=(hb x hx).2
  have hyy:=(hb y hy).1
  linarith

lemma plane_harmonic_harnack {h : Plane → ℝ} (hh : Smooth h)
    (he : ∀z∈ball (0:Plane) 2,euclideanLaplacian h z=0)
    (hn : ∀z∈ball (0:Plane) 2,0≤h z) {x y : Plane}
    (hx:x∈ball 0 (1/2)) (hy:y∈ball 0 (1/2)) : h x≤16*h y := by
  let H:=h ∘ planeComplex.symm
  have hs : ContDiff ℝ ∞ H:=hh.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hh' : HarmonicOnNhd H (closedBall 0 1) := by
    intro z hz
    refine ⟨hs.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤)),?_⟩
    have hz' : z∈ball (0:ℂ) 2:=closedBall_subset_ball (by norm_num) hz
    filter_upwards [isOpen_ball.mem_nhds hz'] with w hw
    rw [laplacian_comp_isometry planeComplex.symm hh,←plane_laplacian_eq_mathlib hh]
    exact he _ (by simpa only [mem_ball,dist_zero_right,planeComplex.symm.norm_map] using hw)
  have hpc (z : Plane) (hz:z∈ball 0 (1/2)) : planeComplex z∈ball (0:ℂ) (1/2) := by
    simpa only [mem_ball,dist_zero_right,planeComplex.norm_map] using hz
  simpa only [H,Function.comp_apply,planeComplex.symm_apply_apply] using
    harmonic_harnack hh' (fun z hz=>hn _ (by
      have hz':=sphere_subset_ball (by norm_num : (1:ℝ)<2) hz
      simpa only [mem_ball,dist_zero_right,planeComplex.symm.norm_map] using hz')) (hpc x hx) (hpc y hy)
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman
lemma laplacian_sub {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun z=>f z-g z) x=euclideanLaplacian f x-euclideanLaplacian g x := by
  have he : (fun z=>f z-g z)=(fun z=>f z+(-1)*g z) := by funext z; ring
  rw [he,laplacian_add hf (contDiff_const.mul hg),laplacian_const_mul hg]
  ring

lemma additive_harnack_unit : ∃D : ℝ,0<D ∧ ∀(U q : Plane → ℝ),
    ContDiffOn ℝ ∞ U (ball 0 3) → ContDiffOn ℝ ∞ q (ball 0 3) →
    (∀z∈ball (0:Plane) 3,euclideanLaplacian U z+q z*U z=0) →
    (∀z∈ball (0:Plane) 3,|U z|≤1) → ∀Q : ℝ,0≤Q →
    (∀z∈ball (0:Plane) 3,|q z|≤Q) →
    ∀x∈ball (0:Plane) (1/2),∀y∈ball (0:Plane) (1/2),
      1-U x≤16*(1-U y)+D*Q := by
  obtain ⟨C,hC,hCb⟩:=newton_operator_bounds
  refine ⟨34*C,by linarith,?_⟩
  intro U q hU hq he hUb Q hQ hqb x hx y hy
  obtain ⟨V,hV,-,hVe,-,-⟩:=bump_smoothOn_extension hU
  obtain ⟨P,hP,-,hPe,-,-⟩:=bump_smoothOn_extension hq
  let χ : ContDiffBump (0:Plane):=⟨9/4,5/2,by norm_num,by norm_num⟩
  let f : Plane → ℝ:=fun z=>χ z*(P z*V z)
  have hf : Smooth f:=χ.contDiff.mul (hP.mul hV)
  have hcf : HasCompactSupport f:=χ.hasCompactSupport.mul_right
  have hfs : ∀z,3≤‖z‖ → f z=0 := by
    intro z hz
    have hz':χ z=0:=χ.zero_of_le_dist (by dsimp [χ]; simpa only [dist_zero_right] using (show (5/2:ℝ)≤‖z‖ by linarith))
    simp [f,hz']
  have hfb : ∀z∈ball (0:Plane) 3,|f z|≤Q := by
    intro z hz
    by_cases hz' : z∈ball (0:Plane) (5/2)
    · have hz'' : z∈ball (0:Plane) (11/4):=ball_subset_ball (by norm_num) hz'
      have hvz:=hVe z hz''
      have hpz:=hPe z hz''
      have hh:=mul_le_mul (hqb z hz) (hUb z hz) (abs_nonneg _) hQ
      dsimp [f]
      rw [hpz.self_of_nhds,hvz.self_of_nhds,abs_mul,abs_mul,abs_of_nonneg χ.nonneg]
      calc
        _ ≤ 1*(|q z| * |U z|):=mul_le_mul_of_nonneg_right χ.le_one (by positivity)
        _ ≤ Q:=by simpa using hh
    · have hz0 : χ z=0:=χ.zero_of_le_dist (by simpa only [χ,mem_ball,dist_zero_right,not_lt] using hz')
      simpa [f,hz0] using hQ
  have hnb:=hCb f hf hcf Q hQ hfs hfb
  let N:=newtonPotential f
  have hN : Smooth N:=smooth_newtonPotential hf hcf
  let H : Plane → ℝ:=fun z=>1-(V z+N z)+C*Q
  have hH : Smooth H:=(contDiff_const.sub (hV.add hN)).add contDiff_const
  have hHE : ∀z∈ball (0:Plane) 2,euclideanLaplacian H z=0 := by
    intro z hz
    have hz11 : z∈ball (0:Plane) (11/4):=ball_subset_ball (by norm_num) hz
    have hz3 : z∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hz
    have hVE:=laplacian_germ (hVe z hz11)
    have hfz : f z=q z*U z:=by
      have hχ : χ z=1:=χ.one_of_mem_closedBall (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))
      simp only [f,hχ,one_mul,(hPe z hz11).self_of_nhds,(hVe z hz11).self_of_nhds]
    rw [laplacian_add (contDiff_const.sub (hV.add hN)) contDiff_const,
      laplacian_const,add_zero,laplacian_sub contDiff_const (hV.add hN),laplacian_const,
      laplacian_add hV hN,laplacian_newtonPotential hf hcf,hVE,hfz]
    rw [he z hz3,sub_zero]
  have hHn : ∀z∈ball (0:Plane) 2,0≤H z := by
    intro z hz
    have hz3 : z∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hz
    have hz11 : z∈ball (0:Plane) (11/4):=ball_subset_ball (by norm_num) hz
    have hvz:=(hUb z hz3)
    have hnz:=(hnb z hz3).1
    have hvEq:=(hVe z hz11).self_of_nhds
    dsimp [H,N]; rw [hvEq]; linarith [le_abs_self (U z),le_abs_self (newtonPotential f z)]
  have hh:=plane_harmonic_harnack hH hHE hHn hx hy
  have hx3 : x∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hx
  have hy3 : y∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hy
  have hnx:=(hnb x hx3).1
  have hny:=(hnb y hy3).1
  have hvx:=(hVe x (ball_subset_ball (by norm_num) hx)).self_of_nhds
  have hvy:=(hVe y (ball_subset_ball (by norm_num) hy)).self_of_nhds
  dsimp [H,N] at hh
  rw [hvx,hvy] at hh
  have hnxl:=(abs_le.mp hnx).1
  have hnxu:=(abs_le.mp hnx).2
  have hnyl:=(abs_le.mp hny).1
  have hnyu:=(abs_le.mp hny).2
  nlinarith [show 0≤C*Q by positivity]
end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Set Filter Metric
namespace SharpNodal.Geometry
lemma no_low_energy_sequence {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    {v : ℕ → X → ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀j x,0≤v j x) (hmin : ∀j,∃x,v j x=0) (hmax : ∀j,∃x,1≤v j x)
    (hlocal : ∀x:X,∃G : Set X,IsOpen G ∧ x∈G ∧ ∃D : ℝ,0≤D ∧
      ∀j,∀y∈G,∀z∈G,v j y≤16*v j z+D*ε j) : False := by
  choose x hx using hmin
  obtain ⟨a,-,φ,hφ,hconv⟩:=isCompact_univ.tendsto_subseq (fun j=>mem_univ (x j))
  let S : Set X:={y | Tendsto (fun j=>v (φ j) y) atTop (𝓝 0)}
  have heps : Tendsto (fun j=>ε (φ j)) atTop (𝓝 0):=hε.comp hφ.tendsto_atTop
  have hprop {G : Set X} {D : ℝ}
      (hb : ∀j,∀y∈G,∀z∈G,v j y≤16*v j z+D*ε j)
      {y z : X} (hy:y∈G) (hz:z∈G) (hs:z∈S) : y∈S := by
    have ht : Tendsto (fun j=>16*v (φ j) z+D*ε (φ j)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hs).add (tendsto_const_nhds.mul heps)
    exact squeeze_zero (fun j=>hv (φ j) y) (fun j=>hb (φ j) y hy z hz) ht
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨G,hG,hyG,D,-,hb⟩:=hlocal y
    exact Filter.mem_of_superset (hG.mem_nhds hyG) (fun z hz=>hprop hb hz hyG hy)
  have hScopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨G,hG,hyG,D,-,hb⟩:=hlocal y
    apply Filter.mem_of_superset (hG.mem_nhds hyG)
    intro z hz hzs
    exact hy (hprop hb hyG hz hzs)
  have ha : a∈S := by
    obtain ⟨G,hG,haG,D,-,hb⟩:=hlocal a
    have hGevent:=hconv.eventually (hG.mem_nhds haG)
    have hupper : ∀ᶠj in atTop,v (φ j) a≤D*ε (φ j) := by
      filter_upwards [hGevent] with j hj
      have hh:=hb (φ j) a haG (x (φ j)) hj
      simpa only [hx,mul_zero,zero_add] using hh
    apply squeeze_zero' (Eventually.of_forall fun j=>hv (φ j) a) hupper
    simpa using tendsto_const_nhds.mul heps
  have hSuniv : S=univ:=(show IsClopen S from ⟨by simpa only [compl_compl] using hScopen.isClosed_compl,hSopen⟩).eq_univ ⟨a,ha⟩
  choose z hz using hmax
  obtain ⟨b,-,ψ,hψ,hzconv⟩:=isCompact_univ.tendsto_subseq (fun j=>mem_univ (z (φ j)))
  obtain ⟨G,hG,hbG,D,-,hb⟩:=hlocal b
  have hbevent:=hzconv.eventually (hG.mem_nhds hbG)
  have hbS : b∈S:=by rw [hSuniv]; exact mem_univ b
  have hb0 : Tendsto (fun j=>v (φ (ψ j)) b) atTop (𝓝 0):=hbS.comp hψ.tendsto_atTop
  have ht : Tendsto (fun j=>16*v (φ (ψ j)) b+D*ε (φ (ψ j))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hb0).add (tendsto_const_nhds.mul (heps.comp hψ.tendsto_atTop))
  have hone : ∀ᶠj in atTop,(1:ℝ)≤16*v (φ (ψ j)) b+D*ε (φ (ψ j)) := by
    filter_upwards [hbevent] with j hj
    exact (hz (φ (ψ j))).trans (hb (φ (ψ j)) _ hj b hbG)
  have := ge_of_tendsto ht hone
  norm_num at this
end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
lemma exists_additive_harnack (x : M) :
    ∃G : Set M,IsOpen G ∧ x ∈ G ∧ ∃D : ℝ,0 ≤ D ∧
      ∀K : ℝ,∀u : M → ℝ,NormalizedEigen K u →
      ∀y ∈ G,∀z ∈ G,1-u y ≤ 16*(1-u z)+D*K^2 := by
  obtain ⟨e,hxe,he⟩:=exists_isothermal_chart x
  have hy:=e.map_source hxe
  obtain ⟨r,Cp,hr,hCp,hclose,-,hpbound,-⟩:=he.exists_profile_ball hy
  obtain ⟨B,hB,hBb⟩:=additive_harnack_unit
  let s:=r/4
  have hs : 0 < s:=by dsimp [s]; positivity
  let F:=rescaleMap (e x) s
  have hFmap : MapsTo F (ball 0 3) (ball (e x) r) := by
    intro z hz
    change dist (e x+s • z) (e x) < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    have hz':=mem_ball_zero_iff.mp hz
    dsimp [s]; nlinarith
  have hFe : MapsTo F (ball 0 3) e.target:=fun z hz=>hclose (ball_subset_closedBall (hFmap hz))
  let G:=e.source∩e ⁻¹' ball (e x) (s/2)
  have hs2 : 0 < s/2:=by positivity
  refine ⟨G,e.isOpen_inter_preimage isOpen_ball,⟨hxe,mem_ball_self hs2⟩,B*s^2*Cp,by positivity,?_⟩
  intro K u hu y hyG z hzG
  let U:=u∘e.symm
  let V:=U∘F
  let q:=fun w=>s^2*K^2*conformalFactor e (F w)
  obtain ⟨hU,hUE⟩:=he.eigenfunction hu.smooth hu.equation
  have hV : ContDiffOn ℝ ∞ V (ball 0 3):=hU.comp (smooth_rescaleMap (e x) s).contDiffOn hFe
  have hq : ContDiffOn ℝ ∞ q (ball 0 3):=contDiffOn_const.mul (he.factor_smooth.comp (smooth_rescaleMap (e x) s).contDiffOn hFe)
  have hVE : ∀w ∈ ball (0:Plane) 3,euclideanLaplacian V w+q w*V w=0 := by
    intro w hw
    rw [laplacian_rescale_local e.open_target hU (e x) s w (hFe hw)]
    have hh:=hUE _ (hFe hw)
    dsimp [V,U,q,F] at *; nlinarith only [hh]
  have hVb : ∀w ∈ ball (0:Plane) 3,|V w| ≤ 1:=fun w _=>hu.bound _
  have hqb : ∀w ∈ ball (0:Plane) 3,|q w| ≤ s^2*K^2*Cp := by
    intro w hw
    dsimp [q]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ s^2*K^2)]
    exact mul_le_mul_of_nonneg_left (hpbound _ (hFmap hw)) (by positivity)
  let Y:=s⁻¹ • (e y-e x)
  let Z:=s⁻¹ • (e z-e x)
  have hpoint {a : M} (ha:a ∈ G) : s⁻¹ • (e a-e x) ∈ ball (0:Plane) (1/2) := by
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    have hh:=ha.2
    rw [mem_preimage,mem_ball,dist_eq_norm] at hh
    exact (inv_mul_lt_iff₀ hs).mpr (by nlinarith)
  have hvalue {a : M} (ha : a ∈ G) : V (s⁻¹ • (e a-e x))=u a := by
    dsimp [V,U,F,rescaleMap]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul,add_sub_cancel,e.left_inv ha.1]
  have hh:=hBb V q hV hq hVE hVb _ (by positivity : 0 ≤ s^2*K^2*Cp) hqb Y (hpoint hyG) Z (hpoint hzG)
  rw [show V Y=u y from hvalue hyG,show V Z=u z from hvalue hzG] at hh
  nlinarith only [hh]

lemma normalized_frequency_gap [CompactSpace M] [ConnectedSpace M] :
    ∃k₀ : ℝ,0 < k₀ ∧ ∀K : ℝ,0 < K → ∀u : M → ℝ,NormalizedEigen K u → k₀ ≤ K := by
  by_contra hn
  push Not at hn
  have hf (j : ℕ):=hn ((j+1:ℝ)⁻¹) (by positivity)
  choose K hK u hu hKsmall using hf
  have hkt : Tendsto K atTop (𝓝 0) := by
    apply squeeze_zero (fun j=>(hK j).le) (fun j=>(hKsmall j).le)
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun _=>le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop)
  have hchoose (j : ℕ) : ∃v : M → ℝ,NormalizedEigen (K j) v ∧ (∃x,v x=1) ∧ ∃x,v x ≤ 0 := by
    obtain ⟨x,hx⟩:=(hu j).maximum
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with hx|hx
    · exact ⟨u j,hu j,⟨x,hx⟩,(hu j).exists_nonpos (hK j)⟩
    · refine ⟨fun y=> -u j y,(hu j).neg,⟨x,by linarith⟩,(hu j).neg.exists_nonpos (hK j)⟩
  choose v hv hvmax hvmin using hchoose
  apply no_low_energy_sequence (v:=fun j x=>1-v j x) (ε:=fun j=>(K j)^2)
  · simpa only [zero_pow (by decide : (2:ℕ)≠0)] using hkt.pow 2
  · intro j x; linarith [(le_abs_self (v j x)).trans ((hv j).bound x)]
  · intro j; obtain ⟨x,hx⟩:=hvmax j; exact ⟨x,by linarith⟩
  · intro j; obtain ⟨x,hx⟩:=hvmin j; exact ⟨x,by linarith⟩
  · intro x
    obtain ⟨G,hG,hx,D,hD,hDb⟩:=exists_additive_harnack x
    exact ⟨G,hG,hx,D,hD,fun j=>hDb (K j) (v j) (hv j)⟩
end SharpNodal.Geometry

end
end
end
end

end OAI
