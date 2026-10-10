import OAI.Analysis.NodalLength.GradientAnchors

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

namespace SharpNodal.Profiles
open Carleman
lemma smooth_C1_bounded_ball {U : Plane → ℝ} (hU : Smooth U) (R : ℝ) :
    ∃K : ℝ,0≤K ∧ ∀x∈ball (0:Plane) R,|U x|≤K ∧ ∀i,|coordPartial U i x|≤K := by
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:Plane) R).exists_bound_of_continuousOn hU.continuous.continuousOn
  choose D hD using fun i : Fin 2 =>(isCompact_closedBall (0:Plane) R).exists_bound_of_continuousOn
    (smooth_partial hU i).continuous.continuousOn
  let K:=max 0 B+∑i : Fin 2,max 0 (D i)
  have hs : 0≤∑i : Fin 2,max 0 (D i):=Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  refine ⟨K,add_nonneg (le_max_left _ _) hs,?_⟩
  intro x hx
  have hm:=ball_subset_closedBall hx
  constructor
  · exact (hB x hm).trans (by dsimp [K]; simpa only [Real.norm_eq_abs] using (le_max_right (0:ℝ) B).trans (le_add_of_nonneg_right hs))
  · intro i
    apply (hD i x hm).trans
    apply (le_max_right (0:ℝ) (D i)).trans
    exact (Finset.single_le_sum (fun j _=>le_max_left (0:ℝ) (D j)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left (le_max_left _ _))

lemma recenter_inner_maps {p : Plane} (hp : p∈ball (0:Plane) (1/4)) {x : Plane}
    (hx : x∈closedBall (0:Plane) 1) : rescaleMap p (3/4) x∈ball (0:Plane) 1 := by
  apply mem_ball_zero_iff.mpr
  have hp':=mem_ball_zero_iff.mp hp
  have hx':=mem_closedBall_zero_iff.mp hx
  have ht:=norm_add_le p ((3/4:ℝ) • x)
  rw [norm_smul] at ht
  norm_num at ht
  dsimp [rescaleMap]; linarith

lemma planeToComplex_rescale (p x : Plane) (r : ℝ) :
    planeToComplex (rescaleMap p r x)=planeToComplex p+(r:ℂ)*planeToComplex x := by
  simp only [rescaleMap,map_add,map_smul,Complex.real_smul]

theorem normalized_small_potential_length : ∃L : ℝ,0<L ∧
    ∀{C ε δ : ℝ} {q : Plane → ℝ},SmallPotential C ε δ q →
    Real.exp (8*C*(4*δ/(1-δ)))-1≤1/2048 →
    ∀{U : Plane → ℝ},Smooth U →
    (∀x∈ball (0:Plane) (5/2),euclideanLaplacian U x+q x*U x=0) →
    ∀S : ℝ,1≤S → (∀x∈ball (0:Plane) (5/2),|U x|≤S) →
    (∃y∈ball (0:Plane) (1/4),1≤|U y|) →
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ U x=0}≤
      ENNReal.ofReal (L*(1+Real.log S)) := by
  obtain ⟨A,hA,hAb⟩:=small_potential_gradient_bound
  let L₀:=65536*4*Real.pi*(2001+21/Real.log (4/3))
  have hL₀ : 0<L₀:=by dsimp [L₀]; have:=Real.log_pos (by norm_num : (1:ℝ)<4/3); positivity
  have hAP : 0<A:=by linarith
  have hlogA : 0≤Real.log (128*A):=Real.log_nonneg (by linarith)
  refine ⟨L₀*(1+Real.log (128*A)),mul_pos hL₀ (by linarith),?_⟩
  intro C ε δ q h hη U hU hUE S hS hUb hanchor
  have hSp : 0<S:=by linarith
  have hlogS : 0≤Real.log S:=Real.log_nonneg hS
  by_cases hz : ∃z∈ball (0:Plane) (1/60),U z=0
  swap
  · have he : {x | x∈ball (0:Plane) (1/60) ∧ U x=0}=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx; exact hz ⟨x,hx.1,hx.2⟩
    rw [he,measure_empty]; exact bot_le
  obtain ⟨z,hz,hUz⟩:=hz
  obtain ⟨y,hy,hUy⟩:=hanchor
  let v : Plane → ℝ:=fun x=>U x/multiplierLimit q x
  have hv : ∀x∈ball (0:Plane) 3,DifferentiableAt ℝ v x := fun x hx=>h.quotient_differentiable hU hx
  have hvz : v z=0:=by simp [v,hUz]
  have hvy : 1/2≤|v y| := by
    have hy3 : y∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hy
    have hlow:=h.limit_lower hy3
    have hupp:=h.limit_upper hy3
    dsimp [v]; rw [abs_div,abs_of_pos (by linarith : 0 < multiplierLimit q y)]
    apply (le_div_iff₀ (by linarith : 0 < multiplierLimit q y)).mpr
    linarith
  obtain ⟨p,hp,hpgrad⟩:=gradient_anchor (fun x hx=>hv x (ball_subset_ball (by norm_num) hx))
    hy (ball_subset_ball (by norm_num) hz) hvz hvy
  obtain ⟨K,hK,hKb⟩:=smooth_C1_bounded_ball hU 3
  obtain ⟨H,hH,hHclose⟩:=h.holomorphic_gradient hU hUE hK hKb
  have hc (x : Plane) (hx : x∈ball (0:Plane) 1) :
      ‖H (planeToComplex x)-complexGradient v x‖≤‖complexGradient v x‖/2048 := by
    exact (hHclose x (ball_subset_closedBall hx)).trans (by dsimp [v]; nlinarith [norm_nonneg (complexGradient v x)])
  have hnorms (x : Plane) (hx : x∈ball (0:Plane) 1) :
      ‖complexGradient v x‖≤2*‖H (planeToComplex x)‖ ∧
      ‖H (planeToComplex x)‖≤2*‖complexGradient v x‖ := by
    have hd:=hc x hx
    have h1:=norm_sub_norm_le (H (planeToComplex x)) (complexGradient v x)
    have h2:=norm_sub_norm_le (complexGradient v x) (H (planeToComplex x))
    rw [norm_sub_rev (complexGradient v x)] at h2
    constructor <;> linarith [norm_nonneg (complexGradient v x)]
  have hvgrad (x : Plane) (hx : x∈ball (0:Plane) 1) : ‖complexGradient v x‖≤12*(A*S) := by
    have hx3 : x∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hx
    have hAS : 0≤A*S:=mul_nonneg hAP.le hSp.le
    have hpbound (i : Fin 2) : |coordPartial v i x|≤6*(A*S) := by
      have hu : |U x|≤A*S := (hUb x (ball_subset_ball (by norm_num) hx)).trans (by nlinarith)
      have ht:=quotient_partial_bound hAS (by norm_num : (0:ℝ)≤1)
        (hU.differentiable (by simp) |>.differentiableAt) (h.limit_differentiable hx3)
        (h.limit_lower hx3) hu (hAb h hU hUE S hSp.le hUb x hx) (h.limit_partial_bound hx3) i
      dsimp [v]; linarith only [ht]
    exact (norm_gradient_le v x).trans (by have:=hpbound 0; have:=hpbound 1; linarith)
  have hbH (x : Plane) (hx : x∈ball (0:Plane) 1) : ‖H (planeToComplex x)‖≤24*A*S := by
    have:= (hnorms x hx).2
    have:=hvgrad x hx
    linarith
  let T : ℂ → ℂ:=fun w=>planeToComplex p+(3/4:ℂ)*w
  let G : ℂ → ℂ:=fun w=>(3/4:ℂ)*H (T w)
  let w : Plane → ℝ:=v∘rescaleMap p (3/4)
  have hT (a : ℂ) (ha : a∈ball (0:ℂ) 1) : T a∈ball (0:ℂ) 1 := by
    apply mem_ball_zero_iff.mpr
    have hn:=norm_add_le (planeToComplex p) ((3/4:ℂ)*a)
    rw [LinearIsometryEquiv.norm_map,norm_mul] at hn
    norm_num at hn
    have hp':=mem_ball_zero_iff.mp hp
    have ha':=mem_ball_zero_iff.mp ha
    dsimp [T]; linarith
  have hG : DifferentiableOn ℂ G (ball 0 1) := by
    intro a ha
    have hd' : DifferentiableAt ℂ H (T a):=hH.differentiableAt (isOpen_ball.mem_nhds (hT a ha))
    exact ((hd'.comp a (by dsimp [T]; fun_prop)).const_mul (3/4:ℂ)).differentiableWithinAt
  have hp1 : p∈ball (0:Plane) 1:=ball_subset_ball (by norm_num) hp
  have hGp : 3/16≤‖G 0‖ := by
    have he:=(hnorms p hp1).1
    dsimp [G,T]
    rw [mul_zero,add_zero,norm_mul]
    norm_num
    linarith
  have hG0 : G 0≠0:=norm_pos_iff.mp (by linarith : 0<‖G 0‖)
  have hbG : ∀a∈closedBall (0:ℂ) (2/3),‖G a‖≤24*A*S := by
    intro a ha
    have hTa:=hT a (closedBall_subset_ball (by norm_num) ha)
    have ht:=hbH (complexToPlane (T a)) (by
      apply mem_ball_zero_iff.mpr
      simpa only [LinearIsometryEquiv.norm_map] using mem_ball_zero_iff.mp hTa)
    rw [planeToComplex,LinearIsometryEquiv.symm_apply_apply] at ht
    dsimp [G]
    rw [norm_mul]; norm_num
    nlinarith [norm_nonneg (H (T a))]
  have hw : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ w x := by
    intro x hx
    have ht:=recenter_inner_maps hp (ball_subset_closedBall hx)
    exact (hv _ (ball_subset_ball (by norm_num) ht)).comp x ((smooth_rescaleMap p (3/4)).differentiable (by simp) |>.differentiableAt)
  have hwc : ∀x∈ball (0:Plane) 1,‖complexGradient w x-G (planeToComplex x)‖≤‖G (planeToComplex x)‖/1024 := by
    intro x hx
    have ht:=recenter_inner_maps hp (ball_subset_closedBall hx)
    have hdiff:=gradient_rescale_differentiable (r:=3/4) (hv _ (ball_subset_ball (by norm_num) ht))
    have he : T (planeToComplex x)=planeToComplex (rescaleMap p (3/4) x):=by
      dsimp [T]
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using (planeToComplex_rescale p x (3/4)).symm
    change ‖complexGradient (v∘rescaleMap p (3/4)) x-(3/4:ℂ)*H (T (planeToComplex x))‖≤_
    rw [hdiff,he,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_ofNat,←mul_sub,norm_mul]
    change _≤‖(3/4:ℂ)*H (T (planeToComplex x))‖/1024
    rw [he,norm_mul]
    norm_num
    have hclose:=hc _ ht
    rw [norm_sub_rev] at hclose
    have hnorm:=(hnorms _ ht).1
    linarith
  have hM : 1≤24*A*S:=by nlinarith
  have hlen:=nodal_length_holomorphic_comparison_wide hM hG hG0 hbG hw hwc
  have hlen':=small_nodal_length_of_translated (v:=v) hp
  have he : {x | x∈ball (0:Plane) (1/60) ∧ U x=0}={x | x∈ball (0:Plane) (1/60) ∧ v x=0} := by
    ext x
    by_cases hx : x∈ball (0:Plane) (1/60)
    · have hne : multiplierLimit q x≠0:=by have:=h.limit_lower (ball_subset_ball (by norm_num : (1/60:ℝ)≤3) hx); linarith
      simp only [Set.mem_ofPred_eq, hx, true_and, v, div_eq_zero_iff, hne, or_false]
    · simp only [Set.mem_ofPred_eq,hx,false_and]
  rw [he]
  apply (hlen'.trans hlen).trans
  apply ENNReal.ofReal_le_ofReal
  have hlg : Real.log ((24*A*S)/‖G 0‖)≤Real.log (128*A)+Real.log S := by
    rw [←Real.log_mul (by positivity : 128*A≠0) hSp.ne']
    apply Real.log_le_log (div_pos (by positivity) (norm_pos_iff.mpr hG0))
    apply (div_le_iff₀ (norm_pos_iff.mpr hG0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hGp (by positivity : 0≤128*A*S)]
  change L₀*(1+Real.log ((24*A*S)/‖G 0‖))≤_
  have hle:=mul_le_mul_of_nonneg_left hlg hL₀.le
  nlinarith [mul_nonneg hlogA hlogS,mul_nonneg hL₀.le (mul_nonneg hlogA hlogS)]
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma log_sq_le_inv {r : ℝ} (hr : 0≤r) (hr1 : r≤1) : (Real.log r)^2≤4*r⁻¹ := by
  rcases eq_or_lt_of_le hr with he | hp
  · rw [←he]; simp
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (inv_pos.mpr hp))
  rw [Real.log_sqrt (inv_nonneg.mpr hr),Real.log_inv] at h
  have hl := Real.log_nonpos hr hr1
  have hs := Real.sq_sqrt (inv_nonneg.mpr hr)
  have hb : -Real.log r ≤ 2*Real.sqrt r⁻¹ := by linarith
  have hc := mul_self_le_mul_self (by linarith : 0≤-Real.log r) hb
  nlinarith

lemma integrable_logParametrix_sq : Integrable (fun x=>logParametrix x^2) := by
  have hi : IntegrableOn (fun x : Plane=> (Real.log ‖x‖)^2) (ball 0 (1/4)) := by
    apply ((inv_norm_integrableOn_ball (1/4)).const_mul 4).mono'
      ((measurable_id.norm.log.pow_const 2).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    change |(Real.log ‖x‖)^2|≤_
    rw [abs_of_nonneg (sq_nonneg (Real.log ‖x‖))]
    exact log_sq_le_inv (norm_nonneg _) (by have:=mem_ball_zero_iff.mp hx; linarith)
  have hQ : IntegrableOn (fun x=>logParametrix x^2) (ball 0 (1/4)) := by
    apply hi.mono' ((parametrixCutoff.continuous.measurable.mul measurable_id.norm.log).pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    change |(parametrixCutoff x*Real.log ‖x‖)^2|≤_
    rw [abs_of_nonneg (sq_nonneg (parametrixCutoff x*Real.log ‖x‖)),mul_pow]
    have hc : parametrixCutoff x^2≤1 := by
      have hl:=parametrixCutoff.nonneg (x:=x)
      have hu:=parametrixCutoff.le_one (x:=x)
      nlinarith
    exact mul_le_of_le_one_left (sq_nonneg _) hc
  have he : (fun x=>logParametrix x^2)=(ball (0:Plane) (1/4)).indicator (fun x=>logParametrix x^2) := by
    funext x
    by_cases hx : x∈ball (0:Plane) (1/4)
    · simp only [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,logParametrix_zero (by simpa only [mem_ball,dist_zero_right,not_lt] using hx)]
      norm_num
  rw [he]
  exact hQ.integrable_indicator measurableSet_ball

lemma integral_abs_mul_le_sqrt {f g : Plane → ℝ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    |∫x,f x*g x|≤Real.sqrt (∫x,f x^2)*Real.sqrt (∫x,g x^2) := by
  have hh:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by norm_num; exact hf) (by norm_num; exact hg)
  simp only [Real.norm_eq_abs,Real.rpow_two, sq_abs,←Real.sqrt_eq_rpow] at hh
  exact (norm_integral_le_integral_norm (fun x=>f x*g x)).trans (by simpa only [Real.norm_eq_abs,abs_mul] using hh)

lemma continuous_sq_integrableOn_ball {U : Plane → ℝ} (hU : Continuous U) (R : ℝ) :
    IntegrableOn (fun x=>U x^2) (ball 0 R) :=
  (hU.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0:Plane) R) |>.mono_set ball_subset_closedBall

lemma memLp_indicator_ball {U : Plane → ℝ} (hU : Continuous U) (R : ℝ) :
    MemLp ((ball (0:Plane) R).indicator U) 2 := by
  apply (memLp_two_iff_integrable_sq (hU.measurable.indicator measurableSet_ball |>.aestronglyMeasurable)).mpr
  have he : (fun x=>((ball (0:Plane) R).indicator U x)^2)=(ball (0:Plane) R).indicator (fun x=>U x^2) := by
    funext x; by_cases hx : x∈ball (0:Plane) R <;> simp [hx]
  rw [he]
  exact (continuous_sq_integrableOn_ball hU R).integrable_indicator measurableSet_ball

lemma kernel_L2_bound {f U : Plane → ℝ} (hf : MemLp f 2) (hU : Continuous U)
    {x : Plane} {R r : ℝ} (hx : ‖x‖+r<R) (hs : ∀y,r<‖y‖ → f y=0) :
    |rconv f U x|≤Real.sqrt (∫y,f y^2)*Real.sqrt (∫y in ball (0:Plane) R,U y^2) := by
  let V:=(ball (0:Plane) R).indicator U
  have hV:=memLp_indicator_ball hU R
  have ht : MemLp (fun y=>V (x-y)) 2 := hV.comp_measurePreserving ((volume : Measure Plane).measurePreserving_sub_left x)
  have he : rconv f U x=∫y,f y*V (x-y) := by
    rw [rconv_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : r<‖y‖
    · rw [hs y hy]; simp
    · have hm : x-y∈ball (0:Plane) R:=mem_ball_zero_iff.mpr ((norm_sub_le x y).trans_lt (by linarith only [hx,le_of_not_gt hy]))
      simp only [V,indicator_of_mem hm]
  rw [he]
  have hh:=integral_abs_mul_le_sqrt hf ht
  have heI : (∫y,V (x-y)^2)=∫y in ball (0:Plane) R,U y^2 := by
    rw [integral_sub_left_eq_self (fun y=>V y^2) volume x]
    have heV : (fun y=>V y^2)=(ball (0:Plane) R).indicator (fun y=>U y^2) := by
      funext y; by_cases hy : y∈ball (0:Plane) R <;> simp [V,hy]
    rw [heV,integral_indicator measurableSet_ball]
  rwa [heI] at hh

lemma small_potential_parametrix {U q : Plane → ℝ} (hU : Smooth U) (_hq : Smooth q)
    (he : ∀x∈ball (0:Plane) (11/4),euclideanLaplacian U x+q x*U x=0)
    {x : Plane} (hx : x∈ball (0:Plane) (5/2)) :
    2*Real.pi*U x= -rconv logParametrix (fun y=>q y*U y) x-rconv parametrixKernel U x := by
  let χ : ContDiffBump (0:Plane):=⟨11/4,3,by norm_num,by norm_num⟩
  let V : Plane → ℝ:=fun y=>χ y*U y
  have hV : Smooth V:=χ.contDiff.mul hU
  have hcV : HasCompactSupport V:=χ.hasCompactSupport.mul_right
  have hVe {y : Plane} (hy : y∈ball (0:Plane) (11/4)) : V=ᶠ[𝓝 y]U := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    have hz' : z∈closedBall (0:Plane) χ.rIn:=ball_subset_closedBall hz
    simp only [V,χ.one_of_mem_closedBall hz',one_mul]
  have hi:=laplacian_parametrix_convolution hV hcV x
  rw [laplacian_rconv integrable_logParametrix hV hcV] at hi
  have hx' : ‖x‖<5/2:=mem_ball_zero_iff.mp hx
  have ht {y : Plane} (hy : ‖y‖≤1/4) : x-y∈ball (0:Plane) (11/4) :=
    mem_ball_zero_iff.mpr ((norm_sub_le x y).trans_lt (by linarith only [hx',hy]))
  have hQ : rconv logParametrix (euclideanLaplacian V) x= -rconv logParametrix (fun y=>q y*U y) x := by
    rw [rconv_eq,rconv_eq,←integral_neg]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : (1/4:ℝ)≤‖y‖
    · rw [logParametrix_zero hy]; simp
    · rw [laplacian_germ (hVe (ht (lt_of_not_ge hy).le))]
      have hh:=he (x-y) (ht (lt_of_not_ge hy).le)
      rw [show euclideanLaplacian U (x-y)= -(q (x-y)*U (x-y)) by linarith]
      ring
  have hK : rconv parametrixKernel V x=rconv parametrixKernel U x := by
    rw [rconv_eq,rconv_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : (1/4:ℝ)<‖y‖
    · rw [parametrixKernel_zero hy]; simp
    · rw [(hVe (ht (le_of_not_gt hy))).eq_of_nhds]
  rw [hQ,hK,(hVe (ball_subset_ball (by norm_num) hx)).eq_of_nhds] at hi
  linarith

lemma small_potential_L2_interior : ∃C : ℝ,1≤C ∧ ∀(U q : Plane → ℝ),Smooth U → Smooth q →
    (∀x∈ball (0:Plane) (11/4),euclideanLaplacian U x+q x*U x=0) →
    (∀x∈ball (0:Plane) 3,|q x|≤1) →
    ∀x∈ball (0:Plane) (5/2),|U x|≤C*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2) := by
  have hQ : MemLp logParametrix 2:=
    (memLp_two_iff_integrable_sq (parametrixCutoff.continuous.measurable.mul measurable_id.norm.log |>.aestronglyMeasurable)).mpr integrable_logParametrix_sq
  have hK : MemLp parametrixKernel 2:=
    (memLp_two_iff_integrable_sq smooth_parametrixKernel.continuous.aestronglyMeasurable).mpr
      ((smooth_parametrixKernel.pow 2).continuous.integrable_of_hasCompactSupport (by
        apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4))
        intro x hx
        rw [parametrixKernel_zero (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx)]
        norm_num))
  let N:=Real.sqrt (∫y,logParametrix y^2)+Real.sqrt (∫y,parametrixKernel y^2)
  let C:=1+(2*Real.pi)⁻¹*N
  have hN : 0≤N:=add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hC : 1≤C:=by dsimp [C]; have : 0≤(2*Real.pi)⁻¹*N:=mul_nonneg (by positivity) hN; linarith
  refine ⟨C,hC,?_⟩
  intro U q hU hq he hb x hx
  have hx' : ‖x‖+(1/4:ℝ)<11/4:=by have:=mem_ball_zero_iff.mp hx; linarith
  have hqU:=kernel_L2_bound hQ (hq.continuous.mul hU.continuous) hx'
    (fun y hy=>logParametrix_zero hy.le)
  have hKU:=kernel_L2_bound hK hU.continuous hx' (fun y hy=>parametrixKernel_zero hy)
  have hsq : (∫y in ball (0:Plane) (11/4),(q y*U y)^2)≤∫y in ball (0:Plane) (11/4),U y^2 := by
    apply integral_mono_ae (continuous_sq_integrableOn_ball (hq.continuous.mul hU.continuous) _) (continuous_sq_integrableOn_ball hU.continuous _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hyb:=hb y (ball_subset_ball (by norm_num) hy)
    have hq2 : q y^2≤1:=by have:=abs_nonneg (q y); nlinarith [sq_abs (q y)]
    change (q y*U y)^2≤_
    rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) hq2
  have hsqrt:=Real.sqrt_le_sqrt hsq
  have hqU':=hqU.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))
  change |rconv logParametrix (fun y=>q y*U y) x|≤_ at hqU'
  have hei:=small_potential_parametrix hU hq he hx
  have hn:=abs_add_le (-rconv logParametrix (fun y=>q y*U y) x) (-rconv parametrixKernel U x)
  rw [←sub_eq_add_neg,←hei,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),abs_neg,abs_neg] at hn
  have hpos : 0<2*Real.pi:=by positivity
  have hh : |U x|≤(2*Real.pi)⁻¹*N*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2) := by
    calc
      |U x|≤(N*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2))/(2*Real.pi) := by
        apply (le_div_iff₀ hpos).mpr
        dsimp [N]; nlinarith only [hn,hqU',hKU]
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.sqrt_nonneg _))
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma exists_local_smallness : ∃C ε δ : ℝ, NewtonControl C ∧ 0<ε ∧ ε≤1 ∧
    0≤δ ∧ δ≤1/4 ∧ C*ε≤δ ∧ Real.exp (8*C*(4*δ/(1-δ)))-1≤1/2048 := by
  obtain ⟨C,hC⟩:=exists_newtonControl
  have hCp : 0<C:=by linarith [hC.1]
  let δ:=min (1/8:ℝ) (Real.log (2049/2048)/(64*C))
  have hlog : 0<Real.log (2049/2048):=Real.log_pos (by norm_num)
  have hδ : 0<δ:=lt_min (by norm_num) (div_pos hlog (by positivity))
  have hδb : δ≤1/8:=min_le_left _ _
  have hδlog : 64*C*δ≤Real.log (2049/2048):=by
    have hd:=min_le_right (1/8:ℝ) (Real.log (2049/2048)/(64*C))
    exact (by nlinarith only [(le_div_iff₀ (show 0<64*C by positivity)).mp hd])
  have he : 8*C*(4*δ/(1-δ))≤Real.log (2049/2048) := by
    have hh : 4*δ/(1-δ)≤8*δ:=by apply (div_le_iff₀ (by linarith : 0<1-δ)).mpr; nlinarith
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans (by nlinarith only [hδlog])
  refine ⟨C,δ/C,δ,hC,div_pos hδ hCp,(div_le_one hCp).mpr (by linarith [hC.1]),hδ.le,by linarith,by field_simp; rfl,?_⟩
  have hh:=Real.exp_le_exp.mpr he
  rw [Real.exp_log (by norm_num : (0:ℝ)<2049/2048)] at hh
  linarith

lemma bump_smoothOn_extension {U : Plane → ℝ} (hU : ContDiffOn ℝ ∞ U (ball 0 3)) :
    ∃V : Plane → ℝ,Smooth V ∧ HasCompactSupport V ∧
      (∀x∈ball (0:Plane) (11/4),V=ᶠ[𝓝 x]U) ∧
      (∀x,|V x|≤|U x|) ∧ (∀x,3≤‖x‖ → V x=0) := by
  let χ : ContDiffBump (0:Plane):=⟨11/4,23/8,by norm_num,by norm_num⟩
  let V : Plane → ℝ:=fun x=>χ x*U x
  have hc : tsupport χ⊆ball (0:Plane) 3 := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  refine ⟨V,smooth_cutoff_mul isOpen_ball χ.contDiff hc hU,χ.hasCompactSupport.mul_right,?_,?_,?_⟩
  · intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hy' : y∈closedBall (0:Plane) χ.rIn:=ball_subset_closedBall hy
    simp only [V,χ.one_of_mem_closedBall hy',one_mul]
  · intro x
    dsimp [V]; rw [abs_mul,abs_of_nonneg (χ.nonneg (x:=x))]
    exact mul_le_of_le_one_left (abs_nonneg _) (χ.le_one (x:=x))
  · intro x hx
    have hz : χ x=0:=χ.zero_of_le_dist (by simpa only [dist_zero_right] using (show χ.rOut≤‖x‖ by dsimp [χ]; linarith))
    simp only [V,hz,zero_mul]
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma inner_L2_anchor {U : Plane → ℝ} (hU : Continuous U)
    (hI : 0<∫x in ball (0:Plane) (1/4),U x^2) :
    ∃y∈ball (0:Plane) (1/4),Real.sqrt (∫x in ball (0:Plane) (1/4),U x^2)/4≤|U y| := by
  let I:=∫x in ball (0:Plane) (1/4),U x^2
  have hn : 0≤Real.sqrt I/4:=by positivity
  have hv : volume.real (ball (0:Plane) (1/4))≤1 := by
    rw [measureReal_def,EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/4),ENNReal.toReal_ofReal Real.pi_pos.le]
    nlinarith [Real.pi_lt_four]
  by_contra he
  push Not at he
  have hb : ∀x∈ball (0:Plane) (1/4),U x^2≤(Real.sqrt I/4)^2 := by
    intro x hx
    have hh : |U x|≤Real.sqrt I/4:=(he x hx).le
    nlinarith [sq_abs (U x),abs_nonneg (U x)]
  have hi:=integral_mono_ae (continuous_sq_integrableOn_ball hU (1/4))
    (integrableOn_const (C:=((Real.sqrt I/4)^2)) measure_ball_ne_top)
    ((ae_restrict_mem measurableSet_ball).mono (fun x hx=>hb x hx))
  rw [integral_const,measureReal_def,Measure.restrict_apply_univ,←measureReal_def,smul_eq_mul] at hi
  have hh:=mul_le_mul_of_nonneg_right hv (sq_nonneg (Real.sqrt I/4))
  have hs:=Real.sq_sqrt hI.le
  dsimp [I] at hi hh ⊢
  nlinarith

lemma sq_integral_ball_mono {U : Plane → ℝ} (hU : Continuous U) {r R : ℝ} (hrR : r≤R) :
    (∫x in ball (0:Plane) r,U x^2)≤∫x in ball (0:Plane) R,U x^2 :=
  integral_mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hrR))
    (Eventually.of_forall (fun x=>sq_nonneg (U x))) (continuous_sq_integrableOn_ball hU R)

theorem small_potential_L2_length : ∃ε L : ℝ,0<ε ∧ 0<L ∧
    ∀(U q : Plane → ℝ),ContDiffOn ℝ ∞ U (ball 0 3) → ContDiffOn ℝ ∞ q (ball 0 3) →
    (∀x∈ball (0:Plane) 3,euclideanLaplacian U x+q x*U x=0) →
    (∀x∈ball (0:Plane) 3,|q x|≤ε) →
    0<(∫x in ball (0:Plane) (1/4),U x^2) →
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ U x=0}≤
      ENNReal.ofReal (L*(1+(Real.log (∫x in ball (0:Plane) (11/4),U x^2)-
        Real.log (∫x in ball (0:Plane) (1/4),U x^2))/2)) := by
  obtain ⟨C,ε,δ,hC,hε,hε1,hδ,hδ1,hsmall,hη⟩:=exists_local_smallness
  obtain ⟨L₀,hL₀,hL⟩:=normalized_small_potential_length
  obtain ⟨B,hB,hBb⟩:=small_potential_L2_interior
  have hBp : 0<B:=by linarith
  have hlogB : 0≤Real.log (4*B):=Real.log_nonneg (by linarith)
  refine ⟨ε,L₀*(1+Real.log (4*B)),hε,mul_pos hL₀ (by linarith),?_⟩
  intro U q hU hq he hqb hI
  obtain ⟨V,hV,-,hVe,-,-⟩:=bump_smoothOn_extension hU
  obtain ⟨Q,hQ,hcQ,hQe,hQb,hQs⟩:=bump_smoothOn_extension hq
  have hSP : SmallPotential C ε δ Q:=⟨hC,hε.le,hδ,hδ1,hsmall,hQ,hcQ,hQs,
    fun x hx=>(hQb x).trans (hqb x hx)⟩
  have hVE : ∀x∈ball (0:Plane) (11/4),euclideanLaplacian V x+Q x*V x=0 := by
    intro x hx
    rw [laplacian_germ (hVe x hx),(hVe x hx).eq_of_nhds,(hQe x hx).eq_of_nhds]
    exact he x (ball_subset_ball (by norm_num) hx)
  have hmass (r : ℝ) (hr : r≤11/4) :
      (∫x in ball (0:Plane) r,V x^2)=∫x in ball (0:Plane) r,U x^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [(hVe x (ball_subset_ball hr hx)).eq_of_nhds]
  let I:=∫x in ball (0:Plane) (1/4),V x^2
  let O:=∫x in ball (0:Plane) (11/4),V x^2
  have hIp : 0<I:=by dsimp [I]; rwa [hmass (1/4) (by norm_num)]
  have hIO : I≤O:=sq_integral_ball_mono hV.continuous (by norm_num)
  have hOp : 0<O:=lt_of_lt_of_le hIp hIO
  let a:=Real.sqrt I/4
  have hap : 0<a:=div_pos (Real.sqrt_pos.2 hIp) (by norm_num)
  let S:=4*B*Real.sqrt O/Real.sqrt I
  have hS : 1≤S:=by
    apply (le_div_iff₀ (Real.sqrt_pos.2 hIp)).mpr
    have hroot:=Real.sqrt_le_sqrt hIO
    nlinarith [Real.sqrt_nonneg I,Real.sqrt_nonneg O]
  have hW : Smooth (fun x=>a⁻¹*V x):=contDiff_const.mul hV
  have hWE : ∀x∈ball (0:Plane) (5/2),euclideanLaplacian (fun y=>a⁻¹*V y) x+
      Q x*(a⁻¹*V x)=0 := by
    intro x hx
    rw [laplacian_const_mul hV]
    have hh:=hVE x (ball_subset_ball (by norm_num) hx)
    linear_combination a⁻¹*hh
  have hbV:=hBb V Q hV hQ hVE (fun x hx=>(hSP.bound x hx).trans hε1)
  have hWb : ∀x∈ball (0:Plane) (5/2),|a⁻¹*V x|≤S := by
    intro x hx
    rw [abs_mul,abs_of_pos (inv_pos.mpr hap)]
    have ht:=mul_le_mul_of_nonneg_left (hbV x hx) (inv_nonneg.mpr hap.le)
    exact ht.trans_eq (by dsimp [S,a]; ring)
  obtain ⟨y,hy,hyb⟩:=inner_L2_anchor hV.continuous hIp
  have han : ∃y∈ball (0:Plane) (1/4),1≤|a⁻¹*V y| := by
    refine ⟨y,hy,?_⟩
    rw [abs_mul,abs_of_pos (inv_pos.mpr hap),inv_mul_eq_div]
    exact (le_div_iff₀ hap).mpr (by simpa only [one_mul] using hyb)
  have hh:=hL hSP hη hW hWE S hS hWb han
  have hz : {x | x∈ball (0:Plane) (1/60) ∧ a⁻¹*V x=0}=
      {x | x∈ball (0:Plane) (1/60) ∧ U x=0} := by
    ext x
    by_cases hx : x∈ball (0:Plane) (1/60)
    · simp only [mem_ofPred_eq,hx,true_and,mul_eq_zero,inv_ne_zero hap.ne',false_or,
        (hVe x (ball_subset_ball (by norm_num) hx)).eq_of_nhds]
    · simp only [mem_ofPred_eq,hx,false_and]
  rw [hz] at hh
  have heS : Real.log S=Real.log (4*B)+(Real.log O-Real.log I)/2 := by
    dsimp [S]
    rw [Real.log_div (mul_ne_zero (by positivity) (Real.sqrt_pos.2 hOp).ne')
      (Real.sqrt_pos.2 hIp).ne',Real.log_mul (by positivity : 4*B≠0) (Real.sqrt_pos.2 hOp).ne',
      Real.log_sqrt hOp.le,Real.log_sqrt hIp.le]
    ring
  have hE : 0≤(Real.log O-Real.log I)/2:=by have:=Real.log_le_log hIp hIO; linarith
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  rw [heS]
  rw [←hmass (11/4) le_rfl,←hmass (1/4) (by norm_num)]
  change L₀*(1+(Real.log (4*B)+(Real.log O-Real.log I)/2))≤L₀*(1+Real.log (4*B))*(1+(Real.log O-Real.log I)/2)
  nlinarith [mul_nonneg hL₀.le (mul_nonneg hlogB hE)]
end SharpNodal.Profiles

end
end
end
end

end OAI
