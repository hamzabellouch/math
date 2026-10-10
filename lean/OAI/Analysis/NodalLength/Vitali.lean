import OAI.Analysis.NodalLength.GradientCones

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

namespace SharpNodal

lemma vitali_measure_bound {α : Type*} [MetricSpace α] [SeparableSpace α]
    [MeasurableSpace α] [BorelSpace α] (ν μ : Measure α) (S D : Set α)
    (r : α → ℝ) {R : ℝ} (hr : ∀x∈S,0<r x) (hb : ∀x∈S,r x≤R)
    (hD : ∀x∈S,ball x (r x)⊆D) (C : ℝ≥0∞)
    (hlocal : ∀x∈S,ν (S∩ball x (4*r x))≤C*μ (ball x (r x))) :
    ν S≤C*μ D := by
  obtain ⟨T,hTS,hdis,hcover⟩:=Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    S id r R hb 4 (by norm_num)
  have hcount : T.Countable := hdis.countable_of_isOpen (fun _ _=>isOpen_ball)
    (fun x hx=>nonempty_ball.mpr (hr x (hTS hx)))
  let _ : Countable T :=hcount.to_subtype
  have hc : S⊆⋃x : T,S∩ball x.val (4*r x.val) := by
    intro x hx
    obtain ⟨y,hy,hyc⟩:=hcover x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hx,hyc (mem_ball_self (hr x hx))⟩
  have hpd : Pairwise (Disjoint on (fun x : T=>ball x.val (r x.val))) := by
    intro x y hne
    exact hdis x.property y.property (fun he=>hne (Subtype.ext he))
  calc
    ν S ≤ ν (⋃x : T,S∩ball x.val (4*r x.val)) :=measure_mono hc
    _ ≤ ∑'x : T,ν (S∩ball x.val (4*r x.val)) :=measure_iUnion_le _
    _ ≤ ∑'x : T,C*μ (ball x.val (r x.val)) :=ENNReal.tsum_le_tsum (fun x=>hlocal x.val (hTS x.property))
    _ = C*(∑'x : T,μ (ball x.val (r x.val))) :=ENNReal.tsum_mul_left
    _ = C*μ (⋃x : T,ball x.val (r x.val)) :=by rw [measure_iUnion hpd (fun _=>measurableSet_ball)]
    _ ≤ C*μ D :=mul_le_mul_right (measure_mono (iUnion_subset (fun (x : T)=>hD x.val (hTS x.property)))) _

end SharpNodal

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
namespace SharpNodal.Profiles

lemma inverse_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane =>‖x‖⁻¹) (ball (0:Plane) R) := by
  rw [integrableOn_fun_norm_addHaar]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,pow_one,smul_eq_mul]
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo 0 R) := integrableOn_const (by simp)
  exact hi.congr_fun
    (fun r hr=>by rw [mul_inv_cancel₀ (ne_of_gt hr.1)]) measurableSet_Ioo

lemma integral_inverse_norm_ball {R : ℝ} (hR : 0≤R) :
    (∫x in ball (0:Plane) R,‖x‖⁻¹)=2*Real.pi*R := by
  rw [plane_radial_ball_integral (fun r=>r⁻¹) R]
  have he : (∫r in Ioo (0:ℝ) R,r*r⁻¹)=R := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun r hr=>mul_inv_cancel₀ (ne_of_gt hr.1))]
    simp [hR]
  rw [he]

lemma inverse_translate_integrable_bound {a : Plane} (ha : ‖a‖<1/2) :
    IntegrableOn (fun x : Plane=>‖x-a‖⁻¹) (ball (0:Plane) 1) ∧
      (∫x in ball (0:Plane) 1,‖x-a‖⁻¹)≤4*Real.pi := by
  let F : Plane → ℝ :=(ball (0:Plane) 2).indicator (fun x=>‖x‖⁻¹)
  have hi : Integrable F :=(inverse_norm_integrableOn_ball 2).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x=>F (x-a)) :=
    (measurePreserving_sub_right volume a).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  have he (x : Plane) (hx : x∈ball (0:Plane) 1) : ‖x-a‖⁻¹=F (x-a) := by
    have hn : ‖x-a‖<2 := by
      have hh:=norm_sub_le x a
      have hx':=mem_ball_zero_iff.mp hx
      linarith
    dsimp [F]
    rw [indicator_of_mem (show x-a∈ball (0:Plane) 2 from mem_ball_zero_iff.mpr hn)]
  have hin : IntegrableOn (fun x : Plane=>‖x-a‖⁻¹) (ball (0:Plane) 1) :=
    hit.integrableOn.congr_fun (fun x hx=>(he x hx).symm) measurableSet_ball
  refine ⟨hin,?_⟩
  calc
    _ = ∫x in ball (0:Plane) 1,F (x-a) :=setIntegral_congr_fun measurableSet_ball he
    _ ≤ ∫x,F (x-a) :=integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x=>indicator_nonneg (fun y _=>by positivity) _)) hit
    _ = ∫x,F x :=integral_sub_right_eq_self F a
    _ = ∫x in ball (0:Plane) 2,‖x‖⁻¹ :=integral_indicator measurableSet_ball
    _ = 4*Real.pi :=by rw [integral_inverse_norm_ball (by norm_num)]; ring

lemma complex_difference_norm (x : Plane) (a : ℂ) :
    ‖planeToComplex x-a‖=‖x-complexToPlane a‖ := by
  have he:=planeToComplex.norm_map (x-complexToPlane a)
  simpa only [map_sub,planeToComplex,LinearIsometryEquiv.symm_apply_apply] using he

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
namespace SharpNodal.Profiles
open Holomorphic

def weightMeasure (S : Finset ℂ) (m : ℂ → ℕ) (B : ℝ) : Measure Plane :=
  volume.withDensity (fun x=>ENNReal.ofReal (zeroWeight S m B (planeToComplex x)))

lemma weightMeasure_unit_bound (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 0<B)
    (hS : ∀a∈S,a∈ball 0 (1/2)) :
    weightMeasure S m B (ball (0:Plane) 1) ≤ ENNReal.ofReal (Real.pi*B+4*Real.pi*∑a∈S,(m a:ℝ)) := by
  have hk (a : ℂ) (ha : a∈S) := inverse_translate_integrable_bound
    (a:=complexToPlane a) (by simpa only [complexToPlane.norm_map] using mem_ball_zero_iff.mp (hS a ha))
  have hi : IntegrableOn (fun x : Plane=>zeroWeight S m B (planeToComplex x)) (ball (0:Plane) 1) := by
    simp only [zeroWeight,complex_difference_norm]
    exact (integrableOn_const (C:=B)).add (integrable_finsetSum S (fun a ha =>(hk a ha).1.const_mul _))
  have hnn : 0≤ᵐ[volume.restrict (ball (0:Plane) 1)] (fun x=>zeroWeight S m B (planeToComplex x)) :=
    Eventually.of_forall (fun x=>(zeroWeight_pos hB _).le)
  rw [weightMeasure,withDensity_apply _ measurableSet_ball,←ofReal_integral_eq_lintegral_ofReal hi hnn]
  apply ENNReal.ofReal_le_ofReal
  simp only [zeroWeight,complex_difference_norm]
  rw [integral_add (integrableOn_const (C:=B) (μ:=volume) (s:=ball (0:Plane) 1)) (integrable_finsetSum S (fun a ha=>(hk a ha).1.const_mul _)),
    integral_const,integral_finsetSum S (fun a ha=>(hk a ha).1.const_mul _)]
  simp only [integral_const_mul,Measure.restrict_apply_univ,measureReal_def,EuclideanSpace.volume_ball_fin_two,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal Real.pi_pos.le,smul_eq_mul]
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun a ha=>by nlinarith [mul_le_mul_of_nonneg_left (hk a ha).2 (Nat.cast_nonneg (m a))])

lemma weightMeasure_local_lower (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 1≤B)
    (hm : ∀a∈S,0 < m a) {c : Plane} (hc : ∀a∈S,planeToComplex c≠a) :
    ENNReal.ofReal (1/(2097152*zeroWeight S m B (planeToComplex c))) ≤
      weightMeasure S m B (ball c (1/(1024*zeroWeight S m B (planeToComplex c)))) := by
  let W:=zeroWeight S m B (planeToComplex c)
  let r:=1/(1024*W)
  have hW : 0<W:=zeroWeight_pos (by linarith : 0<B) _
  have hr : 0<r:=by dsimp [r]; positivity
  have hw (x : Plane) (hx : x∈ball c r) : W/2≤zeroWeight S m B (planeToComplex x) := by
    apply (zeroWeight_local_comparison (by linarith : 0<B) hc hm (w:=planeToComplex x) ?_).2.1
    rw [←map_sub,planeToComplex.norm_map]
    have hd : ‖x-c‖<r:=by simpa only [dist_eq_norm] using mem_ball.mp hx
    apply hd.le.trans
    change r≤1/(4*W)
    dsimp [r]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have he : ENNReal.ofReal (W/2)*volume (ball c r) ≤ weightMeasure S m B (ball c r) := by
    rw [weightMeasure,withDensity_apply _ measurableSet_ball,←Measure.restrict_apply_univ (μ:=volume) (s:=ball c r),←lintegral_const]
    exact lintegral_mono_ae (by filter_upwards [ae_restrict_mem measurableSet_ball] with x hx; exact ENNReal.ofReal_le_ofReal (hw x hx))
  have hvol : volume (ball c r)=ENNReal.ofReal (Real.pi*r^2) := by
    rw [EuclideanSpace.volume_ball_fin_two,←ENNReal.ofReal_pow hr.le,←ENNReal.ofReal_mul (sq_nonneg r)]
    congr 1; ring
  rw [hvol,←ENNReal.ofReal_mul (by positivity)] at he
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) he
  change 1/(2097152*W)≤W/2*(Real.pi*r^2)
  dsimp [r]
  have hpi : 1≤Real.pi:=by linarith [Real.pi_gt_three]
  field_simp
  nlinarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Holomorphic Carleman

lemma nodal_length_of_weight {H : ℂ → ℂ} {v : Plane → ℝ}
    (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 1≤B)
    (hS : ∀a∈S,a∈ball 0 (1/2) ∧ 0 < m a)
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hHne : ∀z∈closedBall 0 (1/3),(∀a∈S,z≠a) → H z≠0)
    (hHd : ∀z∈closedBall 0 (1/3),(∀a∈S,z≠a) → ‖logDeriv H z‖≤zeroWeight S m B z)
    (hv : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ v x)
    (hcomp : ∀x∈ball (0:Plane) 1,‖complexGradient v x-H (planeToComplex x)‖≤‖H (planeToComplex x)‖/1024) :
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/4) ∧ v x=0}
      ≤ ENNReal.ofReal (65536*(Real.pi*B+4*Real.pi*∑a∈S,(m a:ℝ))) := by
  classical
  let K : Set Plane:=planeToComplex ⁻¹' (S : Set ℂ)
  let Z : Set Plane:={x | x∈ball (0:Plane) (1/4) ∧ v x=0}
  let T:=Z\K
  let W : Plane → ℝ:=fun x=>zeroWeight S m B (planeToComplex x)
  let r : Plane → ℝ:=fun x=>1/(1024*W x)
  have hWp (x : Plane) : 0<W x:=zeroWeight_pos (by linarith :0<B) _
  have hW (x : Plane) : 1≤W x := by
    have hs : 0≤∑a∈S,(m a:ℝ)*‖planeToComplex x-a‖⁻¹ :=Finset.sum_nonneg (fun _ _=>by positivity)
    dsimp [W,zeroWeight]; linarith
  have hr (x : Plane) : 0<r x:=by have hp:=hWp x; dsimp [r]; positivity
  have hrb (x : Plane) : r x≤1/1024 := by
    have hp:=hWp x
    dsimp [r]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hW x]
  have hca (x : Plane) (hx : x∈T) (a : ℂ) (ha : a∈S) : planeToComplex x≠a := by
    intro he; exact hx.2 (by change planeToComplex x∈S; simpa only [he] using ha)
  have hD (x : Plane) (hx : x∈T) : ball x (r x)⊆ball (0:Plane) 1 := by
    intro y hy
    have hx' : ‖x‖<1/4:=mem_ball_zero_iff.mp hx.1.1
    have hy' : ‖y-x‖<r x:=by simpa only [dist_eq_norm] using mem_ball.mp hy
    have ht:=norm_add_le (y-x) x
    rw [sub_add_cancel] at ht
    exact mem_ball_zero_iff.mpr (by linarith [hrb x])
  have hlocal (x : Plane) (hx : x∈T) : Measure.hausdorffMeasure 1 (T∩ball x (4*r x))≤
      (65536:ℝ≥0∞)*weightMeasure S m B (ball x (r x)) := by
    have hlen:=holomorphic_gradient_local_length S m hB (fun a ha=>(hS a ha).2) hH hHne hHd hv hcomp hx.1.1 (hca x hx)
    have hlow:=weightMeasure_local_lower S m hB (fun a ha=>(hS a ha).2) (hca x hx)
    have he : 4*r x=4/(1024*W x):=by dsimp [r]; ring
    have hs : T∩ball x (4*r x)⊆{y | y∈ball x (4/(1024*W x)) ∧ v y=0} :=by
      intro y hy; exact ⟨he ▸ hy.2,hy.1.1.2⟩
    apply (measure_mono hs).trans (hlen.trans ?_)
    have hconst : ENNReal.ofReal (32/(1024*W x))=(65536:ℝ≥0∞)*ENNReal.ofReal (1/(2097152*W x)) :=by
      rw [←ENNReal.ofReal_ofNat 65536,←ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [hconst]
    exact mul_le_mul_right hlow _
  have hbound:=vitali_measure_bound (Measure.hausdorffMeasure 1) (weightMeasure S m B) T (ball (0:Plane) 1) r
    (R:=1/1024) (fun x _=>hr x) (fun x _=>hrb x) hD 65536 hlocal
  have hkfin : K.Finite:=S.finite_toSet.preimage planeToComplex.injective.injOn
  have : NullSingletonClass (Measure.hausdorffMeasure (X:=Plane) 1):=Measure.nullSingletonClass_hausdorff Plane (by norm_num)
  have hK : Measure.hausdorffMeasure 1 K=0:=hkfin.measure_zero _
  have hZ : Z⊆T∪K:=fun x hx=>by by_cases h : x∈K; exact Or.inr h; exact Or.inl ⟨hx,h⟩
  calc
    Measure.hausdorffMeasure 1 Z ≤ Measure.hausdorffMeasure 1 T+Measure.hausdorffMeasure 1 K :=measure_union_le _ _ |>.trans' (measure_mono hZ)
    _ ≤ (65536:ℝ≥0∞)*weightMeasure S m B (ball (0:Plane) 1) := by simpa only [hK,add_zero] using hbound
    _ ≤ (65536:ℝ≥0∞)*ENNReal.ofReal (Real.pi*B+4*Real.pi*∑a∈S,(m a:ℝ)) :=
      mul_le_mul_right (weightMeasure_unit_bound S m (by linarith) (fun a ha=>(hS a ha).1)) _
    _ = _ :=by rw [←ENNReal.ofReal_ofNat 65536,←ENNReal.ofReal_mul (by norm_num)]

lemma nodal_length_holomorphic_comparison {H : ℂ → ℂ} {v : Plane → ℝ} {M : ℝ}
    (hM : 1≤M) (hH : DifferentiableOn ℂ H (ball 0 1)) (hH0 : H 0≠0)
    (hb : ∀z∈closedBall 0 (2/3),‖H z‖≤M)
    (hv : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ v x)
    (hcomp : ∀x∈ball (0:Plane) 1,‖complexGradient v x-H (planeToComplex x)‖≤‖H (planeToComplex x)‖/1024) :
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/4) ∧ v x=0} ≤
      ENNReal.ofReal ((65536*4*Real.pi*(201+7/Real.log (4/3)))*(1+Real.log (M/‖H 0‖))) := by
  have han : AnalyticOnNhd ℂ H (closedBall 0 (2/3)) := by
    intro z hz
    exact hH.analyticAt (isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num) hz))
  obtain ⟨S,m,B,hS,hB,hBN,hne,hd⟩:=exists_zeroWeight hM han hH0 hb
  apply (nodal_length_of_weight S m hB hS hH hne hd hv hcomp).trans
  apply ENNReal.ofReal_le_ofReal
  have hp:=Real.pi_pos
  have hmul:=mul_le_mul_of_nonneg_left hBN (by positivity : 0≤65536*4*Real.pi)
  nlinarith

end SharpNodal.Profiles

end
end
end
end

end OAI
