import OAI.Probability.GaussianPropeller.Coordinates

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Cap
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

noncomputable def coneCap (n : ℕ) (a : ℝ) : Set (CE (n+1)) :=
  {x | a*‖(split n x).2‖ < x 0}

lemma measurableSet_coneCap (n : ℕ) (a : ℝ) : MeasurableSet (coneCap n a) := by
  apply isOpen_lt (by exact continuous_const.mul ((continuous_split n).snd.norm)) (by fun_prop) |>.measurableSet

lemma coneCap_smul (a : ℝ) {r : ℝ} (hr : 0<r) (x : CE (n+1)) :
    r•x∈coneCap n a ↔ x∈coneCap n a := by
  have he : (split n (r•x)).2 = r•(split n x).2 := by ext i; rfl
  simp only [coneCap,mem_ofPred_eq,he,norm_smul,Real.norm_eq_abs,abs_of_pos hr,PiLp.smul_apply,smul_eq_mul]
  rw [← mul_assoc, mul_comm a r, mul_assoc, mul_lt_mul_iff_right₀ hr]

lemma integrable_coord : Integrable (fun x : CE (n+1) => x 0) (stdGaussian (CE (n+1))) := by
  apply Integrable.mono' IsGaussian.integrable_id.norm (by fun_prop)
  filter_upwards [] with x
  exact PiLp.norm_apply_le x 0

lemma tail_first_gaussian (a : ℝ) : ∫ x in Ioi a, x ∂gaussianReal 0 1 = gaussianConst*density a := by
  rw [← integral_indicator measurableSet_Ioi,integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun x=>x) x*density x) =
      (Ioi a).indicator (fun x => x*density x) := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi,tail_first_moment]

lemma integral_cap (n : ℕ) (a : ℝ) :
    ∫ x : CE (n+1), (coneCap n a).indicator (fun _ => (1:ℝ)) x ∂stdGaussian (CE (n+1)) = capP n a := by
  rw [integral_split]
  have hi : Integrable (fun y => (coneCap n a).indicator (fun _ => (1:ℝ)) (join n y))
      ((gaussianReal 0 1).prod (stdGaussian (CE n))) :=
    ((measurePreserving_split n).symm.integrable_comp
      (((integrable_const (1:ℝ)).indicator (measurableSet_coneCap n a)).aestronglyMeasurable)).mpr
      ((integrable_const (1:ℝ)).indicator (measurableSet_coneCap n a))
  rw [integral_prod_symm _ hi]
  unfold capP
  apply integral_congr_ae
  filter_upwards [] with y
  rw [p_eq_integral_indicator]
  rfl

lemma moment_cap (n : ℕ) (a : ℝ) :
    ∫ x : CE (n+1), (coneCap n a).indicator (fun x => x 0) x ∂stdGaussian (CE (n+1)) = capM n a := by
  rw [integral_split]
  have hi : Integrable (fun y => (coneCap n a).indicator (fun x => x 0) (join n y))
      ((gaussianReal 0 1).prod (stdGaussian (CE n))) :=
    ((measurePreserving_split n).symm.integrable_comp
      ((integrable_coord.indicator (measurableSet_coneCap n a)).aestronglyMeasurable)).mpr
      (integrable_coord.indicator (measurableSet_coneCap n a))
  rw [integral_prod_symm _ hi]
  unfold capM
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← tail_first_gaussian,← integral_indicator measurableSet_Ioi]
  rfl

lemma integral_cone_norm {d : ℕ} (hd : 0<d) (K : Set (CE d))
    (hK : MeasurableSet K) (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) :
    (∫ x : CE d, K.indicator (fun x => ‖x‖) x ∂stdGaussian (CE d)) =
      radial d (1/2)/radial (d-1) (1/2) * (stdGaussian (CE d)).real K := by
  let : NeZero d := ⟨by omega⟩
  have h0 := integral_homogeneous (ι:=Fin d) (K.indicator (fun _ => (1:ℝ))) 0 (by
    intro r hr x
    by_cases hx : x∈K <;> simp [hcone r hr x,hx])
  have h1 := integral_homogeneous (ι:=Fin d) (K.indicator (fun x => ‖x‖)) 1 (by
    intro r hr x
    by_cases hx : x∈K <;> simp [hcone r hr x,hx,norm_smul,Real.norm_eq_abs,abs_of_pos hr])
  have he : (fun θ : Metric.sphere (0:CE d) 1 => K.indicator (fun x => ‖x‖) θ.1) =
      fun θ : Metric.sphere (0:CE d) 1 => K.indicator (fun _ => (1:ℝ)) θ.1 := by
    funext θ
    by_cases hh : θ.1∈K <;> simp [hh, mem_sphere_zero_iff_norm.mp θ.2]
  rw [he] at h1
  simp only [Fintype.card_fin,Nat.add_zero,show d-1+1=d by omega] at h0 h1
  rw [integral_indicator hK,setIntegral_const,smul_eq_mul,mul_one] at h0
  have hr (q:ℕ) : (∫ r in Ioi (0:ℝ), r^q*Real.exp (-r^2/2))=radial q (1/2) := by
    unfold radial
    congr 1
    funext r; congr 2; ring
  rw [hr] at h0 h1
  rw [h1,h0]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (radial_pos (d-1) (b:=1/2) (by norm_num)).ne').mpr
  ring

lemma coneCap_criterion {a : ℝ} (ha : 0≤a) (x : CE (n+1)) :
    x∈coneCap n a ↔ a/Real.sqrt (1+a^2)*‖x‖ < x 0 := by
  have hp : 0 < Real.sqrt (1+a^2) := by positivity
  have hs := Real.sq_sqrt (show 0≤1+a^2 by positivity)
  have hn := norm_join_sq n (split n x)
  rw [join_split] at hn
  change ‖x‖^2 = (x 0)^2+‖(split n x).2‖^2 at hn
  change a*‖(split n x).2‖ < x 0 ↔ _
  rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
  constructor
  · intro h
    have hx : 0 < x 0 := lt_of_le_of_lt (by positivity) h
    have hs1 : (a*‖(split n x).2‖)^2 < (x 0)^2 := sq_lt_sq₀ (by positivity) hx.le |>.mpr h
    have hs2 : (a*‖x‖)^2 < (x 0*Real.sqrt (1+a^2))^2 := by nlinarith only [hs1,hn,hs]
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hs2
  · intro h
    have hx : 0 < x 0 := (mul_pos_iff_of_pos_right hp).mp (lt_of_le_of_lt (by positivity) h)
    have hs1 : (a*‖x‖)^2 < (x 0*Real.sqrt (1+a^2))^2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
    have hs2 : (a*‖(split n x).2‖)^2 < (x 0)^2 := by nlinarith only [hs1,hn,hs]
    exact (sq_lt_sq₀ (by positivity) hx.le).mp hs2

lemma moment_rearrange (K : Set (CE (n+1))) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) {a : ℝ} (ha : 0≤a) :
    (∫ x : CE (n+1), K.indicator (fun x=>x 0) x ∂stdGaussian (CE (n+1))) ≤
      capM n a + a/Real.sqrt (1+a^2) * (radial (n+1) (1/2)/radial n (1/2)) *
        ((stdGaussian (CE (n+1))).real K-capP n a) := by
  let b := a/Real.sqrt (1+a^2)
  let C := coneCap n a
  have hn : Integrable (fun x : CE (n+1)=>‖x‖) (stdGaussian (CE (n+1))) := IsGaussian.integrable_id.norm
  have hf : Integrable (fun x : CE (n+1)=> x 0-b*‖x‖) (stdGaussian (CE (n+1))) :=
    integrable_coord.sub (hn.const_mul b)
  have hi := integral_mono (hf.indicator hK) (hf.indicator (measurableSet_coneCap n a)) (fun x => show
      K.indicator (fun x=>x 0-b*‖x‖) x ≤ C.indicator (fun x=>x 0-b*‖x‖) x from by
    by_cases hk : x∈K <;> by_cases hc : x∈C
    · simp [hk,hc]
    · simp only [indicator_of_mem hk,indicator_of_notMem hc]
      exact sub_nonpos.mpr (not_lt.mp (mt (coneCap_criterion ha x).mpr hc))
    · simp only [indicator_of_notMem hk,indicator_of_mem hc]
      exact sub_nonneg.mpr ((coneCap_criterion ha x).mp hc).le
    · simp [hk,hc])
  simp_rw [indicator_sub,indicator_const_mul] at hi
  rw [integral_sub (integrable_coord.indicator hK) ((hn.indicator hK).const_mul b),
    integral_const_mul,
    integral_sub (integrable_coord.indicator (measurableSet_coneCap n a))
      ((hn.indicator (measurableSet_coneCap n a)).const_mul b),integral_const_mul,
    integral_cone_norm (by omega) K hK hcone,
    integral_cone_norm (by omega) C (measurableSet_coneCap n a) (fun r hr x=>coneCap_smul a hr x),
    moment_cap,show n+1-1=n by omega] at hi
  have hp : (stdGaussian (CE (n+1))).real C = capP n a := by
    rw [← integral_cap,integral_indicator (measurableSet_coneCap n a),setIntegral_const]
    simp only [smul_eq_mul,mul_one]
    rfl
  rw [hp] at hi
  dsimp [b] at hi
  linarith only [hi]

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar

lemma cap_parameter {b : ℝ} (hb : 0≤b) (hb1 : b<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ ∧
    (b/Real.sqrt (1-b^2))/Real.sqrt (1+(b/Real.sqrt (1-b^2))^2)=b := by
  have hpos : 0<1-b^2 := by nlinarith only [hb,hb1]
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr hpos
  have hs := Real.sq_sqrt hpos.le
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp
    nlinarith only [hs]
  refine ⟨?_,?_⟩
  · rw [he,Real.sqrt_sq (by positivity)]
  · rw [he,Real.sqrt_sq (by positivity)]
    field_simp

lemma cone_three (K : Set (CE 3)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : (stdGaussian (CE 3)).real K ∈ Ioo (0:ℝ) 1)
    (hPh : (stdGaussian (CE 3)).real K ≤ 1/2) :
    (∫ x : CE 3, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 3)) ≤
      4*gaussianConst*(stdGaussian (CE 3)).real K*(1-(stdGaussian (CE 3)).real K) := by
  let P := (stdGaussian (CE 3)).real K
  let b := 1-2*P
  have hb : 0≤b := by dsimp [b,P]; linarith only [hPh]
  have hb1 : b<1 := by dsimp [b,P]; linarith only [hP.1]
  have hh := cap_parameter hb hb1
  have hr := moment_rearrange (n:=2) K hK hcone (a:=b/Real.sqrt (1-b^2)) (by positivity)
  rw [capP_two,hh.2,capM_eq (by omega),hh.1,inv_inv] at hr
  have hs : 0≤1-b^2 := by nlinarith only [hb,hb1]
  rw [Real.sq_sqrt hs] at hr
  have he : (1-b)/2=P := by dsimp [b]; ring
  rw [he,show (stdGaussian (CE (2+1))).real K=P from rfl,sub_self,mul_zero,add_zero] at hr
  dsimp [b,P] at hr
  nlinarith only [hr]

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma capP_deriv_three (a : ℝ) : HasDerivAt (capP 3)
    (-(2/Real.pi:ℝ)*(Real.sqrt (1+a^2))⁻¹^4) a := by
  have hh := integral_norm_pow_exp (ι:=Fin 3) 1 (a:=a^2/2) (by positivity)
  have hs := radial_scale 3 (b:=a^2/2+1/2) (by positivity)
  norm_num only [Fintype.card_fin, Nat.reduceSub, Nat.reduceAdd, pow_one] at hh
  have hd := hasDerivAt_capP (n:=3) a
  have he : (fun y : CE 3 => ‖y‖*density (a*‖y‖)) = fun y => ‖y‖*Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 2; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,radial_half_three,radial_half_two] at hd
  convert hd using 1
  have hp : 0<Real.sqrt (2*Real.pi) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  dsimp [gaussianConst]
  field_simp
  nlinarith only [hsq]

noncomputable def sphereTail (b:ℝ) := ∫ u in b..1, Real.sqrt (1-u^2)

lemma sphereTail_zero : sphereTail 0 = Real.pi/4 := by
  have hi : IntervalIntegrable (fun u:ℝ=>Real.sqrt (1-u^2)) volume (-1) 0 := by
    exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun u:ℝ=>Real.sqrt (1-u^2)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  have he := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hn := intervalIntegral.integral_comp_neg (f:=fun u:ℝ=>Real.sqrt (1-u^2)) (a:=(0:ℝ)) (b:=1)
  simp only [neg_zero,neg_sq] at hn
  rw [integral_sqrt_one_sub_sq] at he
  dsimp [sphereTail]
  linarith only [he,hn]

lemma hasDerivAt_sphereTail (b:ℝ) : HasDerivAt sphereTail (-Real.sqrt (1-b^2)) b := by
  apply intervalIntegral.integral_hasDerivAt_left
  · exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).stronglyMeasurable.stronglyMeasurableAtFilter
  · fun_prop

lemma cap_parameter' {b:ℝ} (hb:b^2<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ := by
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by linarith only [hb])
  have hs := Real.sq_sqrt (show 0≤1-b^2 by linarith only [hb])
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp; nlinarith only [hs]
  rw [he,Real.sqrt_sq (by positivity)]

lemma capP_three_sphere {b:ℝ} (hb:b∈Ioo (-1:ℝ) 1) :
    capP 3 (b/Real.sqrt (1-b^2)) = 2/Real.pi*sphereTail b := by
  have hd (x:ℝ) (hx:x∈Ioo (-1:ℝ) 1) :
      HasDerivAt (fun x=>capP 3 (x/Real.sqrt (1-x^2)))
        (-(2/Real.pi)*Real.sqrt (1-x^2)) x := by
    have hxs : x^2<1 := by nlinarith only [hx.1,hx.2]
    have hp : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by linarith only [hxs])
    have hs' := Real.sq_sqrt (show 0≤1-x^2 by linarith only [hxs])
    have hh := (capP_deriv_three (x/Real.sqrt (1-x^2))).comp x
      ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).const_sub 1 |>.sqrt (by change 1-x^2≠0; linarith only [hxs])) hp.ne')
    rw [cap_parameter' hxs,inv_inv] at hh
    convert hh using 1 <;> first | rfl | (dsimp; field_simp; ring_nf; try simp only [hs']; ring)
  have he := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1:ℝ) 1).isPreconnected
    (fun x hx=>(hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx=>((hasDerivAt_sphereTail x).const_mul (2/Real.pi)).differentiableAt.differentiableWithinAt)
    (fun x hx=>by rw [(hd x hx).deriv,((hasDerivAt_sphereTail x).const_mul (2/Real.pi)).deriv]; ring)
    (x:=0) (by norm_num) (by rw [zero_div,capP_zero,sphereTail_zero]; field_simp; ring)
  exact he hb

end GaussianPropeller.Cap

end OAI
