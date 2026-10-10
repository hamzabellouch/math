import Mathlib
import OAI.Probability.SKFluctuations.ScalarCurvatureLower

namespace OAI

/-! Parametric Test Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology

 theorem derivative_secant_error {f g : ℝ → ℝ} {M r : ℝ} (hM : 0 ≤ M)
    (hd : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s t, |g s-g t| ≤ M*|s-t|) (hr : 0 < r) (s : ℝ) :
    |g s-(f (s+r)-f s)/r| ≤ M*r := by
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope f g (show s < s+r by linarith)
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => hd y)
  rw [show s+r-s = r by ring] at he
  rw [← he]
  apply (hg s c).trans
  apply mul_le_mul_of_nonneg_left _ hM
  rw [abs_of_nonpos (by linarith [hc.1] : s-c ≤ 0)]
  linarith [hc.2]

 theorem uniformCauchySeqOn_parameter_derivative {X : Type*}
    {f g : ℕ → ℝ → X → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ n s x, HasDerivAt (fun t => f n t x) (g n s x) s)
    (hg : ∀ n s t x, |g n s x-g n t x| ≤ M*|s-t|)
    (hf : ∀ s, UniformCauchySeqOn (fun n => f n s) atTop univ) (s : ℝ) :
    UniformCauchySeqOn (fun n => g n s) atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let r := ε/(8*(M+1))
  have hr : 0 < r := by dsimp [r]; positivity
  let δ := ε*r/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp (hf s) δ hδ
  obtain ⟨P,hP⟩ := Metric.uniformCauchySeqOn_iff.mp (hf (s+r)) δ hδ
  refine ⟨max N P,fun m hm n hn x _ => ?_⟩
  have hmN := (le_max_left N P).trans hm
  have hmP := (le_max_right N P).trans hm
  have hnN := (le_max_left N P).trans hn
  have hnP := (le_max_right N P).trans hn
  have h0 : |f m s x-f n s x| ≤ δ := by
    simpa only [Real.dist_eq] using (hN m hmN n hnN x (mem_univ x)).le
  have h1 : |f m (s+r) x-f n (s+r) x| ≤ δ := by
    simpa only [Real.dist_eq] using (hP m hmP n hnP x (mem_univ x)).le
  have he (k : ℕ) := derivative_secant_error hM (fun t => hd k t x)
    (fun t u => hg k t u x) hr s
  have hq : |(f m (s+r) x-f m s x)/r-(f n (s+r) x-f n s x)/r| ≤ 2*δ/r := by
    rw [← sub_div,abs_div,abs_of_pos hr]
    apply div_le_div_of_nonneg_right _ hr.le
    have hh : (f m (s+r) x-f m s x)-(f n (s+r) x-f n s x) =
        (f m (s+r) x-f n (s+r) x)-(f m s x-f n s x) := by ring
    rw [hh]
    exact (abs_sub _ _).trans (by linarith)
  have hg' : |g m s x-g n s x| ≤ 2*M*r+2*δ/r := by
    have hh := abs_sub_le (g m s x) ((f m (s+r) x-f m s x)/r) (g n s x)
    have hh' := abs_sub_le ((f m (s+r) x-f m s x)/r)
      ((f n (s+r) x-f n s x)/r) (g n s x)
    have hen := he n
    rw [abs_sub_comm (g n s x)] at hen
    linarith [he m]
  have heδ : 2*δ/r = ε/4 := by dsimp [δ]; field_simp; ring
  have her : 2*M*r < ε/4 := by
    have hm1 : 0 < M+1 := by linarith
    have ht : M/(M+1) < 1 := (div_lt_one hm1).2 (by linarith)
    have hh := mul_lt_mul_of_pos_left ht (show 0 < ε/4 by positivity)
    calc
      2*M*r = (ε/4)*(M/(M+1)) := by dsimp [r]; field_simp; ring
      _ < (ε/4)*1 := hh
      _ = ε/4 := mul_one _
  rw [Real.dist_eq]
  exact hg'.trans_lt (by rw [heδ]; linarith)

 theorem lipschitz_derivative_remainder {f g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s t, |g s-g t| ≤ M*|s-t|) (s t : ℝ) :
    |f t-f s-(t-s)*g s| ≤ M*|t-s|^2 := by
  have hline (y : ℝ) : HasDerivAt (fun z => f z-z*g s) (g y-g s) y := by
    convert (hd y).sub ((hasDerivAt_id y).mul_const (g s)) using 1 <;>
      first | rfl | simp only [one_mul]
  have hh := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hline y).hasDerivWithinAt)
    (fun y hy => show ‖g y-g s‖ ≤ M*|t-s| from by
      rw [Real.norm_eq_abs]
      apply (hg y s).trans
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only [Real.dist_eq,abs_sub_comm] using Real.dist_left_le_of_mem_uIcc hy)
    (left_mem_uIcc) (right_mem_uIcc)
  have he : (f t-t*g s)-(f s-s*g s) = f t-f s-(t-s)*g s := by ring
  rw [Real.norm_eq_abs,he,Real.norm_eq_abs] at hh
  exact hh.trans_eq (by ring)

 

 theorem hasDerivAt_limit_of_lipschitz_derivative {f g : ℕ → ℝ → ℝ}
    {F : ℝ → ℝ} {d M s : ℝ} (hM : 0 ≤ M)
    (hd : ∀ n t, HasDerivAt (f n) (g n t) t)
    (hb : ∀ n t u, |g n t-g n u| ≤ M*|t-u|)
    (hf : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (F t)))
    (hg : Tendsto (fun n => g n s) atTop (𝓝 d)) : HasDerivAt F d s := by
  have hr (t : ℝ) : |F t-F s-(t-s)*d| ≤ M*|t-s|^2 := by
    apply le_of_tendsto (((hf t).sub (hf s)).sub (hg.const_mul (t-s))).abs
    exact Eventually.of_forall fun n => lipschitz_derivative_remainder hM (hd n) (hb n) s t
  rw [hasDerivAt_iff_tendsto]
  have hlim : Tendsto (fun t : ℝ => M*|t-s|) (𝓝 s) (𝓝 0) := by
    simpa only [id_eq,sub_self,abs_zero,mul_zero] using
      ((tendsto_id.sub_const s).abs.const_mul M :
        Tendsto (fun t : ℝ => M*|t-s|) (𝓝 s) (𝓝 (M*|s-s|)))
  apply squeeze_zero (fun _ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ hlim
  intro t
  simp only [Real.norm_eq_abs,smul_eq_mul]
  apply (mul_le_mul_of_nonneg_left (hr t) (inv_nonneg.mpr (abs_nonneg (t-s)))).trans
  by_cases he : t=s
  · subst t; simp
  · have hn : |t-s| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr he)
    apply le_of_eq
    field_simp

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.evolve_time_stability {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    {m s t : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : Fin 1 → ℝ) :
    |clockContinuation m J.F t x-clockContinuation m J.F s x| ≤ |t-s|/2 := by
  have hc : ContinuousOn (fun s => (J.evolve hm s).F x) (Ici 0) :=
    ((clockContinuation_continuous J.lipschitz m).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  have hd (r : ℝ) (hr : 0 < r) := J.evolve_time_F hm hr x
  have hb (r : ℝ) (hr : 0 < r) :
      |(1/2:ℝ)*∑ i, ((J.evolve hm r).H i x+m*((J.evolve hm r).G i x)^2)| ≤ 1/2 := by
    rw [Fin.sum_univ_one]
    have hh := (hJ.evolve hm hm1 r) x
    have hsq := sq_nonneg ((J.evolve hm r).G 0 x)
    have hmsq := mul_nonneg (sub_nonneg.mpr hm1) hsq
    have hpos := mul_nonneg hm.le hsq
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (1/2:ℝ)*
      ((J.evolve hm r).H 0 x+m*((J.evolve hm r).G 0 x)^2))]
    nlinarith [hh.1,hh.2]
  have hh := abs_sub_le_mul_of_deriv_interior hc hd hb ht hs
  simpa only [HeatJet.evolve,one_div,mul_comm (2:ℝ)⁻¹,← div_eq_mul_inv,abs_sub_comm] using hh

def HeatClock.scaleTime (c : HeatClock) (r : ℝ≥0) : HeatClock :=
  ⟨c.mass,c.positive,r*c.time⟩

def scaleTimes (cs : List HeatClock) (r : ℝ≥0) : List HeatClock :=
  cs.map (fun c => c.scaleTime r)

@[simp] theorem scaleTimes_nil (r : ℝ≥0) : scaleTimes [] r = [] := rfl
@[simp] theorem scaleTimes_cons (c : HeatClock) (cs : List HeatClock) (r : ℝ≥0) :
    scaleTimes (c::cs) r = c.scaleTime r::scaleTimes cs r := rfl
@[simp] theorem scaleTimes_append (cs ds : List HeatClock) (r : ℝ≥0) :
    scaleTimes (cs++ds) r = scaleTimes cs r++scaleTimes ds r := List.map_append

theorem HeatJet.schedule_scale_time_stability {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (cs : List HeatClock) (hc : ∀ c ∈ cs, c.mass ≤ 1) (r s : ℝ≥0)
    (x : Fin 1 → ℝ) :
    |(J.schedule (scaleTimes cs r)).F x-(J.schedule (scaleTimes cs s)).F x| ≤
      |(r:ℝ)-s| *(cs.map (fun c => (c.time:ℝ))).sum/2 := by
  induction cs generalizing x with
  | nil => simp [HeatJet.schedule]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, d.mass ≤ 1 := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    let A := J.schedule (scaleTimes cs r)
    let B := J.schedule (scaleTimes cs s)
    have hB : B.ScalarAdmissible := hJ.schedule _ (by
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact hcs e he)
    have hh := clockContinuation_abs_sub_le A.lipschitz B.lipschitz c.positive
      (fun y => ih hcs y) ((r*c.time:ℝ≥0):ℝ) x
    have ht := HeatJet.evolve_time_stability hB c.positive (hc c (List.mem_cons_self ..))
      (s*c.time).coe_nonneg (r*c.time).coe_nonneg x
    have ha := (abs_sub_le (clockContinuation c.mass A.F (r*c.time) x)
      (clockContinuation c.mass B.F (r*c.time) x)
      (clockContinuation c.mass B.F (s*c.time) x)).trans (add_le_add hh ht)
    change |(J.schedule (scaleTimes (c::cs) r)).F x-(J.schedule (scaleTimes (c::cs) s)).F x| ≤ _ at ha
    apply ha.trans_eq
    simp only [NNReal.coe_mul,List.map_cons,List.sum_cons,← sub_mul,abs_mul,
      abs_of_nonneg c.time.coe_nonneg]
    ring

 
def PositiveMassProfile.affine (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) : PositiveMassProfile where
  mass s := α.mass (l+(t:ℝ)*s)
  positive _ := α.positive _
  monotone := α.monotone.comp (monotone_const.add (monotone_id.const_mul t.coe_nonneg))

theorem PositiveMassProfile.grid_affine (α : PositiveMassProfile) (b l : ℝ)
    (r t : ℝ≥0) (k : ℕ) :
    scaleTimes ((α.affine b r).grid l t k) r = α.grid (b+(r:ℝ)*l) (r*t) k := by
  induction k generalizing l t with
  | zero => rfl
  | succ k ih =>
    simp only [PositiveMassProfile.grid,scaleTimes_append,ih]
    congr 1
    · congr 1
      ring
    · congr 1
      · simp only [NNReal.coe_mul]
        ring
      · ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

def NonnegativeMassProfile.affine (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) : NonnegativeMassProfile where
  mass s := α.mass (l+(t:ℝ)*s)
  nonneg _ := α.nonneg _
  monotone := α.monotone.comp (monotone_const.add (monotone_id.const_mul t.coe_nonneg))

theorem NonnegativeMassProfile.cappedApprox_affine (α : NonnegativeMassProfile)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    (α.affine l t).cappedApprox k = (α.cappedApprox k).affine l t := rfl

def CoupledHeatClock.scaleTime (c : CoupledHeatClock) (r : ℝ≥0) : CoupledHeatClock :=
  ⟨c.first,c.second,c.first_pos,c.second_pos,r*c.time⟩

theorem coupled_scale_left (cs : List CoupledHeatClock) (r : ℝ≥0) :
    (cs.map (fun c => c.scaleTime r)).map CoupledHeatClock.left =
      scaleTimes (cs.map CoupledHeatClock.left) r := by
  simp only [List.map_map,scaleTimes]
  rfl

theorem coupled_scale_right (cs : List CoupledHeatClock) (r : ℝ≥0) :
    (cs.map (fun c => c.scaleTime r)).map CoupledHeatClock.right =
      scaleTimes (cs.map CoupledHeatClock.right) r := by
  simp only [List.map_map,scaleTimes]
  rfl

theorem coupled_scale_cost (cs : List CoupledHeatClock) (r : ℝ≥0) :
    ((cs.map (fun c => c.scaleTime r)).map CoupledHeatClock.cost).sum =
      (r:ℝ)*(cs.map CoupledHeatClock.cost).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [CoupledHeatClock.cost,CoupledHeatClock.scaleTime,NNReal.coe_mul]
    ring

theorem dyadicLowerSum_mono {f g : ℝ → ℝ} (h : ∀ s, f s ≤ g s)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) : dyadicLowerSum f l t k ≤ dyadicLowerSum g l t k := by
  induction k generalizing l t with
  | zero => exact mul_le_mul_of_nonneg_left (h l) t.coe_nonneg
  | succ k ih => exact add_le_add (ih _ _) (ih _ _)

theorem HeatJet.capped_scaled_mass_comparison {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (α β : NonnegativeMassProfile) (l : ℝ) (t r : ℝ≥0) (k : ℕ) (x : Fin 1 → ℝ) :
    |(J.schedule (scaleTimes ((α.cappedApprox k).grid l t k) r)).F x-
      (J.schedule (scaleTimes ((β.cappedApprox k).grid l t k) r)).F x| ≤
      (r:ℝ)/2*dyadicLowerSum (fun s => |α.mass s-β.mass s|) l t k := by
  have hh := J.schedule_mass_comparison (fun _ => 1) (fun i x => by fin_cases i; exact hJ.gradient x)
    (((α.cappedApprox k).pairedGrid (β.cappedApprox k) l t k).map (fun c => c.scaleTime r)) x
  rw [coupled_scale_left,coupled_scale_right,PositiveMassProfile.pairedGrid_left,
    PositiveMassProfile.pairedGrid_right,coupled_scale_cost,PositiveMassProfile.pairedGrid_cost_eq_sum] at hh
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,one_pow,add_zero] at hh
  have hc := dyadicLowerSum_mono (fun s => abs_max_sub_max_le_abs (α.mass s) (β.mass s) ((1/2:ℝ)^k)) l t k
  change dyadicLowerSum (fun s => |(α.cappedApprox k).mass s-(β.cappedApprox k).mass s|) l t k ≤ _ at hc
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hc r.coe_nonneg])

 

theorem HeatJet.profile_affine_comparison {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l b : ℝ) (t r : ℝ≥0) (x : Fin 1 → ℝ) :
    |J.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α b r x| ≤
      (t:ℝ)/2*(∫ s in (0:ℝ)..1, |α.mass (l+(t:ℝ)*s)-α.mass (b+(r:ℝ)*s)|)+
        |(t:ℝ)-r|/2 := by
  let A := α.affine l t
  let B := α.affine b r
  have hAt (k : ℕ) : scaleTimes ((A.cappedApprox k).grid 0 1 k) t = (α.cappedApprox k).grid l t k := by
    rw [NonnegativeMassProfile.cappedApprox_affine,PositiveMassProfile.grid_affine]
    simp only [mul_zero,add_zero,mul_one]
  have hBr (k : ℕ) : scaleTimes ((B.cappedApprox k).grid 0 1 k) r = (α.cappedApprox k).grid b r k := by
    rw [NonnegativeMassProfile.cappedApprox_affine,PositiveMassProfile.grid_affine]
    simp only [mul_zero,add_zero,mul_one]
  have hf (k : ℕ) :
      |(J.schedule ((α.cappedApprox k).grid l t k)).F x-
        (J.schedule ((α.cappedApprox k).grid b r k)).F x| ≤
      (t:ℝ)/2*dyadicLowerSum (fun s => |A.mass s-B.mass s|) 0 1 k+|(t:ℝ)-r|/2 := by
    have hm := HeatJet.capped_scaled_mass_comparison hJ A B 0 1 t k x
    have hc : ∀ c ∈ (B.cappedApprox k).grid 0 1 k, c.mass ≤ 1 := by
      intro c hc
      exact ((B.cappedApprox k).grid_mass_bounds 0 1 k hc).2.trans
        (B.cappedApprox_le_one (fun s => hα _) k _)
    have ht := J.schedule_scale_time_stability hJ ((B.cappedApprox k).grid 0 1 k) hc t r x
    rw [PositiveMassProfile.grid_total_time] at ht
    simp only [NNReal.coe_one,mul_one] at ht
    have h := (abs_sub_le ((J.schedule (scaleTimes ((A.cappedApprox k).grid 0 1 k) t)).F x)
      ((J.schedule (scaleTimes ((B.cappedApprox k).grid 0 1 k) t)).F x)
      ((J.schedule (scaleTimes ((B.cappedApprox k).grid 0 1 k) r)).F x))
    have hh := h.trans (add_le_add hm ht)
    rw [hAt,hBr] at hh
    exact hh
  have hL := J.capped_grid_tendsto (fun _ => 1) (fun i x => by fin_cases i; exact hJ.gradient x) α hα l t 0 x
  have hR := J.capped_grid_tendsto (fun _ => 1) (fun i x => by fin_cases i; exact hJ.gradient x) α hα b r 0 x
  simp only [Nat.add_zero] at hL hR
  have hI := monotone_abs_sub_sum_tendsto A.monotone B.monotone 0 1
  simp only [NNReal.coe_one,zero_add] at hI
  exact le_of_tendsto_of_tendsto (hL.sub hR).abs
    ((hI.const_mul ((t:ℝ)/2)).add_const (|(t:ℝ)-r|/2)) (Eventually.of_forall hf)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem monotone_shift_integral_bound {f : ℝ → ℝ} (hf : Monotone f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (a b : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ x in a..b, f (x+δ)-f (x-δ)) ≤ 2*δ := by
  have hp : Monotone (fun x => f (x+δ)) := hf.comp (monotone_id.add_const δ)
  have hm : Monotone (fun x => f (x-δ)) := hf.comp (fun _ _ h => sub_le_sub_right h δ)
  rw [intervalIntegral.integral_sub hp.intervalIntegrable hm.intervalIntegrable,
    intervalIntegral.integral_comp_add_right]
  simp_rw [sub_eq_add_neg (b:=δ)]
  rw [intervalIntegral.integral_comp_add_right]
  have he := intervalIntegral.integral_interval_sub_interval_comm' (μ:=volume)
    (hf.intervalIntegrable (a:=a+δ) (b:=b+δ)) (hf.intervalIntegrable (a:=a+-δ) (b:=b+-δ))
    (hf.intervalIntegrable (a:=a+δ) (b:=a+-δ))
  rw [he]
  have hlo := intervalIntegral.integral_nonneg_of_forall (μ:=volume) (a:=a+-δ) (b:=a+δ) (by linarith) h0
  have hhi := intervalIntegral.integral_mono_on (μ:=volume) (a:=b+-δ) (b:=b+δ) (by linarith)
    hf.intervalIntegrable (intervalIntegrable_const (c:=(1:ℝ))) (fun x _ => h1 x)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hhi
  linarith

theorem monotone_affine_l1_bound {f : ℝ → ℝ} (hf : Monotone f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (a b t r : ℝ)
    (ht : 0 ≤ t) (hr : 0 ≤ r) :
    t*(∫ s in (0:ℝ)..1, |f (a+t*s)-f (b+r*s)|) ≤
      2*(|a-b|+|t-r|) := by
  let δ := |a-b|+|t-r|
  have hδ : 0 ≤ δ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hp : Monotone (fun s => f (a+t*s+δ)) :=
    hf.comp ((monotone_const.add (monotone_id.const_mul ht)).add_const δ)
  have hm : Monotone (fun s => f (a+t*s-δ)) :=
    hf.comp (fun _ _ h => by linarith [mul_le_mul_of_nonneg_left h ht])
  have ha : Monotone (fun s => f (a+t*s)) := hf.comp (monotone_const.add (monotone_id.const_mul ht))
  have hb : Monotone (fun s => f (b+r*s)) := hf.comp (monotone_const.add (monotone_id.const_mul hr))
  have hpt (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      |f (a+t*s)-f (b+r*s)| ≤ f (a+t*s+δ)-f (a+t*s-δ) := by
    have hd : |(a+t*s)-(b+r*s)| ≤ δ := by
      calc
        |(a+t*s)-(b+r*s)| = |(a-b)+(t-r)*s| := by congr 1; ring
        _ ≤ |a-b|+|(t-r)*s| := abs_add_le _ _
        _ = |a-b|+|t-r| *s := by rw [abs_mul,abs_of_nonneg hs.1]
        _ ≤ δ := by dsimp [δ]; nlinarith [abs_nonneg (t-r),hs.2]
    have hda := (abs_le.mp hd).1
    have hdb := (abs_le.mp hd).2
    have ha0 := hf (show a+t*s-δ ≤ a+t*s by linarith)
    have ha1 := hf (show a+t*s ≤ a+t*s+δ by linarith)
    have hb0 := hf (show a+t*s-δ ≤ b+r*s by linarith)
    have hb1 := hf (show b+r*s ≤ a+t*s+δ by linarith)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) zero_le_one
    (ha.intervalIntegrable.sub hb.intervalIntegrable).abs
    (hp.intervalIntegrable.sub hm.intervalIntegrable) hpt
  have hc := intervalIntegral.smul_integral_comp_add_mul
    (f:=fun x => f (x+δ)-f (x-δ)) (a:=(0:ℝ)) (b:=1) t a
  simp only [smul_eq_mul,mul_zero,add_zero,mul_one] at hc
  calc
    t*(∫ s in (0:ℝ)..1, |f (a+t*s)-f (b+r*s)|) ≤
        t*(∫ s in (0:ℝ)..1, f (a+t*s+δ)-f (a+t*s-δ)) := mul_le_mul_of_nonneg_left hi ht
    _ = ∫ x in a..a+t, f (x+δ)-f (x-δ) := hc
    _ ≤ 2*δ := monotone_shift_integral_bound hf h0 h1 a (a+t) hδ

 
theorem HeatJet.profile_window_stability {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l b : ℝ) (t r : ℝ≥0) (x : Fin 1 → ℝ) :
    |J.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue α b r x| ≤
      |l-b|+(3/2:ℝ)*|(t:ℝ)-r| := by
  have hh := HeatJet.profile_affine_comparison hJ α hα l b t r x
  have hi := monotone_affine_l1_bound α.monotone α.nonneg hα l b t r t.coe_nonneg r.coe_nonneg
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

def PositiveMassProfile.linearGrid (α : PositiveMassProfile) (l : ℝ) (h : ℝ≥0) : ℕ → List HeatClock
  | 0 => []
  | N+1 => ⟨α.mass l,α.positive l,h⟩ :: α.linearGrid (l+h) h N

theorem PositiveMassProfile.linearGrid_add (α : PositiveMassProfile) (l : ℝ) (h : ℝ≥0) (N M : ℕ) :
    α.linearGrid l h (N+M) = α.linearGrid l h N ++ α.linearGrid (l+(N:ℝ)*h) h M := by
  induction N generalizing l with
  | zero => simp [PositiveMassProfile.linearGrid]
  | succ N ih =>
    simp only [Nat.succ_add,PositiveMassProfile.linearGrid,List.cons_append,ih]
    congr 2
    congr 1
    push_cast
    ring

def HeatClock.pieces (c : HeatClock) (h : ℝ≥0) (M : ℕ) : List HeatClock :=
  List.replicate M ⟨c.mass,c.positive,h⟩

theorem HeatJet.schedule_replicate {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    (h : ℝ≥0) (M : ℕ) :
    (J.schedule (List.replicate M (⟨m,hm,h⟩:HeatClock))).F = clockContinuation m J.F ((M:ℝ)*h) := by
  induction M with
  | zero =>
    simp only [List.replicate_zero,HeatJet.schedule,Nat.cast_zero,zero_mul]
    exact (funext (clockContinuation_zero hm.ne')).symm
  | succ M ih =>
    simp only [List.replicate_succ,HeatJet.schedule,HeatJet.evolve]
    rw [ih]
    funext x
    rw [clockContinuation_add J.lipschitz hm.ne' h.coe_nonneg (by positivity)]
    congr 1
    push_cast
    ring

 
def PositiveMassProfile.linearCoupled (α : PositiveMassProfile) (a : ℝ) (ha : 0 < a)
    (l : ℝ) (h : ℝ≥0) : ℕ → List CoupledHeatClock
  | 0 => []
  | M+1 => ⟨a,α.mass l,ha,α.positive l,h⟩ :: α.linearCoupled a ha (l+h) h M

theorem PositiveMassProfile.linearCoupled_left (α : PositiveMassProfile) (a : ℝ) (ha : 0 < a)
    (l : ℝ) (h : ℝ≥0) (M : ℕ) :
    (α.linearCoupled a ha l h M).map CoupledHeatClock.left = List.replicate M ⟨a,ha,h⟩ := by
  induction M generalizing l with
  | zero => rfl
  | succ M ih => simp only [PositiveMassProfile.linearCoupled,List.map_cons,ih,List.replicate_succ]; rfl

theorem PositiveMassProfile.linearCoupled_right (α : PositiveMassProfile) (a : ℝ) (ha : 0 < a)
    (l : ℝ) (h : ℝ≥0) (M : ℕ) :
    (α.linearCoupled a ha l h M).map CoupledHeatClock.right = α.linearGrid l h M := by
  induction M generalizing l with
  | zero => rfl
  | succ M ih => simp only [PositiveMassProfile.linearCoupled,PositiveMassProfile.linearGrid,List.map_cons,ih]; rfl

theorem PositiveMassProfile.linearCoupled_cost (α : PositiveMassProfile) (a : ℝ) (ha : 0 < a)
    (l : ℝ) (h : ℝ≥0) (M : ℕ) {B : ℝ}
    (hlo : a ≤ α.mass l) (hhi : α.mass (l+(M:ℝ)*h) ≤ B) :
    ((α.linearCoupled a ha l h M).map CoupledHeatClock.cost).sum ≤ (M:ℝ)*h*(B-a) := by
  induction M generalizing l with
  | zero => simp [PositiveMassProfile.linearCoupled]
  | succ M ih =>
    have he : l+h+(M:ℝ)*h = l+((M+1:ℕ):ℝ)*h := by push_cast; ring
    have hl1 : a ≤ α.mass (l+h) := hlo.trans (α.monotone (by linarith [h.coe_nonneg]))
    have hlB : α.mass l ≤ B := (α.monotone (by nlinarith [h.coe_nonneg] : l ≤ l+((M+1:ℕ):ℝ)*h)).trans hhi
    have hh := ih (l+h) hl1 (he ▸ hhi)
    simp only [PositiveMassProfile.linearCoupled,List.map_cons,List.sum_cons,CoupledHeatClock.cost]
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    have hc := mul_le_mul_of_nonneg_right (show -(a-α.mass l) ≤ B-a by linarith) h.coe_nonneg
    push_cast
    nlinarith

 

theorem HeatJet.linear_block_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : PositiveMassProfile)
    (l : ℝ) (h : ℝ≥0) (M : ℕ) (x : Fin (n+1) → ℝ) :
    |clockContinuation (α.mass l) J.F ((M:ℝ)*h) x-(J.schedule (α.linearGrid l h M)).F x| ≤
      (∑ i, (D i)^2)/2*((M:ℝ)*h)*(α.mass (l+(M:ℝ)*h)-α.mass l) := by
  have hh := J.schedule_mass_comparison D hD (α.linearCoupled (α.mass l) (α.positive l) l h M) x
  rw [α.linearCoupled_left,α.linearCoupled_right,J.schedule_replicate] at hh
  have hc := α.linearCoupled_cost (α.mass l) (α.positive l) l h M
    le_rfl le_rfl
  have hC : 0 ≤ (∑ i, (D i)^2)/2 := by positivity
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hc hC])

 
theorem HeatJet.linear_refinement_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : PositiveMassProfile)
    (l : ℝ) (h : ℝ≥0) (N M : ℕ) (x : Fin (n+1) → ℝ) :
    |(J.schedule (α.linearGrid l ((M:ℝ≥0)*h) N)).F x-
      (J.schedule (α.linearGrid l h (N*M))).F x| ≤
      (∑ i, (D i)^2)/2*((M:ℝ)*h)*(α.mass (l+((N*M:ℕ):ℝ)*h)-α.mass l) := by
  induction N generalizing l x with
  | zero => simp [PositiveMassProfile.linearGrid,HeatJet.schedule]
  | succ N ih =>
    have he : l+(M:ℝ)*h+(N*M:ℕ)*h = l+((N+1)*M:ℕ)*h := by
      push_cast
      ring
    have hn : (N+1)*M = M+N*M := by ring
    have hg : α.linearGrid l h ((N+1)*M) =
        α.linearGrid l h M ++ α.linearGrid (l+(M:ℝ)*h) h (N*M) := by rw [hn,α.linearGrid_add]
    rw [hg]
    simp only [PositiveMassProfile.linearGrid]
    rw [J.schedule_append]
    let A := J.schedule (α.linearGrid (l+((M:ℝ≥0)*h:ℝ≥0)) ((M:ℝ≥0)*h) N)
    let B := J.schedule (α.linearGrid (l+(M:ℝ)*h) h (N*M))
    have hAB : ∀ y, |A.F y-B.F y| ≤
        (∑ i,(D i)^2)/2*((M:ℝ)*h)*(α.mass (l+((N+1)*M:ℕ)*h)-α.mass (l+(M:ℝ)*h)) := by
      intro y
      have hh := ih (l+(M:ℝ)*h) y
      simpa only [A,B,NNReal.coe_mul,NNReal.coe_natCast,he] using hh
    have hc := clockContinuation_abs_sub_le A.lipschitz B.lipschitz (α.positive l) hAB
      ((M:ℝ)*h) x
    have hb := B.linear_block_comparison D (J.schedule_gradient_bound D hD _) α l h M x
    have ht := (abs_sub_le (clockContinuation (α.mass l) A.F ((M:ℝ)*h) x)
      (clockContinuation (α.mass l) B.F ((M:ℝ)*h) x)
      ((B.schedule (α.linearGrid l h M)).F x)).trans (add_le_add hc hb)
    apply ht.trans_eq
    ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem PositiveMassProfile.grid_eq_linear (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    α.grid l t k = α.linearGrid l (t/(2^k:ℝ≥0)) (2^k) := by
  induction k generalizing l t with
  | zero => simp [PositiveMassProfile.grid,PositiveMassProfile.linearGrid]
  | succ k ih =>
    have hp : (2:ℝ≥0)^k ≠ 0 := by positivity
    have he : t/2/(2^k:ℝ≥0) = t/(2^(k+1):ℝ≥0) := by rw [pow_succ]; ring
    have hn : (2:ℕ)^(k+1) = 2^k+2^k := by rw [pow_succ]; omega
    have hl : l+((2^k:ℕ):ℝ)*((t:ℝ)/(2:ℝ)^(k+1)) = l+(t:ℝ)/2 := by
      simp only [Nat.cast_pow,Nat.cast_ofNat,pow_succ]
      field_simp
    rw [PositiveMassProfile.grid,ih,ih,he,hn,α.linearGrid_add]
    simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,hl]

theorem HeatJet.linear_grid_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : PositiveMassProfile)
    (l : ℝ) (h : ℝ≥0) (N : ℕ) (x : Fin (n+1) → ℝ) :
    |(J.schedule (α.linearGrid l h N)).F x-J.profileValue α l ((N:ℝ≥0)*h) x| ≤
      (∑ i,(D i)^2)/2*h*(α.mass (l+(N:ℝ)*h)-α.mass l) := by
  let C := (∑ i,(D i)^2)/2
  let V := α.mass (l+(N:ℝ)*h)-α.mass l
  have hf (k : ℕ) :
      |(J.schedule (α.linearGrid l h N)).F x-(J.schedule (α.grid l ((N:ℝ≥0)*h) k)).F x| ≤
        C*((h:ℝ)+(N:ℝ)*h/(2:ℝ)^k)*V := by
    have hp : (2:ℝ≥0)^k ≠ 0 := by positivity
    have ha := J.linear_refinement_comparison D hD α l (h/(2^k:ℝ≥0)) N (2^k) x
    have hb := J.linear_refinement_comparison D hD α l (h/(2^k:ℝ≥0)) (2^k) N x
    have htime : ((2^k:ℕ):ℝ≥0)*(h/(2^k:ℝ≥0)) = h := by
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    have htimeB : (N:ℝ≥0)*(h/(2^k:ℝ≥0)) = ((N:ℝ≥0)*h)/(2^k:ℝ≥0) := by ring
    have hend : l+((N*2^k:ℕ):ℝ)*((h:ℝ)/(2:ℝ)^k) = l+(N:ℝ)*h := by
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    have hendB : l+((2^k*N:ℕ):ℝ)*((h:ℝ)/(2:ℝ)^k) = l+(N:ℝ)*h := by
      rw [Nat.mul_comm (2^k) N]
      exact hend
    rw [htime] at ha
    rw [htimeB] at hb
    simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat] at ha hb
    rw [hend] at ha
    rw [hendB,Nat.mul_comm (2^k) N] at hb
    rw [α.grid_eq_linear]
    have ht := (abs_sub_le ((J.schedule (α.linearGrid l h N)).F x)
      ((J.schedule (α.linearGrid l (h/(2^k:ℝ≥0)) (N*2^k))).F x)
      ((J.schedule (α.linearGrid l (((N:ℝ≥0)*h)/(2^k:ℝ≥0)) (2^k))).F x)).trans
      (add_le_add ha (by simpa only [abs_sub_comm] using hb))
    apply ht.trans_eq
    dsimp [C,V]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hR : Tendsto (fun k : ℕ => C*((h:ℝ)+(N:ℝ)*h/(2:ℝ)^k)*V) atTop (𝓝 (C*h*V)) := by
    have he (k : ℕ) : (N:ℝ)*h/(2:ℝ)^k = (N:ℝ)*h*(1/2:ℝ)^k := by rw [div_pow]; simp [div_eq_mul_inv]
    simp_rw [he]
    simpa only [mul_zero,add_zero] using ((hp.const_mul ((N:ℝ)*h)).const_add (h:ℝ) |>.const_mul C).mul_const V
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub (J.grid_tendsto α l ((N:ℝ≥0)*h) x)).abs hR (Eventually.of_forall hf)

theorem HeatJet.capped_linear_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (k : ℕ) (l : ℝ) (h : ℝ≥0) (N : ℕ) (x : Fin (n+1) → ℝ) :
    |(J.schedule ((α.cappedApprox k).linearGrid l h N)).F x-
      J.nonnegativeProfileValue α l ((N:ℝ≥0)*h) x| ≤
      (∑ i,(D i)^2)/2*((h:ℝ)+(N:ℝ)*h*(1/2:ℝ)^k) := by
  have hg := J.linear_grid_error D hD (α.cappedApprox k) l h N x
  have hp := J.capped_profile_error D hD α k l ((N:ℝ≥0)*h) x
  have hv : (α.cappedApprox k).mass (l+(N:ℝ)*h)-(α.cappedApprox k).mass l ≤ 1 := by
    linarith [α.cappedApprox_le_one hα k (l+(N:ℝ)*h),(α.cappedApprox k).positive l]
  have h0 : 0 ≤ (∑ i,(D i)^2)/2*(h:ℝ) := by positivity
  have hh := (abs_sub_le ((J.schedule ((α.cappedApprox k).linearGrid l h N)).F x)
    (J.profileValue (α.cappedApprox k) l ((N:ℝ≥0)*h) x)
    (J.nonnegativeProfileValue α l ((N:ℝ≥0)*h) x)).trans (add_le_add hg hp)
  simp only [NNReal.coe_mul,NNReal.coe_natCast] at hh
  nlinarith [mul_le_mul_of_nonneg_left hv h0]

 

theorem HeatJet.multiple_grid_tendsto {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (h : ℝ≥0) (N : ℕ) (x : Fin (n+1) → ℝ) :
    Tendsto (fun k => (J.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) (N*2^k))).F x)
      atTop (𝓝 (J.nonnegativeProfileValue α l ((N:ℝ≥0)*h) x)) := by
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb (k : ℕ) :
      dist ((J.schedule ((α.cappedApprox k).linearGrid l (h/(2^k:ℝ≥0)) (N*2^k))).F x)
        (J.nonnegativeProfileValue α l ((N:ℝ≥0)*h) x) ≤
      (∑ i,(D i)^2)/2*((h:ℝ)+(N:ℝ)*h)*(1/2:ℝ)^k := by
    have he : ((N*2^k:ℕ):ℝ≥0)*(h/(2^k:ℝ≥0)) = (N:ℝ≥0)*h := by
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    have hh := J.capped_linear_error D hD α hα k l (h/(2^k:ℝ≥0)) (N*2^k) x
    rw [he] at hh
    rw [Real.dist_eq]
    apply hh.trans_eq
    simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,div_pow,one_pow]
    field_simp
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) hb (by
    simpa only [mul_zero] using hp.const_mul ((∑ i,(D i)^2)/2*((h:ℝ)+(N:ℝ)*h)))

end SKFluctuations.Hierarchy

end

end OAI
