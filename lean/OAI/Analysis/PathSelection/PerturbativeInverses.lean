import Mathlib
import OAI.Analysis.PathSelection.AnalyticCharts

namespace OAI

/-! Logarithmic discs, perturbative inverse sectors and zero-exponent decay. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
namespace DegeneratingTrees

 theorem AdmissibleAngularLoss.logarithmic_discs {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) (R : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ (η : ℝ → ℝ) (R' : ℝ), AdmissibleAngularLoss η ∧ R ≤ R' ∧ 1 < R' ∧
      ∀ z∈lossSector η R', closedBall z (c*‖z‖*(Real.log ‖z‖)⁻¹^2) ⊆ lossSector ω R := by
  obtain ⟨hN,hup⟩ := hω.neighboring
  let η : ℝ → ℝ := fun r => 16*(c+1)*neighboringLoss ω r
  have hη : AdmissibleAngularLoss η := hN.const_mul (by linarith)
  obtain ⟨a,t,S,hS,ha,has,ht,hsmall,hηsmall⟩ := angularLoss_kernel_data hη
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hup.and hN.1)
  obtain ⟨W,hW⟩ := eventually_atTop.mp hω.1
  let Q := Max.max (Max.max R W) 1
  let R' := Max.max (Max.max S T) (4*Q)
  have hQ : 1 ≤ Q := le_max_right _ _
  have hRQ : R ≤ Q := (le_max_left R W).trans (le_max_left _ _)
  have hWQ : W ≤ Q := (le_max_right R W).trans (le_max_left _ _)
  have hRR : R ≤ R' := by
    have hh := le_max_right (Max.max S T) (4*Q)
    dsimp [R']; linarith
  have hR1 : 1 < R' := by
    have hh := le_max_right (Max.max S T) (4*Q)
    dsimp [R']; linarith
  refine ⟨η,R',hη,hRR,hR1,?_⟩
  intro z hz w hw
  have hrS : S < ‖z‖ := lt_of_le_of_lt ((le_max_left S T).trans (le_max_left _ _)) hz.1
  have hrT : T < ‖z‖ := lt_of_le_of_lt ((le_max_right S T).trans (le_max_left _ _)) hz.1
  have hrQ : 4*Q < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz.1
  have hr0 : 0 < ‖z‖ := by linarith
  let N := neighboringLoss ω ‖z‖
  let X := ‖z‖*N
  have hNpos : 0 < N := (hT _ hrT.le).2.1
  have hX : 0 < X := mul_pos hr0 hNpos
  have hbase : (Real.log ‖z‖)⁻¹^2 ≤ N := (hT _ hrT.le).2.2
  have hηb : 16*(c+1)*N ≤ 1/64 := (hηsmall _ hrS.le).2.1
  have hcn : c*N ≤ 1/4 := by nlinarith
  have hd : ‖w-z‖ ≤ c*X := by
    have hh := (mem_closedBall_iff_norm.mp hw).trans
      (mul_le_mul_of_nonneg_left hbase (mul_nonneg hc hr0.le))
    change ‖w-z‖ ≤ c*(‖z‖*N)
    nlinarith
  have hd' : ‖w-z‖ ≤ ‖z‖/4 := by
    have hh := mul_le_mul_of_nonneg_right hcn hr0.le
    change ‖w-z‖ ≤ c*(‖z‖*N) at hd
    nlinarith
  have hwl : ‖z‖-‖z‖/4 ≤ ‖w‖ := by
    have hh := norm_sub_le w (w-z)
    rw [sub_sub_cancel] at hh
    linarith
  have hwu : ‖w‖ ≤ ‖z‖+‖z‖/4 := by
    have hh := norm_add_le (w-z) z
    rw [sub_add_cancel] at hh
    linarith
  have hwQ : Q < ‖w‖ := by linarith
  have hωw : ω ‖w‖ ≤ N := (hT _ hrT.le).1 _ ⟨by linarith,by linarith⟩
  have hωpos : 0 < ω ‖w‖ := (hW _ (hWQ.trans hwQ.le)).1
  have hηπ : η ‖z‖ ≤ Real.pi/2 := by
    have hh := (hηsmall _ hrS.le).2.1
    linarith [Real.pi_gt_three]
  have hre := half_loss_norm_le_re (hηsmall _ hrS.le).1.le hηπ hz.2
  have hre' := (abs_le.mp ((abs_re_le_norm (w-z)).trans hd)).1
  simp only [Complex.sub_re] at hre'
  have hh : ω ‖w‖*‖w‖ ≤ 2*X := by
    have hh₁ := mul_le_mul_of_nonneg_right hωw (norm_nonneg w)
    have hh₂ := mul_le_mul_of_nonneg_left (show ‖w‖ ≤ 2*‖z‖ by linarith) hNpos.le
    change ω ‖w‖*‖w‖ ≤ 2*(‖z‖*N)
    nlinarith
  refine ⟨hRQ.trans_lt hwQ,arg_lt_of_re_lower hωpos (norm_pos_iff.mp (by linarith)) ?_⟩
  have hreX : 8*(c+1)*X ≤ z.re := by
    dsimp [η,X,N] at *
    nlinarith [hre]
  have hcX := mul_nonneg hc hX.le
  nlinarith

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees.Clock

def logarithmicRadius (r : ℝ) : ℝ := r*(Real.log r)⁻¹^2

lemma logarithmicRadius_pos {r : ℝ} (hr : 1 < r) : 0 < logarithmicRadius r :=
  mul_pos (zero_lt_one.trans hr) (sq_pos_of_pos (inv_pos.mpr (Real.log_pos hr)))

lemma continuousOn_logarithmicRadius : ContinuousOn logarithmicRadius (Ioi 1) := by
  intro r hr
  have hr' : 1 < r := hr
  exact (continuousAt_id.mul (((Real.continuousAt_log (by linarith : r≠0)).inv₀
    (Real.log_pos hr).ne').pow 2)).continuousWithinAt

lemma logarithmicRadius_neighbor {a b : ℝ} (ha : 4 ≤ a)
    (hb : a/2 ≤ b) (hb' : b ≤ 2*a) :
    logarithmicRadius b ≤ 8*logarithmicRadius a := by
  have ha0 : 0 < a := by linarith
  have hb1 : 1 < b := by linarith
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hab : a ≤ b^2 := by nlinarith
  have hl : Real.log a ≤ 2*Real.log b := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log ha0 hab
  have hsq : (Real.log a)^2 ≤ 4*(Real.log b)^2 := by nlinarith
  have hh₁ := mul_le_mul_of_nonneg_left hsq hb0.le
  have hh₂ := mul_le_mul_of_nonneg_right hb' (sq_nonneg (Real.log b))
  have he (r : ℝ) : logarithmicRadius r=r/(Real.log r)^2 := by
    simp only [logarithmicRadius,div_eq_mul_inv,inv_pow]
  rw [he b,he a]
  rw [show 8*(a/(Real.log a)^2)=(8*a)/(Real.log a)^2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hlb) (sq_pos_of_pos hla)).mpr
  nlinarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 theorem sector_perturbative_inverse_unique {f : ℂ → ℂ}
    (hf : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ f z)
    (he : (fun z => f z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖))
    (ω : ℝ → ℝ) (R : ℝ) (hω : AdmissibleAngularLoss ω) :
    ∃ (η : ℝ → ℝ) (T : ℝ) (g : ℂ → ℂ),AdmissibleAngularLoss η ∧
      AnalyticOnNhd ℂ g (lossSector η T) ∧
      (∀ z∈lossSector η T,g z∈lossSector ω R ∧ f (g z)=z ∧ ‖g z-z‖ ≤ 2*‖f z-z‖ ∧
        ‖g z-z‖ ≤ logarithmicRadius ‖z‖/2) ∧
      (∀ z∈lossSector η T,∀ u∈ball z (logarithmicRadius ‖z‖),f u=z → g z=u) := by
  have hbase : ∀ᶠ z in sectorInfinity,(Real.log ‖z‖)⁻¹^2 ≤ (1/4:ℝ) := by
    have hh := admissible_baseLoss.tendsto_zero.eventually
      (eventually_le_nhds (show (0:ℝ) < 1/4 by norm_num))
    exact tendsto_norm_sectorInfinity.eventually hh
  have htarget : ∀ᶠ z in sectorInfinity,z∈lossSector ω R := ⟨ω,R,hω,fun _ h => h⟩
  obtain ⟨θ,S,hθ,hdata⟩ := hf.and ((he.bound (by norm_num : (0:ℝ) < 1/32)).and
    (hbase.and ((tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (4:ℝ))).and htarget)))
  obtain ⟨κ,U,hκ,hSU,hU1,hdisc⟩ := hθ.logarithmic_discs S (show (0:ℝ) ≤ 2 by norm_num)
  let V := interior (lossSector κ U)
  let r : ℂ → ℝ := fun z => logarithmicRadius ‖z‖
  have hV : IsOpen V := isOpen_interior
  have hVU : V ⊆ lossSector κ U := interior_subset
  have hrpos (w : ℂ) (hw : w∈V) : 0 < r w :=
    logarithmicRadius_pos (hU1.trans (hVU hw).1)
  have hr : ContinuousOn r V := by
    apply continuousOn_logarithmicRadius.comp continuous_norm.continuousOn
    exact fun w hw => hU1.trans (hVU hw).1
  have hdouble (w : ℂ) (hw : w∈V) : closedBall w (2*r w) ⊆ lossSector θ S := by
    convert hdisc w (hVU hw) using 1
    dsimp [r,logarithmicRadius]; ring_nf
  have hfa : AnalyticOnNhd ℂ f (lossSector θ S) := fun z hz => (hdata z hz).1
  have herr (w : ℂ) (hw : w∈V) (z : ℂ) (hz : z∈closedBall w (2*r w)) :
      ‖f z-z‖ ≤ r w/4 := by
    have hwS := hdouble w hw (mem_closedBall_self (by linarith [hrpos w hw]))
    have hwdata := hdata w hwS
    have hzdata := hdata z (hdouble w hw hz)
    have hdist : ‖z-w‖ ≤ 2*r w := mem_closedBall_iff_norm.mp hz
    have hrbound : 2*r w ≤ ‖w‖/2 := by
      have hh := mul_le_mul_of_nonneg_left hwdata.2.2.1 (norm_nonneg w)
      dsimp [r,logarithmicRadius]; nlinarith
    have hzl : ‖w‖/2 ≤ ‖z‖ := by
      have hh := norm_sub_le z (z-w)
      rw [sub_sub_cancel] at hh
      linarith
    have hzu : ‖z‖ ≤ 2*‖w‖ := by
      have hh := norm_add_le (z-w) w
      rw [sub_add_cancel] at hh
      linarith [norm_nonneg w]
    have hrz := logarithmicRadius_neighbor hwdata.2.2.2.1.le hzl hzu
    have hzpos := logarithmicRadius_pos (show 1 < ‖z‖ by linarith [hzdata.2.2.2.1])
    have hez : ‖f z-z‖ ≤ (1/32:ℝ)*logarithmicRadius ‖z‖ := by
      simpa only [Real.norm_eq_abs,abs_of_pos hzpos] using hzdata.2.1
    dsimp [r]
    linarith
  obtain ⟨g,hga,hg,hunique⟩ := analytic_inverse_of_disc_error hV r hr hrpos hdouble hfa herr
  obtain ⟨η,T,hη,hUT,hunit⟩ := hκ.narrow_discs U
  have hVη : lossSector η T ⊆ V := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Metric.closedBall_mem_nhds z zero_lt_one) (hunit z hz)
  refine ⟨η,T,g,hη,hga.mono hVη,?_,fun z hz => hunique z (hVη hz)⟩
  intro z hz
  obtain ⟨hgS,hgz,hgb⟩ := hg z (hVη hz)
  refine ⟨(hdata (g z) hgS).2.2.2.2,hgz,hgb,?_⟩
  have hh := herr z (hVη hz) z (mem_closedBall_self (by linarith [hrpos z (hVη hz)]))
  change ‖g z-z‖ ≤ r z/2
  linarith

 theorem sector_perturbative_inverse {f : ℂ → ℂ}
    (hf : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ f z)
    (he : (fun z => f z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖))
    (ω : ℝ → ℝ) (R : ℝ) (hω : AdmissibleAngularLoss ω) :
    ∃ (η : ℝ → ℝ) (T : ℝ) (g : ℂ → ℂ),AdmissibleAngularLoss η ∧
      AnalyticOnNhd ℂ g (lossSector η T) ∧
      (∀ z∈lossSector η T,g z∈lossSector ω R ∧ f (g z)=z ∧ ‖g z-z‖ ≤ 2*‖f z-z‖) := by
  obtain ⟨η,T,g,hη,hga,hg,hu⟩ := sector_perturbative_inverse_unique hf he ω R hω
  exact ⟨η,T,g,hη,hga,fun z hz => ⟨(hg z hz).1,(hg z hz).2.1,(hg z hz).2.2.1⟩⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma exp_logsquare_decay_bound {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop,0 ≤ Real.exp (-c*x/(Real.log x)^2)*x^N ∧
      Real.exp (-c*x/(Real.log x)^2)*x^N ≤ 1/x := by
  have hε : 0 < c/((N:ℝ)+1) := by positivity
  have hh := (isLittleO_log_rpow_rpow_atTop (s := 1) 3 zero_lt_one).bound hε
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hb : (Real.log x)^3 ≤ c/((N:ℝ)+1)*x := by
    have hh : |(Real.log x)^3| ≤ c/((N:ℝ)+1)*x := by
      norm_num [Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs,abs_of_pos hx0] at hx ⊢
      exact hx
    exact (le_abs_self _).trans hh
  have hb' : ((N:ℝ)+1)*Real.log x ≤ c*x/(Real.log x)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hh := (le_div_iff₀ (show 0 < (N:ℝ)+1 by positivity)).mp
      (show (Real.log x)^3 ≤ c*x/((N:ℝ)+1) by convert hb using 1; ring)
    nlinarith
  refine ⟨by positivity,?_⟩
  calc
    Real.exp (-c*x/(Real.log x)^2)*x^N =
        Real.exp (-c*x/(Real.log x)^2+(N:ℝ)*Real.log x) := by
      rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log hx0]
    _ ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by
      have he : -c*x/(Real.log x)^2 = -(c*x/(Real.log x)^2) := by ring
      rw [he]
      nlinarith)
    _ = 1/x := by rw [Real.exp_neg,Real.exp_log hx0,one_div]

lemma tendsto_exp_logsquare_mul_pow {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun x : ℝ => Real.exp (-c*x/(Real.log x)^2)*x^N) atTop (𝓝 0) := by
  apply squeeze_zero' (exp_logsquare_decay_bound hc N |>.mono fun _ h => h.1)
    (exp_logsquare_decay_bound hc N |>.mono fun _ h => h.2)
  convert (tendsto_inv_atTop_zero : Tendsto (fun x:ℝ => x⁻¹) atTop (𝓝 0)) using 1
  ext x
  simp only [one_div]

 

theorem exp_logsquare_mul_smaller_pow {α : Type*} {l : Filter α}
    {X w : α → ℝ} (hX : Tendsto X l atTop) (hw : w =o[l] X)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun t => Real.exp (-c*X t/(Real.log (X t))^2)*(w t)^N) l (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t => Real.exp (-c*X t/(Real.log (X t))^2)*(X t)^N)
  · filter_upwards [hw.bound zero_lt_one,hX.eventually (eventually_gt_atTop (0:ℝ))] with t ht hXt
    have ha : |w t| ≤ X t := by simpa only [Real.norm_eq_abs,abs_of_pos hXt,one_mul] using ht
    simpa only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ha N) (Real.exp_nonneg _)
  · exact (tendsto_exp_logsquare_mul_pow hc N).comp hX

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma logarithmicRadius_comparable {C a b : ℝ} (hC : 1 ≤ C) (ha : 1 < a)
    (haC : C ≤ a) (hb : 1 < b) (hl : a/C ≤ b) (hu : b ≤ C*a) :
    logarithmicRadius a ≤ 4*C*logarithmicRadius b := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hupper : b ≤ a^2 := hu.trans (by nlinarith)
  have hlog : Real.log b ≤ 2*Real.log a := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hb0 hupper
  have hsq : (Real.log b)^2 ≤ 4*(Real.log a)^2 := by nlinarith
  have hl' : a ≤ b*C := (div_le_iff₀ hC0).mp hl
  have he (t : ℝ) : logarithmicRadius t=t/(Real.log t)^2 := by
    simp only [logarithmicRadius,div_eq_mul_inv,inv_pow]
  rw [he a,he b,show 4*C*(b/(Real.log b)^2)=(4*C*b)/(Real.log b)^2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hla) (sq_pos_of_pos hlb)).mpr
  have h1 := mul_le_mul_of_nonneg_left hsq ha0.le
  have h2 := mul_le_mul_of_nonneg_right hl' (sq_nonneg (Real.log a))
  nlinarith

lemma re_lower_logarithmicRadius {x : ℂ} {ω : ℝ → ℝ} {R : ℝ}
    (hx : x∈lossSector ω R) (hx1 : 1 < ‖x‖)
    (hω : 0 ≤ ω ‖x‖ ∧ (Real.log ‖x‖)⁻¹^2 ≤ ω ‖x‖)
    (hωπ : ω ‖x‖ ≤ Real.pi/2) : logarithmicRadius ‖x‖/2 ≤ x.re := by
  have hh := half_loss_norm_le_re hω.1 hωπ hx.2
  have hb := mul_le_mul_of_nonneg_right hω.2 (zero_lt_one.trans hx1).le
  dsimp [logarithmicRadius]
  nlinarith

 

lemma lower_chart_re_bound {x : ℂ → ℂ} {X : ℝ → ℝ} {C : ℝ}
    (hC : 1 ≤ C) (hX : Tendsto X atTop atTop)
    (hmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C ≤ ‖x z‖ ∧ ‖x z‖ ≤ C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity) :
    ∀ᶠ z in sectorInfinity,(1/(8*C))*logarithmicRadius (X ‖z‖) ≤ (x z).re := by
  have hbase : ∀ᶠ w in sectorInfinity,logarithmicRadius ‖w‖/2 ≤ w.re := by
    obtain ⟨R,hR⟩ := eventually_atTop.mp
      (admissible_baseLoss.1.and ((admissible_baseLoss.tendsto_zero.eventually
        (eventually_le_nhds (show (0:ℝ) < Real.pi/2 by linarith [Real.pi_pos]))).and
        (eventually_gt_atTop (1:ℝ))))
    refine ⟨baseLoss,R,admissible_baseLoss,?_⟩
    intro w hw
    obtain ⟨hω,hπ,hw1⟩ := hR ‖w‖ hw.1.le
    exact re_lower_logarithmicRadius hw hw1 ⟨hω.1.le,hω.2⟩ hπ
  filter_upwards [hmod,hx.eventually hbase,
    (hX.comp tendsto_norm_sectorInfinity).eventually (eventually_gt_atTop (max C 1)),
    (tendsto_norm_sectorInfinity.comp hx).eventually (eventually_gt_atTop (1:ℝ))] with z hz hb hXz hxz
  have hcomp := logarithmicRadius_comparable hC ((le_max_right _ _).trans_lt hXz)
    ((le_max_left _ _).trans hXz.le) hxz hz.1 hz.2
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  dsimp only [Function.comp_def] at hcomp
  have hh : logarithmicRadius (X ‖z‖) ≤ (x z).re*(8*C) := by
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 8*C by positivity)
    nlinarith
  have he : (1/(8*C))*logarithmicRadius (X ‖z‖)=logarithmicRadius (X ‖z‖)/(8*C) := by ring
  rw [he]
  exact (div_le_iff₀ (by positivity)).mpr hh

 

theorem zero_exponent_error_small {F x : ℂ → ℂ} {X : ℝ → ℝ} {C K ε : ℝ}
    (hC : 1 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε)
    (hX : Tendsto X atTop atTop) (hlog : Real.log =o[atTop] X)
    (hmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C ≤ ‖x z‖ ∧ ‖x z‖ ≤ C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity)
    (herr : ∀ᶠ z in sectorInfinity,‖F z-z‖ ≤ K*‖z‖*Real.exp (-ε*(x z).re)) :
    (fun z => F z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hc : 0 < ε/(8*C) := by positivity
  have hrapid := exp_logsquare_mul_smaller_pow hX hlog hc 2
  have hrapid' := ((tendsto_const_nhds (x:=K)).mul hrapid).comp tendsto_norm_sectorInfinity
  simp only [mul_zero] at hrapid'
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  have hsmall := hrapid'.eventually (eventually_le_nhds hδ)
  filter_upwards [hsmall,lower_chart_re_bound hC hX hmod hx,herr,
    tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hs hl he hz
  have hL : 0 < Real.log ‖z‖ := Real.log_pos hz
  have hrad : 0 < logarithmicRadius ‖z‖ := logarithmicRadius_pos hz
  have heexp : Real.exp (-ε*(x z).re) ≤
      Real.exp (-(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hl hε.le
    dsimp [logarithmicRadius] at hh
    rw [inv_pow] at hh
    have heq : ε*((1/(8*C))*(X ‖z‖*(Real.log (X ‖z‖)^2)⁻¹)) =
        (ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2 := by ring
    rw [heq] at hh
    have heq' : -(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2 =
        -((ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2) := by ring
    rw [heq']
    nlinarith
  have hb := mul_le_mul_of_nonneg_left heexp (mul_nonneg hK (norm_nonneg z))
  have hs' := mul_le_mul_of_nonneg_right hs hrad.le
  have hcancel : K*(Real.exp (-(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2)*
      (Real.log ‖z‖)^2)*logarithmicRadius ‖z‖ =
      K*‖z‖*Real.exp (-(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2) := by
    dsimp [logarithmicRadius]
    field_simp [hL.ne']
  dsimp only [Function.comp_def] at hs'
  rw [hcancel] at hs'
  simpa only [Real.norm_eq_abs,abs_of_pos hrad] using he.trans (hb.trans hs')

 

theorem zero_exponent_sector_inverse {F x : ℂ → ℂ} {X : ℝ → ℝ} {C K ε : ℝ}
    (hF : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (hC : 1 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε)
    (hX : Tendsto X atTop atTop) (hlog : Real.log =o[atTop] X)
    (hmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C ≤ ‖x z‖ ∧ ‖x z‖ ≤ C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity)
    (herr : ∀ᶠ z in sectorInfinity,‖F z-z‖ ≤ K*‖z‖*Real.exp (-ε*(x z).re))
    (ω : ℝ → ℝ) (R : ℝ) (hω : AdmissibleAngularLoss ω) :
    ∃ (η : ℝ → ℝ) (T : ℝ) (g : ℂ → ℂ),AdmissibleAngularLoss η ∧
      AnalyticOnNhd ℂ g (lossSector η T) ∧
      (∀ z∈lossSector η T,g z∈lossSector ω R ∧ F (g z)=z ∧ ‖g z-z‖ ≤ 2*‖F z-z‖) :=
  sector_perturbative_inverse hF (zero_exponent_error_small hC hK hε hX hlog hmod hx herr) ω R hω

end DegeneratingTrees.Clock

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 

theorem zero_exponent_error_logpower {F x : ℂ → ℂ} {X : ℝ → ℝ} {C K ε : ℝ}
    (N : ℕ) (hC : 1 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε)
    (hX : Tendsto X atTop atTop) (hlog : Real.log =o[atTop] X)
    (hmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C ≤ ‖x z‖ ∧ ‖x z‖ ≤ C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity)
    (herr : ∀ᶠ z in sectorInfinity,‖F z-z‖ ≤ K*‖z‖*Real.exp (-ε*(x z).re)) :
    (fun z => F z-z) =o[sectorInfinity] (fun z => ‖z‖/(Real.log ‖z‖)^N) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hc : 0 < ε/(8*C) := by positivity
  have hrapid := exp_logsquare_mul_smaller_pow hX hlog hc N
  have hrapid' := ((tendsto_const_nhds (x:=K)).mul hrapid).comp tendsto_norm_sectorInfinity
  simp only [mul_zero] at hrapid'
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  have hsmall := hrapid'.eventually (eventually_le_nhds hδ)
  filter_upwards [hsmall,lower_chart_re_bound hC hX hmod hx,herr,
    tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hs hl he hz
  have hL : 0 < Real.log ‖z‖ := Real.log_pos hz
  have hrad : 0 < ‖z‖/(Real.log ‖z‖)^N := by positivity
  have heexp : Real.exp (-ε*(x z).re) ≤
      Real.exp (-(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hl hε.le
    dsimp [logarithmicRadius] at hh
    rw [inv_pow] at hh
    have heq : ε*((1/(8*C))*(X ‖z‖*(Real.log (X ‖z‖)^2)⁻¹)) =
        (ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2 := by ring
    rw [heq] at hh
    have heq' : -(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2 =
        -((ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2) := by ring
    rw [heq']
    nlinarith
  have hb := mul_le_mul_of_nonneg_left heexp (mul_nonneg hK (norm_nonneg z))
  have hs' := mul_le_mul_of_nonneg_right hs hrad.le
  have hcancel : K*(Real.exp (-(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2)*
      (Real.log ‖z‖)^N)*(‖z‖/(Real.log ‖z‖)^N) =
      K*‖z‖*Real.exp (-(ε/(8*C))*X ‖z‖/(Real.log (X ‖z‖))^2) := by
    field_simp [hL.ne']
  dsimp only [Function.comp_def] at hs'
  rw [hcancel] at hs'
  simpa only [Real.norm_eq_abs,abs_of_pos hrad] using he.trans (hb.trans hs')

end DegeneratingTrees.Clock
end

end OAI
