import Mathlib
import OAI.Analysis.PathSelection.RealInverses

namespace OAI

/-! Relative perturbation errors, modulus estimates and zero-exponent charts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma tendsto_sectorInfinity_of_close_map {G F : ℂ → ℂ} {C : ℝ}
    (hC : 0≤C) (hG : Tendsto G sectorInfinity sectorInfinity)
    (he : ∀ᶠ z in sectorInfinity,‖F z-G z‖≤C*logarithmicRadius ‖G z‖) :
    Tendsto F sectorInfinity sectorInfinity := by
  apply Filter.tendsto_def.mpr
  intro S hS
  obtain ⟨ω,R,hω,hS⟩ := hS
  obtain ⟨η,T,hη,hRT,hT1,hdisc⟩ := hω.logarithmic_discs R hC
  have hdom : ∀ᶠ w in sectorInfinity,w∈lossSector η T := ⟨η,T,hη,fun _ h => h⟩
  filter_upwards [hG.eventually hdom,he] with z hz hez
  apply hS (F z)
  apply hdisc (G z) hz
  apply mem_closedBall_iff_norm.mpr
  simpa only [logarithmicRadius,mul_assoc] using hez

lemma baseLoss_le_of_upper {r s C : ℝ} (hr : 1<r) (hs : 1<s)
    (hC : C≤r) (hupper : s≤C*r) : baseLoss r≤4*baseLoss s := by
  have hr0 : 0<r := zero_lt_one.trans hr
  have hs0 : 0<s := zero_lt_one.trans hs
  have hlogr : 0<Real.log r := Real.log_pos hr
  have hlogs : 0<Real.log s := Real.log_pos hs
  have hsr : s≤r^2 := hupper.trans (by nlinarith)
  have hlog : Real.log s≤2*Real.log r := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hs0 hsr
  have hsq : (Real.log s)^2≤4*(Real.log r)^2 := by nlinarith
  dsimp [baseLoss]
  rw [inv_pow,inv_pow,inv_eq_one_div,inv_eq_one_div]
  rw [show 4*(1/(Real.log s)^2)=4/(Real.log s)^2 by ring]
  exact (div_le_div_iff₀ (sq_pos_of_pos hlogr) (sq_pos_of_pos hlogs)).mpr (by simpa using hsq)

theorem sector_relative_perturbation {G E : ℂ → ℂ} {C : ℝ}
    (hG : Tendsto G sectorInfinity sectorInfinity)
    (hupper : ∀ᶠ z in sectorInfinity,‖G z‖≤C*‖z‖)
    (he : E =o[sectorInfinity] (fun z => baseLoss ‖z‖)) :
    Tendsto (fun z => G z*(1+E z)) sectorInfinity sectorInfinity := by
  apply tendsto_sectorInfinity_of_close_map (C := 1) zero_le_one hG
  filter_upwards [hupper,he.bound (by norm_num : (0:ℝ)<1/4),
    tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (max C 1)),
    (tendsto_norm_sectorInfinity.comp hG).eventually (eventually_gt_atTop (1:ℝ))] with z hu hez hz hGz
  have hz1 : 1<‖z‖ := (le_max_right _ _).trans_lt hz
  have hlog : 0<Real.log ‖z‖ := Real.log_pos hz1
  have hbase : 0<baseLoss ‖z‖ := by dsimp [baseLoss]; positivity
  rw [Real.norm_eq_abs,abs_of_pos hbase] at hez
  have hb := baseLoss_le_of_upper hz1 hGz ((le_max_left _ _).trans hz.le) hu
  dsimp only [Function.comp_apply] at hb
  have herr : ‖E z‖≤baseLoss ‖G z‖ := by linarith
  rw [show G z*(1+E z)-G z=G z*E z by ring,norm_mul,one_mul]
  exact mul_le_mul_of_nonneg_left herr (norm_nonneg _)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem zero_exponent_relative_error {E x : ℂ → ℂ} {X : ℝ → ℝ} {C K ε : ℝ}
    (hC : 1≤C) (hK : 0≤K) (hε : 0<ε)
    (hX : Tendsto X atTop atTop) (hlog : Real.log =o[atTop] X)
    (hmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C≤‖x z‖ ∧ ‖x z‖≤C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity)
    (herr : ∀ᶠ z in sectorInfinity,‖E z‖≤K*Real.exp (-ε*(x z).re)) :
    E =o[sectorInfinity] (fun z => baseLoss ‖z‖) := by
  let F : ℂ → ℂ := fun z => z*(1+E z)
  have hf : ∀ᶠ z in sectorInfinity,‖F z-z‖≤K*‖z‖*Real.exp (-ε*(x z).re) := by
    filter_upwards [herr] with z hz
    have he : F z-z=z*E z := by dsimp [F]; ring
    rw [he,norm_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hz (norm_nonneg z)]
  have hs := zero_exponent_error_small hC hK hε hX hlog hmod hx hf
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  filter_upwards [hs.bound hδ,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hz hz1
  have hlog : 0<Real.log ‖z‖ := Real.log_pos hz1
  have hb : 0<baseLoss ‖z‖ := by dsimp [baseLoss]; positivity
  have hnorm : 0<‖z‖ := zero_lt_one.trans hz1
  have he : F z-z=z*E z := by dsimp [F]; ring
  rw [he,norm_mul,Real.norm_eq_abs,abs_of_pos (logarithmicRadius_pos hz1)] at hz
  rw [Real.norm_eq_abs,abs_of_pos hb]
  apply (mul_le_mul_iff_right₀ hnorm).mp
  dsimp [logarithmicRadius,baseLoss] at *
  nlinarith only [hz]

lemma nearIdentity_norm_bounds {g : ℂ → ℂ}
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖)) :
    ∀ᶠ z in sectorInfinity,‖z‖/2≤‖g z‖ ∧ ‖g z‖≤2*‖z‖ := by
  have hs := hg.trans_isBigO logarithmicRadius_isBigO_norm
  filter_upwards [hs.bound (by norm_num : (0:ℝ)<1/2)] with z hz
  simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z)] at hz
  have hl := norm_sub_le (g z) (g z-z)
  rw [sub_sub_cancel] at hl
  have hu := norm_add_le (g z-z) z
  rw [sub_add_cancel] at hu
  constructor <;> linarith [norm_nonneg z]

theorem relative_error_comp_nearIdentity {E g : ℂ → ℂ}
    (he : E =o[sectorInfinity] (fun z => baseLoss ‖z‖))
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖)) :
    (fun z => E (g z)) =o[sectorInfinity] (fun z => baseLoss ‖z‖) := by
  have hdisp : ∀ᶠ z in sectorInfinity,‖g z-z‖≤logarithmicRadius ‖z‖ := by
    filter_upwards [hg.bound zero_lt_one,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hz hz1
    simpa only [one_mul,Real.norm_eq_abs,abs_of_pos (logarithmicRadius_pos hz1)] using hz
  have ht := tendsto_sectorInfinity_of_logarithmic_displacement hdisp
  have hb : (fun z => baseLoss ‖g z‖) =O[sectorInfinity] (fun z => baseLoss ‖z‖) := by
    apply Asymptotics.IsBigO.of_bound 4
    filter_upwards [nearIdentity_norm_bounds hg,
      tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ)),
      (tendsto_norm_sectorInfinity.comp ht).eventually (eventually_gt_atTop (2:ℝ))] with z hz hz1 hg2
    have hg1 : 1<‖g z‖ := by dsimp only [Function.comp_apply] at hg2; linarith
    simp only [Real.norm_eq_abs,abs_of_nonneg (show 0≤baseLoss ‖g z‖ by dsimp [baseLoss]; positivity),
      abs_of_nonneg (show 0≤baseLoss ‖z‖ by dsimp [baseLoss]; positivity)]
    exact baseLoss_le_of_upper hg1 hz1 hg2.le (by linarith [hz.1])
  exact (he.comp_tendsto ht).trans_isBigO hb

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma sector_principal_log_bound {G : ℂ → ℂ} {C : ℝ}
    (hGa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ G z)
    (hG : Tendsto G sectorInfinity sectorInfinity)
    (hupper : ∀ᶠ z in sectorInfinity,‖G z‖≤C*‖z‖) :
    (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => Complex.log (G z)) z) ∧
    (∀ᶠ z in sectorInfinity,‖Complex.log (G z)‖≤(2+Real.pi)*Real.log ‖z‖) := by
  constructor
  · filter_upwards [hGa,hG.eventually SectorEventually.realpart_pos] with z ha hr
    exact ha.clog (Complex.mem_slitPlane_iff.mpr (Or.inl hr))
  · filter_upwards [hupper,
      tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (max C (Real.exp 1))),
      (tendsto_norm_sectorInfinity.comp hG).eventually (eventually_gt_atTop (1:ℝ))] with z hu hz hGz
    have hr : Real.exp 1<‖z‖ := (le_max_right _ _).trans_lt hz
    have hn : 0<‖z‖ := (Real.exp_pos 1).trans hr
    have hlog : 1≤Real.log ‖z‖ := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hr.le
    have hG1 : 1<‖G z‖ := hGz
    have hupper' : ‖G z‖≤‖z‖^2 := hu.trans (by have := (le_max_left _ _).trans hz.le; nlinarith)
    have hlogG : Real.log ‖G z‖≤2*Real.log ‖z‖ := by
      simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (zero_lt_one.trans hG1) hupper'
    have hh := Complex.norm_le_abs_re_add_abs_im (Complex.log (G z))
    rw [Complex.log_re,Complex.log_im,abs_of_pos (Real.log_pos hG1)] at hh
    nlinarith [Complex.abs_arg_le_pi (G z),mul_le_mul_of_nonneg_left hlog Real.pi_pos.le]

lemma littleO_baseLoss_tendsto_zero {E : ℂ → ℂ}
    (he : E =o[sectorInfinity] (fun z => baseLoss ‖z‖)) : Tendsto E sectorInfinity (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun z => norm_nonneg (E z)) _
    (admissible_baseLoss.tendsto_zero.comp tendsto_norm_sectorInfinity)
  filter_upwards [he.bound zero_lt_one] with z hz
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (show 0≤baseLoss ‖z‖ by dsimp [baseLoss]; positivity),one_mul] using hz

theorem nearIdentity_factor_ratio {G g : ℂ → ℂ} {C : ℝ}
    (hGa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ G z)
    (hG : Tendsto G sectorInfinity sectorInfinity)
    (hupper : ∀ᶠ z in sectorInfinity,‖G z‖≤C*‖z‖)
    (hgt : Tendsto g sectorInfinity sectorInfinity)
    (hm : ∀ᶠ z in sectorInfinity,‖g z-z‖≤logarithmicRadius ‖z‖)
    (hg : (fun z => g z-z) =o[sectorInfinity] (fun z => ‖z‖/(Real.log ‖z‖)^5)) :
    Tendsto (fun z => G (g z)/G z) sectorInfinity (𝓝 1) := by
  obtain ⟨ha,hb⟩ := sector_principal_log_bound hGa hG hupper
  have hi := sector_log_increment_small (show 0≤2+Real.pi by positivity) ha hb hm hg
  have hit : Tendsto (fun z => Complex.log (G (g z))-Complex.log (G z)) sectorInfinity (𝓝 0) :=
    littleO_baseLoss_tendsto_zero hi
  have hlim := Complex.continuous_exp.tendsto 0 |>.comp hit
  simp only [Complex.exp_zero] at hlim
  apply hlim.congr'
  filter_upwards [hG.eventually SectorEventually.realpart_pos,
    (hG.comp hgt).eventually SectorEventually.realpart_pos] with z hz hgz
  have h0 : G z≠0 := by
    intro h
    have hp : 0<(G z).re := hz
    rw [h,Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hg0 : G (g z)≠0 := by
    intro h
    change 0<(G (g z)).re at hgz
    simp [h] at hgz
  dsimp only [Function.comp_apply]
  rw [Complex.exp_sub,Complex.exp_log hg0,Complex.exp_log h0]

lemma relative_modulus_bounds {F G : ℂ → ℂ}
    (h : Tendsto (fun z => F z/G z) sectorInfinity (𝓝 1)) :
    ∀ᶠ z in sectorInfinity,‖G z‖/2≤‖F z‖ ∧ ‖F z‖≤2*‖G z‖ := by
  have hn := (continuous_norm.tendsto (1:ℂ)).comp h
  simp only [norm_one] at hn
  have hlo := hn.eventually (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))
  have hup := hn.eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2))
  filter_upwards [hlo,hup] with z hl hu
  have hG0 : G z≠0 := by intro he; norm_num [Function.comp_apply,he] at hl
  have hnG : 0<‖G z‖ := norm_pos_iff.mpr hG0
  simp only [Function.comp_apply,norm_div] at hl hu
  have hl' := (lt_div_iff₀ hnG).mp hl
  have hu' := (div_lt_iff₀ hnG).mp hu
  constructor <;> linarith

theorem relative_modulus_comparison {F G : ℂ → ℂ} {C : ℝ}
    (hC : 0<C) (h : Tendsto (fun z => F z/G z) sectorInfinity (𝓝 1))
    (hmod : ∀ᶠ z in sectorInfinity,‖G (‖z‖:ℂ)‖/C≤‖G z‖ ∧ ‖G z‖≤C*‖G (‖z‖:ℂ)‖) :
    ∀ᶠ z in sectorInfinity,‖F (‖z‖:ℂ)‖/(4*C)≤‖F z‖ ∧ ‖F z‖≤4*C*‖F (‖z‖:ℂ)‖ := by
  have hb := relative_modulus_bounds h
  have hrad := tendsto_norm_sectorInfinity.eventually (tendsto_real_sectorInfinity.eventually hb)
  filter_upwards [hb,hrad,hmod] with z hz hr hm
  have hml := (div_le_iff₀ hC).mp hm.1
  have h1 := mul_le_mul_of_nonneg_left hz.1 hC.le
  have h2 := mul_le_mul_of_nonneg_left hr.1 hC.le
  constructor
  · apply (div_le_iff₀ (show 0<4*C by positivity)).mpr
    nlinarith [hr.2]
  · nlinarith [hz.2,hm.2]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem zero_exponent_chart {H G E x : ℂ → ℂ} {X : ℝ → ℝ} {C K ε D M : ℝ}
    (hHa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ H z)
    (hHr : ∀ᶠ r : ℝ in atTop,(H (r:ℂ)).im=0)
    (hC : 1≤C) (hK : 0≤K) (hε : 0<ε)
    (hX : Tendsto X atTop atTop) (hlog : Real.log =o[atTop] X)
    (hxmod : ∀ᶠ z in sectorInfinity,X ‖z‖/C≤‖x z‖ ∧ ‖x z‖≤C*X ‖z‖)
    (hx : Tendsto x sectorInfinity sectorInfinity)
    (hHerr : ∀ᶠ z in sectorInfinity,‖H z-z‖≤K*‖z‖*Real.exp (-ε*(x z).re))
    (hGa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ G z)
    (hEa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ E z)
    (hG : Tendsto G sectorInfinity sectorInfinity)
    (hD : 0≤D) (hupper : ∀ᶠ z in sectorInfinity,‖G z‖≤D*‖z‖)
    (hM : 0<M)
    (hGmod : ∀ᶠ z in sectorInfinity,‖G (‖z‖:ℂ)‖/M≤‖G z‖ ∧ ‖G z‖≤M*‖G (‖z‖:ℂ)‖)
    (hEerr : ∀ᶠ z in sectorInfinity,‖E z‖≤K*Real.exp (-ε*(x z).re)) :
    ∃ (g : ℂ → ℂ) (I : ℝ → ℝ),
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ g z ∧ H (g z)=z) ∧
      Tendsto g sectorInfinity sectorInfinity ∧ Tendsto I atTop atTop ∧
      (∀ᶠ r : ℝ in atTop,g (r:ℂ)=(I r:ℂ) ∧ H (I r:ℂ)=(r:ℂ)) ∧
      (∀ᶠ r : ℝ in atTop,I ((H (r:ℂ)).re)=r) ∧
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => G (g z)*(1+E (g z))) z) ∧
      Tendsto (fun z => G (g z)*(1+E (g z))) sectorInfinity sectorInfinity ∧
      (∀ᶠ z in sectorInfinity,
        ‖G (g (‖z‖:ℂ))*(1+E (g (‖z‖:ℂ)))‖/(4*M)≤‖G (g z)*(1+E (g z))‖ ∧
        ‖G (g z)*(1+E (g z))‖≤4*M*‖G (g (‖z‖:ℂ))*(1+E (g (‖z‖:ℂ)))‖) ∧
      ((fun z => (G z).re) =o[sectorInfinity] Complex.re →
        (fun z => (G (g z)*(1+E (g z))).re) =o[sectorInfinity] Complex.re) := by
  obtain ⟨g,I,hga,hgt,hIt,hreal,hri,hgs,hgN,hgre⟩ :=
    zero_exponent_real_inverse hHa hHr hC hK hε hX hlog hxmod hx hHerr
  have he := relative_error_comp_nearIdentity
    (zero_exponent_relative_error hC hK hε hX hlog hxmod hx hEerr) hgs
  have hu : ∀ᶠ z in sectorInfinity,‖G (g z)‖≤(2*D)*‖z‖ := by
    filter_upwards [hgt.eventually hupper,nearIdentity_norm_bounds hgs] with z hz hn
    exact hz.trans (by nlinarith [mul_le_mul_of_nonneg_left hn.2 hD])
  have hdisp : ∀ᶠ z in sectorInfinity,‖g z-z‖≤logarithmicRadius ‖z‖ := by
    filter_upwards [hgs.bound zero_lt_one,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop (1:ℝ))] with z hz hz1
    simpa only [one_mul,Real.norm_eq_abs,abs_of_pos (logarithmicRadius_pos hz1)] using hz
  have hratio := nearIdentity_factor_ratio hGa hG hupper hgt hdisp (hgN 5)
  have het := littleO_baseLoss_tendsto_zero he
  have hrat : Tendsto (fun z => G (g z)*(1+E (g z))/G z) sectorInfinity (𝓝 1) := by
    have hh := hratio.mul (het.const_add 1)
    simp only [add_zero,mul_one] at hh
    convert hh using 1
    ext z
    ring
  refine ⟨g,I,hga,hgt,hIt,hreal,hri,?_,
    sector_relative_perturbation (hG.comp hgt) hu he,
    relative_modulus_comparison hM hrat hGmod,?_⟩
  · filter_upwards [hga,hgt.eventually hGa,hgt.eventually hEa] with z hg hGz hEz
    exact (hGz.comp hg.1).mul (analyticAt_const.add (hEz.comp hg.1))
  · intro hsmall
    have hbig : (fun z => G (g z)) =O[sectorInfinity] (fun z => ‖z‖) := by
      apply Asymptotics.IsBigO.of_bound (2*D)
      simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hu
    have hprod := hbig.mul_isLittleO he
    have hep : (fun z => G (g z)*E (g z)) =o[sectorInfinity] (fun z => logarithmicRadius ‖z‖) := hprod
    have hh := nearIdentity_realpart_separation hgs hsmall hep
    convert hh using 1
    ext z
    congr 1
    ring

end DegeneratingTrees.Clock
end

end OAI
