import Mathlib
import OAI.Analysis.PathSelection.PuiseuxInverses
import OAI.Analysis.PathSelection.SectorLimits

namespace OAI

/-! Positive Puiseux sectors, loss scales and strict phase estimates. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma analytic_root_error {n : ℕ} (hn : 0 < n) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z in radialInfinity,
      ‖F (complexRoot n z)-F 0‖ ≤ K*‖z‖^(-(n:ℝ)⁻¹) := by
  obtain ⟨K,hK,hbound⟩ := hF.differentiableAt.hasDerivAt.isBigO_sub.exists_pos
  refine ⟨K,hK,?_⟩
  filter_upwards [(complexRoot_tendsto_zero hn).eventually hbound.bound] with z hz
  simpa only [sub_zero,complexRoot_norm,rootCoord] using hz

 

theorem Puiseux.positive_sector {f : ℝ → ℝ}
    (hf : Puiseux (fun t => (f t:ℂ))) (hft : Tendsto f atTop atTop) :
    ∃ (q : ℚ) (a C K R : ℝ) (G : ℂ → ℂ), 0 < (q:ℝ) ∧ 0 < a ∧ 0 < C ∧ 0 < K ∧
      (∀ z : ℂ, R < ‖z‖ → 0 < z.re → AnalyticAt ℂ G z) ∧
      (fun t => (f t:ℂ)) =ᶠ[atTop] (fun t => G (t:ℂ)) ∧
      ∀ z : ℂ, R < ‖z‖ →
        ‖G z-(C:ℂ)*z^((q:ℝ):ℂ)‖ ≤ K * ‖z‖^((q:ℝ)-a) := by
  obtain ⟨n,k,hn,hk,F,hF,hFre,hFim,he⟩ := hf.normalize_unbounded_real hft
  let q : ℚ := (k:ℚ)/(n:ℚ)
  let a : ℝ := (n:ℝ)⁻¹
  let G : ℂ → ℂ := fun z => (complexRoot n z)^(-(k:ℤ)) * F (complexRoot n z)
  have hq : 0 < (q:ℝ) := by dsimp [q]; push_cast; positivity
  have ha : 0 < a := inv_pos.mpr (Nat.cast_pos.mpr hn)
  have hqeq : ((q:ℝ):ℂ) = ((-((-(k:ℤ)):ℝ)/(n:ℝ):ℝ):ℂ) := by
    dsimp [q]
    push_cast
    ring
  have hFreal : F 0 = ((F 0).re:ℂ) := Complex.ext rfl (by simpa using hFim)
  obtain ⟨K,hK,hbound⟩ := analytic_root_error hn hF
  obtain ⟨R,hR⟩ := radial_eventually
    (((complexRoot_tendsto_zero hn).eventually hF.eventually_analyticAt).and hbound)
  refine ⟨q,a,(F 0).re,K,max R 0,G,hq,ha,hFre,hK,?_,?_,?_⟩
  · intro z hz hzre
    have hr := complexRoot_analytic (n := n) hzre
    have hr0 : complexRoot n z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      intro h; simp [h] at hzre))
    exact (hr.zpow hr0).mul (((hR z ((le_max_left _ _).trans_lt hz)).1).comp hr)
  · filter_upwards [he,eventually_gt_atTop (0:ℝ)] with t ht htpos
    simpa only [G,complexRoot_real htpos.le,←Complex.ofReal_zpow,Complex.real_smul] using ht
  · intro z hz
    have hzpos : 0 < ‖z‖ := (le_max_right _ _).trans_lt hz
    have herr := (hR z ((le_max_left _ _).trans_lt hz)).2
    have heq : G z-(F 0).re*z^((q:ℝ):ℂ) =
        z^((q:ℝ):ℂ) * (F (complexRoot n z)-F 0) := by
      dsimp [G]
      rw [complexRoot_zpow,hFreal]
      have hexp : ((-((-(k:ℤ)):ℝ)/(n:ℝ):ℝ):ℂ) = ((q:ℝ):ℂ) := hqeq.symm
      push_cast at hexp ⊢
      rw [hexp]
      simp only [Complex.ofReal_re]
      ring
    rw [heq,norm_mul,Complex.norm_cpow_real]
    calc
      ‖z‖^(q:ℝ)*‖F (complexRoot n z)-F 0‖ ≤
          ‖z‖^(q:ℝ)*(K*‖z‖^(-a)) := mul_le_mul_of_nonneg_left herr (Real.rpow_nonneg (norm_nonneg _) _)
      _ = K*‖z‖^((q:ℝ)-a) := by rw [sub_eq_add_neg,Real.rpow_add hzpos]; ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees

def scaleEnvelope (ω : ℝ → ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  sSup (ω '' Icc (r/(2:ℝ)^k) (2^k*r))

private lemma scale_window_bound {ω : ℝ → ℝ} {n₀ : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hb : ∀ n r, (2:ℝ)^(n+n₀) < r → r < (2:ℝ)^(n+n₀+2) → ω r ≤ w n)
    (k n : ℕ) {r : ℝ} (hrl : (2:ℝ)^(n+(n₀+k+1)) < r)
    (hru : r < (2:ℝ)^(n+(n₀+k+1)+2)) {s : ℝ}
    (hsl : r/(2:ℝ)^k ≤ s) (hsu : s ≤ 2^k*r) :
    ω s ≤ ∑ j ∈ Finset.range (2*k+2), w (n+j) := by
  have hpow : (0:ℝ) < 2^k := by positivity
  have hlo : (2:ℝ)^(n+n₀+1) < s := by
    have hrl' : 2^(n+n₀+1)*2^k < r := by
      simpa only [←pow_add,show n+n₀+1+k=n+(n₀+k+1) by omega] using hrl
    exact (lt_div_iff₀ hpow).mpr hrl' |>.trans_le hsl
  have hhi : s < (2:ℝ)^(n+n₀+1) * 2^(2*k+2) := by
    have hu := mul_lt_mul_of_pos_left hru hpow
    have he : (2:ℝ)^k*2^(n+(n₀+k+1)+2) = 2^(n+n₀+1)*2^(2*k+2) := by
      simp only [←pow_add]
      congr 1
      omega
    exact hsu.trans_lt (he ▸ hu)
  obtain ⟨j,hjl,hju⟩ := dyadic_shell (show (0:ℝ)<2^(n+n₀+1) by positivity) hlo.le
  have hjlt : j < 2*k+2 := by
    have hp : (2:ℝ)^j < 2^(2*k+2) := (mul_lt_mul_iff_of_pos_left (show (0:ℝ)<2^(n+n₀+1) by positivity)).mp (hjl.trans_lt hhi)
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hp
  have hl : (2:ℝ)^(n+j+n₀) < s := by
    have hp : (2:ℝ)^(n+j+n₀) < 2^(n+n₀+1)*2^j := by
      rw [←pow_add]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    exact hp.trans_le hjl
  have hu : s < (2:ℝ)^(n+j+n₀+2) := by
    convert hju using 1
    simp only [←pow_add]
    calc
      (2:ℝ)^(n+j+n₀+2) = 2^((n+n₀+1+j)+1) := by congr 1; omega
      _ = 2*2^(n+n₀+1+j) := by rw [pow_succ]; ring
  exact (hb (n+j) s hl hu).trans
    (Finset.single_le_sum (fun i _ => hw (n+i)) (Finset.mem_range.mpr hjlt))

private lemma scale_envelope_bdd {ω : ℝ → ℝ} {n₀ : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hb : ∀ n r, (2:ℝ)^(n+n₀) < r → r < (2:ℝ)^(n+n₀+2) → ω r ≤ w n)
    (k : ℕ) {r : ℝ} (hr : (2:ℝ)^(n₀+k+2) ≤ r) :
    BddAbove (ω '' Icc (r/(2:ℝ)^k) (2^k*r)) := by
  obtain ⟨n,hnl,hnu⟩ := dyadic_shell (show (0:ℝ)<2^(n₀+k+2) by positivity) hr
  have hrl : (2:ℝ)^(n+(n₀+k+1)) < r := by
    have hp : (2:ℝ)^(n+(n₀+k+1)) < 2^(n₀+k+2)*2^n := by
      rw [←pow_add]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    exact hp.trans_le hnl
  have hru : r < (2:ℝ)^(n+(n₀+k+1)+2) := by
    convert hnu using 1
    rw [←pow_add]
    calc
      (2:ℝ)^(n+(n₀+k+1)+2) = 2^((n₀+k+2+n)+1) := by congr 1; omega
      _ = 2*2^(n₀+k+2+n) := by rw [pow_succ]; ring
  refine ⟨∑ j ∈ Finset.range (2*k+2),w (n+j),?_⟩
  rintro _ ⟨s,hs,rfl⟩
  exact scale_window_bound hw hb k n hrl hru hs.1 hs.2

lemma AdmissibleAngularLoss.scale_envelope {ω : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) (k : ℕ) :
    AdmissibleAngularLoss (scaleEnvelope ω k) ∧
      ∀ᶠ r : ℝ in atTop, ∀ s ∈ Icc (r/(2:ℝ)^k) (2^k*r),
        ω s ≤ scaleEnvelope ω k r := by
  obtain ⟨hp,n₀,w,hw,hs,hb⟩ := hω
  have hupper : ∀ᶠ r : ℝ in atTop, ∀ s ∈ Icc (r/(2:ℝ)^k) (2^k*r),
        ω s ≤ scaleEnvelope ω k r := by
    filter_upwards [eventually_ge_atTop ((2:ℝ)^(n₀+k+2))] with r hr s hs
    exact le_csSup (scale_envelope_bdd hw hb k hr) (mem_image_of_mem _ hs)
  have hpk : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hself {r : ℝ} (hr : 0 ≤ r) : r ∈ Icc (r/(2:ℝ)^k) (2^k*r) :=
    ⟨div_le_self hr hpk,le_mul_of_one_le_left hr hpk⟩
  refine ⟨⟨?_,n₀+k+1,fun n => ∑ j ∈ Finset.range (2*k+2),w (n+j),?_,?_,?_⟩,hupper⟩
  · filter_upwards [hp,hupper,eventually_ge_atTop (0:ℝ)] with r hp hu hr
    have hh := hu r (hself hr)
    exact ⟨hp.1.trans_le hh,hp.2.trans hh⟩
  · intro n
    exact Finset.sum_nonneg (fun j _ => hw (n+j))
  · have hsum (s : Finset ℕ) : Summable (fun n => ∑ j ∈ s, w (n+j)) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using ((summable_nat_add_iff j).mpr hs).add ih
    exact hsum _
  · intro n r hl hu
    apply csSup_le
    · have hr : 0 ≤ r := (show (0:ℝ)<2^(n+(n₀+k+1)) by positivity).trans hl |>.le
      exact ⟨ω r,mem_image_of_mem _ (hself hr)⟩
    · rintro _ ⟨s,hs,rfl⟩
      exact scale_window_bound hw hb k n hl hu hs.1 hs.2

end DegeneratingTrees

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma cpow_real_re {z : ℂ} (hz : z ≠ 0) (q : ℝ) :
    (z ^ (q:ℂ)).re = ‖z‖^q * Real.cos (q*z.arg) := by
  rw [Complex.cpow_def_of_ne_zero hz,Complex.exp_re]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero,zero_add,Complex.log_re,Complex.log_im]
  rw [←Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
  congr 2
  ring

lemma cpow_real_re_lower {z : ℂ} (hz : z ≠ 0) {q : ℝ} (hq : 0 ≤ q)
    (hq1 : q ≤ 1) (hzarg : |z.arg| ≤ Real.pi/2) :
    ‖z‖^q * Real.cos (q*Real.pi/2) ≤ (z^(q:ℂ)).re := by
  rw [cpow_real_re hz]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  rw [←Real.cos_abs (q*z.arg),abs_mul,abs_of_nonneg hq]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · nlinarith [Real.pi_pos]
  · nlinarith

 
lemma power_error_relative {a q K : ℝ} (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, 0 < r ∧ K*r^(q-a) ≤ ε*r^q := by
  have ht : Tendsto (fun r : ℝ => K*r^(-a)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).const_mul K
  filter_upwards [ht.eventually (eventually_lt_nhds hε),eventually_gt_atTop (0:ℝ)] with r hr hr0
  refine ⟨hr0,?_⟩
  rw [sub_eq_add_neg,Real.rpow_add hr0]
  nlinarith [Real.rpow_pos_of_pos hr0 q]

lemma power_model_norm {G : ℂ → ℂ} {q a C K R : ℝ} (ha : 0 < a) (hC : 0 < C)
    (herr : ∀ z : ℂ, R < ‖z‖ → ‖G z-(C:ℂ)*z^(q:ℂ)‖ ≤ K*‖z‖^(q-a)) :
    ∀ᶠ r : ℝ in atTop, 0 < r ∧ ∀ z : ℂ, ‖z‖=r →
      C/2*r^q ≤ ‖G z‖ ∧ ‖G z‖ ≤ 2*C*r^q := by
  filter_upwards [power_error_relative (q := q) (K := K) ha (C/2) (by positivity),
    eventually_gt_atTop R] with r hr hR
  refine ⟨hr.1,?_⟩
  intro z hz
  have he := (herr z (hz ▸ hR)).trans (hz ▸ hr.2)
  rw [hz] at he
  have hm : ‖(C:ℂ)*z^(q:ℂ)‖ = C*r^q := by
    rw [norm_mul,Complex.norm_of_nonneg hC.le,Complex.norm_cpow_real,hz]
  have hu := norm_add_le (G z-(C:ℂ)*z^(q:ℂ)) ((C:ℂ)*z^(q:ℂ))
  have hl := norm_sub_le (G z) (G z-(C:ℂ)*z^(q:ℂ))
  rw [sub_add_cancel,hm] at hu
  rw [sub_sub_cancel,hm] at hl
  constructor <;> nlinarith [Real.rpow_pos_of_pos hr.1 q]

 

theorem power_model_sublinear_sector {G : ℂ → ℂ} {q a C K R : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (ha : 0 < a) (hC : 0 < C)
    (herr : ∀ z : ℂ, R < ‖z‖ → ‖G z-(C:ℂ)*z^(q:ℂ)‖ ≤ K*‖z‖^(q-a))
    {ω : ℝ → ℝ} (hω : AdmissibleAngularLoss ω) (S : ℝ) :
    ∃ T : ℝ, ∀ z ∈ lossSector ω T, G z ∈ lossSector ω S := by
  let d := Real.cos (q*Real.pi/2)
  have hd : 0 < d := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],by nlinarith [Real.pi_pos]⟩
  have hωsmall : ∀ᶠ r : ℝ in atTop, 0 < ω r ∧ ω r < d/8 :=
    hω.1.mono (fun _ h => h.1) |>.and (hω.tendsto_zero.eventually (eventually_lt_nhds (by positivity)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hωsmall
  have hescape : Tendsto (fun r : ℝ => C/2*r^q) atTop atTop :=
    (tendsto_rpow_atTop hq).const_mul_atTop (by positivity)
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((power_model_norm ha hC herr).and
    ((power_error_relative (q := q) (K := K) ha (C*d/2) (by positivity)).and
    ((hescape.eventually (eventually_gt_atTop (max W S))).and
    ((eventually_gt_atTop R).and hω.1))))
  refine ⟨T,?_⟩
  intro z hz
  obtain ⟨hn,he,hes,hR,hωz⟩ := hT ‖z‖ hz.1.le
  have hb := hn.2 z rfl
  have hw := hW ‖G z‖ ((le_max_left _ _).trans (hes.le.trans hb.1))
  have harg : |z.arg| ≤ Real.pi/2 := by linarith [hωz.1,hz.2]
  have hpow := cpow_real_re_lower (norm_pos_iff.mp hn.1) hq.le hq1.le harg
  have herror := (abs_re_le_norm (G z-(C:ℂ)*z^(q:ℂ))).trans ((herr z hR).trans he.2)
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at herror
  have hlow : C*d/2*‖z‖^q ≤ (G z).re := by
    dsimp [d] at *
    nlinarith [(abs_le.mp herror).1]
  have hnormpos : 0 < ‖G z‖ := (mul_pos (by positivity) (Real.rpow_pos_of_pos hn.1 q)).trans_le hb.1
  refine ⟨(le_max_right _ _).trans_lt (hes.trans_le hb.1),
    arg_lt_of_re_lower hw.1 (norm_pos_iff.mp hnormpos) ?_⟩
  have hm := mul_le_mul_of_nonneg_left hb.2 hw.1.le
  have hh := mul_lt_mul_of_pos_right hw.2 (mul_pos (by positivity : 0 < 2*C) (Real.rpow_pos_of_pos hn.1 q))
  nlinarith [Real.rpow_pos_of_pos hn.1 q]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma phase_ratio_error {G : ℂ → ℂ} {f : ℝ → ℝ} {q : ℝ}
    (hf : ∀ᶠ r : ℝ in atTop,0<f r)
    (h : Tendsto (fun z => Complex.exp (-Complex.I*(q*z.arg:ℝ))*(G z/(f ‖z‖:ℂ)))
      sectorInfinity (𝓝 1)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ z in sectorInfinity,‖G z-(f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ))‖≤ε*f ‖z‖ := by
  have he := Metric.tendsto_nhds.mp h ε hε
  filter_upwards [he,tendsto_norm_sectorInfinity.eventually hf] with z hz hfz
  rw [dist_eq_norm] at hz
  have hf0 : (f ‖z‖:ℂ)≠0 := by exact_mod_cast hfz.ne'
  have hei : ‖Complex.exp (Complex.I*(q*z.arg:ℝ))‖=1 := by simp [Complex.norm_exp]
  have heq : G z-(f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ)) =
      ((f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ))) *
        (Complex.exp (-Complex.I*(q*z.arg:ℝ))*(G z/(f ‖z‖:ℂ))-1) := by
    have hx : Complex.exp (Complex.I*(q*z.arg:ℝ))*Complex.exp (-Complex.I*(q*z.arg:ℝ))=1 := by
      rw [←Complex.exp_add,show Complex.I*(q*z.arg:ℝ)+ -Complex.I*(q*z.arg:ℝ)=0 by ring,Complex.exp_zero]
    calc
      G z-(f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ)) =
          (Complex.exp (Complex.I*(q*z.arg:ℝ))*Complex.exp (-Complex.I*(q*z.arg:ℝ)))*G z-
            (f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ)) := by rw [hx,one_mul]
      _ = _ := by field_simp
  rw [heq,norm_mul,norm_mul,Complex.norm_of_nonneg hfz.le,hei,mul_one]
  nlinarith

theorem strict_phase_sector_mapping {G : ℂ → ℂ} {f : ℝ → ℝ} {q : ℝ}
    (hq : 0≤q) (hq1 : q<1) (hf : Tendsto f atTop atTop)
    (h : Tendsto (fun z => Complex.exp (-Complex.I*(q*z.arg:ℝ))*(G z/(f ‖z‖:ℂ)))
      sectorInfinity (𝓝 1)) (ω : ℝ → ℝ) (S : ℝ) (hω : AdmissibleAngularLoss ω) :
    ∃ (η : ℝ → ℝ) (T : ℝ),AdmissibleAngularLoss η ∧
      (∀ z∈lossSector η T,G z∈lossSector ω S) ∧
      (∀ z∈lossSector η T,f ‖z‖/2≤‖G z‖ ∧ ‖G z‖≤2*f ‖z‖) := by
  let d := Real.cos (q*Real.pi/2)
  have hd : 0<d := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],by nlinarith [Real.pi_pos]⟩
  have hd1 : d≤1 := Real.cos_le_one _
  have hfp : ∀ᶠ r : ℝ in atTop,0<f r := hf.eventually (eventually_gt_atTop 0)
  have herr := phase_ratio_error hfp h (d/2) (by positivity)
  have hωsmall := hω.1.and (hω.tendsto_zero.eventually (eventually_lt_nhds (show (0:ℝ)<d/8 by positivity)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hωsmall
  have hfbig : ∀ᶠ r : ℝ in atTop,2*(max W S)<f r := hf.eventually (eventually_gt_atTop _)
  have harg : ∀ᶠ z in sectorInfinity,|z.arg|<Real.pi/2 := by
    obtain ⟨U,hU⟩ := eventually_atTop.mp admissible_baseLoss.1
    refine ⟨baseLoss,U,admissible_baseLoss,?_⟩
    intro z hz
    change |z.arg|<Real.pi/2
    have hp := (hU ‖z‖ hz.1.le).1
    have hh : |z.arg|<Real.pi/2-baseLoss ‖z‖ := hz.2
    linarith
  obtain ⟨η,T,hη,hdata⟩ := herr.and (harg.and
    (tendsto_norm_sectorInfinity.eventually (hfp.and hfbig)))
  refine ⟨η,T,hη,?_,?_⟩
  · intro z hz
    obtain ⟨he,ha,hfp,hfb⟩ := hdata z hz
    have hm : ‖(f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ))‖=f ‖z‖ := by
      rw [norm_mul,Complex.norm_of_nonneg hfp.le,Complex.norm_exp]
      simp
    have hn := norm_le_norm_sub_add (G z) ((f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ)))
    have hn' := norm_le_norm_sub_add ((f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ))) (G z)
    rw [hm,norm_sub_rev] at hn'
    rw [hm] at hn
    have hlo : f ‖z‖/2≤‖G z‖ := by nlinarith
    have hup : ‖G z‖≤2*f ‖z‖ := by nlinarith
    have hw := hW ‖G z‖ (by linarith [le_max_left W S])
    have hc : d≤Real.cos (q*z.arg) := by
      rw [←Real.cos_abs (q*z.arg),abs_mul,abs_of_nonneg hq]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith [Real.pi_pos]
      · nlinarith
    have hreal := (abs_re_le_norm (G z-(f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ)))).trans he
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.exp_re,Complex.I_re,Complex.I_im,mul_zero,
      Complex.mul_im,zero_add,Real.exp_zero,one_mul] at hreal
    have hrlo : d/2*f ‖z‖≤(G z).re := by
      have hh := mul_le_mul_of_nonneg_left hc hfp.le
      nlinarith [(abs_le.mp hreal).1]
    have hnormpos : 0<‖G z‖ := (half_pos hfp).trans_le hlo
    refine ⟨by linarith [le_max_right W S],arg_lt_of_re_lower hw.1.1 (norm_pos_iff.mp hnormpos) ?_⟩
    have hh := mul_le_mul_of_nonneg_left hup hw.1.1.le
    nlinarith [mul_lt_mul_of_pos_right hw.2 (by positivity : 0<2*f ‖z‖)]
  · intro z hz
    obtain ⟨he,ha,hfp,hfb⟩ := hdata z hz
    have hm : ‖(f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ))‖=f ‖z‖ := by
      rw [norm_mul,Complex.norm_of_nonneg hfp.le,Complex.norm_exp]
      simp
    have hn := norm_le_norm_sub_add (G z) ((f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ)))
    have hn' := norm_le_norm_sub_add ((f ‖z‖:ℂ)*Complex.exp (Complex.I*(q*z.arg:ℝ))) (G z)
    rw [hm,norm_sub_rev] at hn'
    rw [hm] at hn
    constructor <;> nlinarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem sublinear_sector_realpart {G : ℂ → ℂ} {q C : ℝ} (hq : q < 1) (hC : 0 < C)
    (hb : ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖=r → ‖G z‖ ≤ C*r^q)
    {η : ℝ → ℝ} (hη : AdmissibleAngularLoss η) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ lossSector η R,
      |(G z).re| ≤ ε*z.re := by
  intro ε hε
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := 1-q) 2 (by linarith)).bound
    (show 0 < ε/(2*C) by positivity)
  have hηsmall := hη.tendsto_zero.eventually
    (eventually_lt_nhds (by linarith [Real.pi_pos] : (0:ℝ)<Real.pi/2))
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hb.and (hsmall.and (hη.1.and
    (hηsmall.and (eventually_gt_atTop (1:ℝ))))))
  refine ⟨R,?_⟩
  intro z hz
  obtain ⟨hb,hs,hηr,hηπ,hr1⟩ := hR ‖z‖ hz.1.le
  have hr : 0 < ‖z‖ := zero_lt_one.trans hr1
  have hL : 0 < Real.log ‖z‖ := Real.log_pos hr1
  have hL2 : 0 < (Real.log ‖z‖)^2 := sq_pos_of_pos hL
  have hp : 0 < ‖z‖^(1-q) := Real.rpow_pos_of_pos hr _
  have hqpos : 0 < ‖z‖^q := Real.rpow_pos_of_pos hr _
  have hs' : (Real.log ‖z‖)^2 ≤ ε/(2*C)*‖z‖^(1-q) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log ‖z‖)),
      abs_of_pos hp] using hs
  have hre := half_loss_norm_le_re hηr.1.le hηπ.le hz.2
  have hm := mul_le_mul_of_nonneg_right hηr.2 hr.le
  have hlower : ‖z‖ ≤ 2*z.re*(Real.log ‖z‖)^2 := by
    rw [inv_pow] at hm
    have hmul := mul_le_mul_of_nonneg_right hm hL2.le
    have hcancel : ((Real.log ‖z‖)^2)⁻¹*‖z‖*(Real.log ‖z‖)^2 = ‖z‖ := by
      calc
        ((Real.log ‖z‖)^2)⁻¹*‖z‖*(Real.log ‖z‖)^2 =
            ‖z‖*(((Real.log ‖z‖)^2)⁻¹*(Real.log ‖z‖)^2) := by ring
        _ = ‖z‖ := by rw [inv_mul_cancel₀ hL2.ne',mul_one]
    rw [hcancel] at hmul
    have hhr := mul_le_mul_of_nonneg_right hre hL2.le
    nlinarith
  have hprod : ‖z‖^(1-q)*‖z‖^q=‖z‖ := by
    rw [←Real.rpow_add hr,sub_add_cancel,Real.rpow_one]
  have hsm := mul_le_mul_of_nonneg_right hs' (mul_pos (by positivity : 0 < 2*C) hqpos).le
  have hsm' : 2*C*‖z‖^q*(Real.log ‖z‖)^2 ≤ ε*‖z‖ := by
    calc
      2*C*‖z‖^q*(Real.log ‖z‖)^2 ≤ ε/(2*C)*‖z‖^(1-q)*(2*C*‖z‖^q) := by nlinarith
      _ = ε*‖z‖ := by rw [mul_assoc,show ‖z‖^(1-q)*(2*C*‖z‖^q)=2*C*(‖z‖^(1-q)*‖z‖^q) by ring,hprod]; field_simp
  have heL := mul_le_mul_of_nonneg_left hlower hε.le
  have hfinal : C*‖z‖^q ≤ ε*z.re := by nlinarith
  exact (abs_re_le_norm _).trans ((hb z rfl).trans hfinal)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem sector_sublinear_realpart {G : ℂ → ℂ} {q C : ℝ} (hq : q<1) (hC : 0<C)
    (hb : ∀ᶠ z in sectorInfinity,‖G z‖≤C*‖z‖^q) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ ε : ℝ,0<ε → ∃ R : ℝ,∀ z∈lossSector η R,|(G z).re|≤ε*z.re := by
  classical
  obtain ⟨η,T,hη,hT⟩ := hb
  let G' : ℂ → ℂ := fun z => if z∈lossSector η T then G z else 0
  have hb' : ∀ᶠ r : ℝ in atTop,∀ z : ℂ,‖z‖=r → ‖G' z‖≤C*r^q := by
    exact Eventually.of_forall fun r z hz => by
      dsimp [G']
      split_ifs with h
      · have hh := hT z h
        change ‖G z‖≤C*‖z‖^q at hh
        simpa only [hz] using hh
      · simp only [norm_zero]
        exact mul_nonneg hC.le (by rw [←hz]; exact Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨η,hη,?_⟩
  intro ε hε
  obtain ⟨R,hR⟩ := sublinear_sector_realpart hq hC hb' hη ε hε
  refine ⟨max T R,?_⟩
  intro z hz
  have hzT : z∈lossSector η T := ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩
  have hzR : z∈lossSector η R := ⟨(le_max_right _ _).trans_lt hz.1,hz.2⟩
  simpa only [G',ite_eq_left hzT] using hR z hzR

end DegeneratingTrees.Clock
end

end OAI
