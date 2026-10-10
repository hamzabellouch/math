import Mathlib
import OAI.Combinatorics.SharpRamsey.Bounds.SamplingParameter
import OAI.Combinatorics.RamseyFive.Bounds.RamseyPropertyRelated

namespace OAI

open scoped BigOperators Classical
open Finset
namespace SharpRamseyFive
open Filter SimpleGraph
open scoped Topology

def PrimeConstruction (η : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → q.Prime →
    ∃ G : SimpleGraph (Fin ⌊(q:ℝ)^4*Real.log q⌋₊),
      G.CliqueFree 5 ∧ Gᶜ.CliqueFree ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊

lemma graph_lower {N k t : ℕ} (ht : 1 ≤ t) (hkt : k ≤ t)
    (G : SimpleGraph (Fin N)) (hG : G.CliqueFree 5) (hI : Gᶜ.CliqueFree k) :
    N < ramsey 5 t := by
  rw [ramsey_eq_related]
  simpa only [Fintype.card_fin] using SharpLogRamsey.Foundation.order_lt_ramsey G
    (by decide : 2 ≤ 5) ht hG (CliqueFree.mono hkt hI)

lemma prime_in_interval {x : ℝ} (hx : 2 ≤ x) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q:ℝ) ≤ 3*x := by
  have hceil : 0 < ⌈x⌉₊ := by
    have he := Nat.le_ceil x
    by_contra hn
    have : ⌈x⌉₊ = 0 := by omega
    rw [this,Nat.cast_zero] at he
    linarith
  obtain ⟨q,hq,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈x⌉₊ (Nat.ne_of_gt hceil)
  refine ⟨q,hq,(Nat.le_ceil x).trans_lt (by exact_mod_cast hlo),?_⟩
  have hh : (q:ℝ) ≤ 2*(⌈x⌉₊:ℝ) := by exact_mod_cast hhi
  have hh' := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  linarith

lemma conversion_scales (η : ℝ) (A : ℝ) :
    ∀ᶠ t : ℕ in atTop,
      2 ≤ t ∧ 1 < Real.log t ∧
      A ≤ (t:ℝ)/(4*(Real.log t)^(1+η)) ∧
      2 ≤ (t:ℝ)/(4*(Real.log t)^(1+η)) ∧
      Real.log (t:ℝ)/2 ≤ Real.log ((t:ℝ)/(4*(Real.log t)^(1+η))) := by
  have hlog : Tendsto (fun t : ℕ => Real.log (t:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun t : ℕ =>
      (Real.log 4+(1+η)*Real.log (Real.log t))/Real.log t) atTop (nhds 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hlog
    have hh' := (tendsto_const_nhds (x := Real.log 4)).div_atTop hlog
    simpa only [Function.comp_apply, id_eq, add_div,mul_div_assoc,mul_zero,add_zero] using
      hh'.add (hh.const_mul (1+η))
  have hlogbound : ∀ᶠ t : ℕ in atTop,
      Real.log (t:ℝ)/2 ≤ Real.log ((t:ℝ)/(4*(Real.log t)^(1+η))) := by
    filter_upwards [eventually_ge_atTop (2:ℕ),hlog.eventually (eventually_gt_atTop (1:ℝ)),
      hsmall.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with t ht hl hs
    have htp : 0<(t:ℝ) := by exact_mod_cast (show 0<t by omega)
    have hlp : 0<Real.log (t:ℝ) := by linarith
    rw [Real.log_div (ne_of_gt htp) (by positivity), Real.log_mul (by norm_num)
      (ne_of_gt (Real.rpow_pos_of_pos hlp _)),Real.log_rpow hlp]
    have h := (div_lt_iff₀ hlp).mp hs
    linarith
  have hgrowth : Tendsto (fun t : ℕ => Real.log ((t:ℝ)/(4*(Real.log t)^(1+η)))) atTop atTop :=
    tendsto_atTop_mono' _ hlogbound (hlog.atTop_div_const (by norm_num))
  have hxgrowth : Tendsto (fun t : ℕ => (t:ℝ)/(4*(Real.log t)^(1+η))) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.comp hgrowth)
    filter_upwards [hlog.eventually (eventually_gt_atTop (1:ℝ)),eventually_ge_atTop (2:ℕ)] with t hl ht
    have htp : 0<(t:ℝ) := by exact_mod_cast (show 0<t by omega)
    rw [Function.comp_apply,Real.exp_log (div_pos htp (by positivity))]
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog.eventually (eventually_gt_atTop (1:ℝ)),
    hxgrowth.eventually (eventually_ge_atTop A),hxgrowth.eventually (eventually_ge_atTop 2),hlogbound]
    with t ht hl hA h2 hb
  exact ⟨ht,hl,hA,h2,hb⟩

lemma lower_expression_identity (t l η : ℝ) (hl : 0 < l) :
    (t/(4*l^(1+η)))^4*(l/2) = t^4/(512*l^(3+4*η)) := by
  have hpow : (l^(1+η))^4 = l^(3+4*η)*l := by
    rw [← Real.rpow_mul_natCast hl.le,show (1+η)*(4:ℕ) = (3+4*η)+1 by push_cast; ring,
      Real.rpow_add hl,Real.rpow_one]
  rw [div_pow,mul_pow,hpow]
  have hne : l ≠ 0 := ne_of_gt hl
  have hpne : l^(3+4*η) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hl _)
  field_simp
  ring

theorem lower_fixed_eta {η : ℝ} (hη : 0<η) (hconstruction : PrimeConstruction η) :
    ∀ᶠ t : ℕ in atTop, (t:ℝ)^4/(512*(Real.log t)^(3+4*η)) < (ramsey 5 t:ℝ) := by
  obtain ⟨q₀,hq₀⟩ := hconstruction
  filter_upwards [conversion_scales η (q₀:ℝ)] with t ht
  obtain ⟨ht2,hlog,hscale,hscale2,hlogscale⟩ := ht
  let x : ℝ := (t:ℝ)/(4*(Real.log t)^(1+η))
  have hx : 2≤x := hscale2
  obtain ⟨q,hq,hxq,hqx⟩ := prime_in_interval hx
  have hq0 : q₀≤q := by exact_mod_cast (hscale.trans hxq.le)
  obtain ⟨G,hG,hI⟩ := hq₀ q hq0 hq
  have htp : 0<(t:ℝ) := by exact_mod_cast (show 0<t by omega)
  have hlp : 0<Real.log (t:ℝ) := by linarith
  have hpow1 : 1 ≤ (Real.log t)^(1+η) := Real.one_le_rpow hlog.le (by linarith)
  have hpowpos : 0<(Real.log t)^(1+η) := Real.rpow_pos_of_pos hlp _
  have h3x : 3*x≤3*(t:ℝ)/4 := by
    dsimp [x]
    have hh : (t:ℝ)/(4*(Real.log t)^(1+η)) ≤ (t:ℝ)/4 :=
      div_le_div_of_nonneg_left htp.le (by norm_num) (by linarith)
    linarith
  have hqt : (q:ℝ)<t := hqx.trans_lt (by linarith)
  have hqp : 0<(q:ℝ) := by linarith
  have hlogq : 0<Real.log (q:ℝ) := Real.log_pos (by linarith)
  have hlogqt := Real.log_le_log hqp hqt.le
  have hkreal : (q:ℝ)*(Real.log q)^(1+η) ≤ (t:ℝ) := by
    calc
      _ ≤ (3*x)*(Real.log t)^(1+η) := mul_le_mul hqx
        (Real.rpow_le_rpow hlogq.le hlogqt (by linarith)) (by positivity) (by linarith)
      _ = 3*(t:ℝ)/4 := by dsimp [x]; field_simp
      _ ≤ t := by linarith
  have hkt : ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊ ≤ t := by
    exact_mod_cast (Nat.floor_le (mul_nonneg hqp.le (Real.rpow_nonneg hlogq.le _))).trans hkreal
  have lower := graph_lower (by omega : 1≤t) hkt G hG hI
  have lower' : (q:ℝ)^4*Real.log q < (ramsey 5 t:ℝ) :=
    (Nat.floor_lt (mul_nonneg (by positivity) hlogq.le)).mp lower
  have hxlog : Real.log t/2≤Real.log (q:ℝ) := hlogscale.trans (Real.log_le_log (by linarith) hxq.le)
  have hnum : x^4*(Real.log t/2) ≤ (q:ℝ)^4*Real.log q :=
    mul_le_mul (pow_le_pow_left₀ (by linarith) hxq.le _) hxlog (by positivity) (by positivity)
  rw [lower_expression_identity (t:ℝ) (Real.log t) η hlp] at hnum
  exact hnum.trans_lt lower'

theorem lower_arbitrary_slack
    (hconstruction : ∀ η : ℝ, 0<η → η<1/10 → PrimeConstruction η)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℕ in atTop, (t:ℝ)^4/Real.rpow (Real.log t) (3+ε) ≤ (ramsey 5 t:ℝ) := by
  let η := min (ε/8) (1/20)
  have hη : 0<η := lt_min (by linarith) (by norm_num)
  have hηhi : η<1/10 := (min_le_right _ _).trans_lt (by norm_num)
  have hdiff : 0<ε-4*η := by have hh := min_le_left (ε/8) (1/20); change η≤ε/8 at hh; linarith
  have hgrowth : Tendsto (fun t : ℕ => (Real.log t)^(ε-4*η)) atTop atTop :=
    (tendsto_rpow_atTop hdiff).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [lower_fixed_eta hη (hconstruction η hη hηhi),eventually_ge_atTop (2:ℕ),
    hgrowth.eventually (eventually_ge_atTop (512:ℝ))] with t ht ht2 h512
  have hl : 0<Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (show 1<t by omega))
  have hden : 512*(Real.log t)^(3+4*η) ≤ Real.rpow (Real.log t) (3+ε) := by
    have heq : (3+ε) = (ε-4*η)+(3+4*η) := by ring
    change _ ≤ (Real.log t)^(3+ε)
    conv_rhs => rw [heq,Real.rpow_add hl]
    exact mul_le_mul_of_nonneg_right h512 (Real.rpow_nonneg hl.le _)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans ht.le

end SharpRamseyFive

end OAI
