import Mathlib
import OAI.Combinatorics.SharpRamsey.Bounds.SamplingParameter

namespace OAI

/-! Transfer of finite prime-field graph constructions to all sufficiently large orders. -/

section
namespace SharpLogRamsey.LowerTransfer
open Filter Real
open scoped Topology
noncomputable section

def PrimeConstruction (d : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 1/10 → ∀ᶠ q : ℕ in atTop,
    q.Prime → ∃ G : SimpleGraph (Fin ⌊(q:ℝ)^d * Real.log q⌋₊),
      G.CliqueFree (d+1) ∧ G.indepNum < ⌊(q:ℝ) * (Real.log q)^(1+η)⌋₊

theorem prime_interval (x : ℝ) (hx : 4 ≤ x) :
    ∃ q : ℕ, q.Prime ∧ x/4 ≤ q ∧ (q:ℝ) ≤ x := by
  let n := ⌊x/2⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr (by linarith)
  obtain ⟨q,hq,hnq,hqn⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  refine ⟨q,hq,?_,?_⟩
  · have hnf := Nat.lt_floor_add_one (x/2)
    have hnqr : (n:ℝ)+1 ≤ q := by exact_mod_cast hnq
    dsimp [n] at hnqr
    linarith
  · have hnf := Nat.floor_le (show 0≤x/2 by linarith)
    have hqn' : (q:ℝ) ≤ 2*n := by exact_mod_cast hqn
    dsimp [n] at hqn'
    linarith

theorem witness_bound (d q t : ℕ) (η : ℝ) (hd : 1≤d) (ht : 1≤t)
    (G : SimpleGraph (Fin ⌊(q:ℝ)^d * Real.log q⌋₊))
    (hG : G.CliqueFree (d+1))
    (hI : G.indepNum < ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊)
    (hqt : (q:ℝ)*(Real.log q)^(1+η) ≤ t) :
    (q:ℝ)^d * Real.log q < (ramsey (d+1) t : ℝ) := by
  have hk : ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊ ≤ t := Nat.floor_le_of_le hqt
  have hf : Gᶜ.CliqueFree t := by
    intro A hA
    have hi := G.isNClique_compl.mp hA
    have hle := hi.isIndepSet.card_le_indepNum
    have hc := hi.card_eq
    omega
  have hr := Foundation.order_lt_ramsey G (by omega) ht hG hf
  simp only [Fintype.card_fin] at hr
  have hr' : (⌊(q:ℝ)^d * Real.log q⌋₊ :ℝ)+1 ≤ ramsey (d+1) t := by
    exact_mod_cast hr
  exact (Nat.lt_floor_add_one _).trans_le hr'

theorem eventual_scale (η : ℝ) : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧
    4*t^((1:ℝ)/2) ≤ t/(Real.log t)^(1+η) := by
  have h := (isLittleO_log_rpow_rpow_atTop (1+η) (show 0<(1:ℝ)/2 by norm_num)).bound
    (show 0<(1:ℝ)/4 by norm_num)
  filter_upwards [h,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with t ht ht1 hl
  refine ⟨ht1,hl,?_⟩
  have ht0 : 0<t := by linarith
  have hl0 : 0<Real.log t := by linarith
  simp only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hl0 _),
    abs_of_pos (Real.rpow_pos_of_pos ht0 _)] at ht
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl0 _)).mpr
  have hp : t^((1:ℝ)/2)*t^((1:ℝ)/2)=t := by
    rw [←Real.rpow_add ht0]; norm_num
  nlinarith [mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg ht0.le ((1:ℝ)/2))]

theorem interval_bounds (η t q : ℝ) (hη : 0≤η) (ht : 1<t) (hl : 1≤Real.log t)
    (hscale : 4*t^((1:ℝ)/2) ≤ t/(Real.log t)^(1+η))
    (hqlo : (t/(Real.log t)^(1+η))/4 ≤ q)
    (hqhi : q ≤ t/(Real.log t)^(1+η)) :
    0<q ∧ Real.log t/2 ≤ Real.log q ∧
    q*(Real.log q)^(1+η) ≤ t := by
  have ht0 : 0<t := by linarith
  have hl0 : 0<Real.log t := by linarith
  have hp : 0<(Real.log t)^(1+η) := Real.rpow_pos_of_pos hl0 _
  have hqs : t^((1:ℝ)/2)≤q := by linarith
  have hq0 : 0<q := (Real.rpow_pos_of_pos ht0 _).trans_le hqs
  refine ⟨hq0,?_,?_⟩
  · have hlog := Real.log_le_log (Real.rpow_pos_of_pos ht0 _) hqs
    rw [Real.log_rpow ht0] at hlog
    linarith
  · have hden : 1≤(Real.log t)^(1+η) := Real.one_le_rpow hl (by linarith)
    have hqt : q≤t := hqhi.trans (div_le_self ht0.le hden)
    have hq1 : 1≤q := (Real.one_le_rpow ht.le (by norm_num)).trans hqs
    have hlogq : 0≤Real.log q := Real.log_nonneg hq1
    have hpow : (Real.log q)^(1+η)≤(Real.log t)^(1+η) :=
      Real.rpow_le_rpow hlogq (Real.log_le_log hq0 hqt) (by linarith)
    calc
      q*(Real.log q)^(1+η) ≤ q*(Real.log t)^(1+η) := mul_le_mul_of_nonneg_left hpow hq0.le
      _ ≤ (t/(Real.log t)^(1+η))*(Real.log t)^(1+η) :=
        mul_le_mul_of_nonneg_right hqhi hp.le
      _ = t := div_mul_cancel₀ _ hp.ne'

theorem scalar_lower (d : ℕ) (hd : 1≤d) (η ε t q : ℝ)
    (ht : 0≤t) (hl : 0<Real.log t) (hq : 0≤q)
    (hqlo : (t/(Real.log t)^(1+η))/4 ≤ q)
    (hlog : Real.log t/2 ≤ Real.log q)
    (habsorb : 2*(4:ℝ)^d ≤ (Real.log t)^(ε-(d:ℝ)*η)) :
    t^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) ≤ q^d*Real.log q := by
  let a : ℝ := ((d-1:ℕ):ℝ)+(d:ℝ)*η
  have he : (1+η)*(d:ℝ)=a+1 := by
    dsimp [a]
    rw [Nat.cast_sub hd]
    norm_num
    ring
  have he' : ((d-1:ℕ):ℝ)+ε=a+(ε-(d:ℝ)*η) := by dsimp [a];ring
  have hpow : ((Real.log t)^(1+η))^d=(Real.log t)^a*Real.log t := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le,he,Real.rpow_add_one hl.ne']
  have hp : 0<(Real.log t)^a := Real.rpow_pos_of_pos hl _
  have hp' : 0<(Real.log t)^(ε-(d:ℝ)*η) := Real.rpow_pos_of_pos hl _
  have h4 : 0<(4:ℝ)^d := by positivity
  have hden : ((Real.log t)^a)*(2*(4:ℝ)^d) ≤
      ((Real.log t)^a)*(Real.log t)^(ε-(d:ℝ)*η) :=
    mul_le_mul_of_nonneg_left habsorb hp.le
  calc
    t^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) =
        t^d/((Real.log t)^a*(Real.log t)^(ε-(d:ℝ)*η)) := by rw [he',Real.rpow_add hl]
    _ ≤ t^d/((Real.log t)^a*(2*(4:ℝ)^d)) :=
      div_le_div_of_nonneg_left (pow_nonneg ht _) (by positivity) hden
    _ = ((t/(Real.log t)^(1+η))/4)^d*(Real.log t/2) := by
      rw [div_pow,div_pow,hpow]
      field_simp
    _ ≤ q^d*Real.log q := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) hqlo _
      · exact hlog
      · positivity
      · exact pow_nonneg hq _

theorem lower_from_prime_construction (d : ℕ) (hd : 1≤d) (hprime : PrimeConstruction d)
    (η ε : ℝ) (hη : 0<η) (hη' : η<1/10) (hε : (d:ℝ)*η<ε) :
    ∀ᶠ t : ℕ in atTop,
      (t:ℝ)^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) ≤ (ramsey (d+1) t :ℝ) := by
  obtain ⟨q₀,hq₀⟩ := eventually_atTop.mp (hprime η hη hη')
  have hcoef : ∀ᶠ t : ℝ in atTop,
      2*(4:ℝ)^d ≤ (Real.log t)^(ε-(d:ℝ)*η) :=
    ((tendsto_rpow_atTop (by linarith : 0<ε-(d:ℝ)*η)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have hsqr : ∀ᶠ t : ℝ in atTop, max 1 (q₀:ℝ) ≤ t^((1:ℝ)/2) :=
    (tendsto_rpow_atTop (by norm_num : 0<(1:ℝ)/2)).eventually_ge_atTop _
  have H : ∀ᶠ t : ℝ in atTop,
      1<t ∧ 1≤Real.log t ∧ 4*t^((1:ℝ)/2)≤t/(Real.log t)^(1+η) ∧
        max 1 (q₀:ℝ)≤t^((1:ℝ)/2) ∧
          2*(4:ℝ)^d≤(Real.log t)^(ε-(d:ℝ)*η) := by
    filter_upwards [eventual_scale η,hsqr,hcoef] with t ht hs hc
    exact ⟨ht.1,ht.2.1,ht.2.2,hs,hc⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually H] with t ht
  obtain ⟨ht1,hl,hs,hqmin,hcoef⟩ := ht
  have hx4 : 4 ≤ (t:ℝ)/(Real.log t)^(1+η) := by
    have := (le_max_left (1:ℝ) q₀).trans hqmin
    linarith
  obtain ⟨q,hq,hql,hqu⟩ := prime_interval _ hx4
  have hq₀' : q₀≤q := by
    have hreal : (q₀:ℝ)≤q := by
      have := (le_max_right (1:ℝ) q₀).trans hqmin
      linarith
    exact_mod_cast hreal
  obtain ⟨G,hG,hI⟩ := hq₀ q hq₀' hq
  obtain ⟨hqpos,hlog,hsize⟩ := interval_bounds η t q hη.le ht1 hl hs hql hqu
  have hr := witness_bound d q t η hd (by exact_mod_cast ht1.le) G hG hI hsize
  exact (scalar_lower d hd η ε t q (by positivity) (by linarith) hqpos.le hql hlog hcoef).trans hr.le

theorem all_epsilon_lower (d : ℕ) (hd : 1≤d) (hprime : PrimeConstruction d)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ t : ℕ in atTop,
      (t:ℝ)^d/(Real.log t)^(((d-1:ℕ):ℝ)+ε) ≤ (ramsey (d+1) t :ℝ) := by
  let η := min (1/20:ℝ) (ε/(2*(d:ℝ)))
  have hd0 : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη' : η<1/10 := (min_le_left _ _).trans_lt (by norm_num)
  have hηε : (d:ℝ)*η<ε := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (1/20:ℝ) (ε/(2*(d:ℝ)))) hd0.le
    have he : (d:ℝ)*(ε/(2*(d:ℝ)))=ε/2 := by field_simp
    rw [he] at h
    exact h.trans_lt (by linarith)
  exact lower_from_prime_construction d hd hprime η ε hη hη' hηε

end
end SharpLogRamsey.LowerTransfer

end

end OAI
