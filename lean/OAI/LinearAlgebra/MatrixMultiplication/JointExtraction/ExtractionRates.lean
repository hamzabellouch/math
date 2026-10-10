import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.APFree
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointExtractionRates

open Filter
open scoped BigOperators Topology

def goodCount {Ω E : Type*} [Fintype E] (good : Ω → E → Prop) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (good ω)).card

def goodIncidence {Ω E : Type*} [Fintype Ω] (good : Ω → E → Prop) (e : E) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ω => good ω e)).card

theorem sum_goodCount_eq_sum_goodIncidence {Ω E : Type*} [Fintype Ω] [Fintype E]
    (good : Ω → E → Prop) :
    (∑ ω, goodCount good ω) = ∑ e, goodIncidence good e := by
  classical
  simp only [goodCount, goodIncidence, Finset.card_filter]
  exact Finset.sum_comm

theorem exists_goodCount_ge {Ω E : Type*} [Fintype Ω] [Nonempty Ω] [Fintype E]
    (good : Ω → E → Prop) (q : ℝ)
    (hinc : ∀ e, q * (Fintype.card Ω : ℝ) ≤ (goodIncidence good e : ℝ)) :
    ∃ ω, (Fintype.card E : ℝ) * q ≤ (goodCount good ω : ℝ) := by
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hinc e)
  have hdouble : (∑ ω, (goodCount good ω : ℝ)) =
      ∑ e, (goodIncidence good e : ℝ) := by
    exact_mod_cast sum_goodCount_eq_sum_goodIncidence good
  have havg : (∑ _ω : Ω, (Fintype.card E : ℝ) * q) ≤
      ∑ ω, (goodCount good ω : ℝ) := by
    rw [hdouble]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc,
      mul_comm, mul_left_comm] using hsum
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨ω, hω⟩

theorem exists_good_subfamily {Ω E : Type*} [Fintype E]
    (good : Ω → E → Prop) (ω : Ω) (K : ℕ) (hK : K ≤ goodCount good ω) :
    ∃ G : Finset E, G.card = K ∧ ∀ e ∈ G, good ω e := by
  classical
  obtain ⟨G, hG, hcard⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (good ω)) (by simpa only [goodCount] using hK)
  exact ⟨G, hcard, fun e he => (Finset.mem_filter.mp (hG he)).2⟩

theorem eventually_exists_good_subfamily {Ω E : ℕ → Type*}
    [∀ N, Fintype (E N)]
    (good : ∀ N, Ω N → E N → Prop) (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, ∃ ω : Ω N, K N ≤ goodCount (good N) ω) :
    ∀ᶠ N in atTop, ∃ (ω : Ω N) (G : Finset (E N)),
      G.card = K N ∧ ∀ e ∈ G, good N ω e := by
  filter_upwards [hK] with N hN
  obtain ⟨ω, hω⟩ := hN
  obtain ⟨G, hcard, hgood⟩ := exists_good_subfamily (good N) ω (K N) hω
  exact ⟨ω, G, hcard, hgood⟩

theorem incidence_lower_of_survival_and_loss {Ω E : Type*} [Fintype Ω]
    (survives bad : Ω → E → Prop) (e : E) (s ε : ℝ)
    (hs : s * (Fintype.card Ω : ℝ) ≤ (goodIncidence survives e : ℝ))
    (hb : (goodIncidence (fun ω e => survives ω e ∧ bad ω e) e : ℝ) ≤
      s * ε * (Fintype.card Ω : ℝ)) :
    s * (1 - ε) * (Fintype.card Ω : ℝ) ≤
      (goodIncidence (fun ω e => survives ω e ∧ ¬ bad ω e) e : ℝ) := by
  classical
  have hsplit : goodIncidence (fun ω e => survives ω e ∧ bad ω e) e +
      goodIncidence (fun ω e => survives ω e ∧ ¬ bad ω e) e =
      goodIncidence survives e := by
    simp only [goodIncidence, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hs : survives ω e <;> by_cases hb : bad ω e <;> simp [hs, hb]
  have hsplitR :
      (goodIncidence (fun ω e => survives ω e ∧ bad ω e) e : ℝ) +
        (goodIncidence (fun ω e => survives ω e ∧ ¬ bad ω e) e : ℝ) =
      (goodIncidence survives e : ℝ) := by
    exact_mod_cast hsplit
  nlinarith

theorem exists_goodCount_ge_half_survival {Ω E : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype E]
    (survives bad : Ω → E → Prop) (s ε : ℝ) (hs₀ : 0 ≤ s) (hε : ε ≤ 1 / 2)
    (hs : ∀ e, s * (Fintype.card Ω : ℝ) ≤ (goodIncidence survives e : ℝ))
    (hb : ∀ e, (goodIncidence (fun ω e => survives ω e ∧ bad ω e) e : ℝ) ≤
      s * ε * (Fintype.card Ω : ℝ)) :
    ∃ ω, (Fintype.card E : ℝ) * (s / 2) ≤
      (goodCount (fun ω e => survives ω e ∧ ¬ bad ω e) ω : ℝ) := by
  apply exists_goodCount_ge
  intro e
  have h := incidence_lower_of_survival_and_loss survives bad e s ε (hs e) (hb e)
  have hc : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε hs₀) hc
  nlinarith

theorem tendsto_polynomial_mul_exp_neg (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ d * Real.exp (-c * (N : ℝ)))
      atTop (𝓝 0) := by
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul d hc).tendsto_atTop_zero
  have hshift := (hbase.comp (tendsto_add_atTop_nat 1)).mul_const (Real.exp c)
  simp only [zero_mul, Function.comp_apply, Nat.cast_add, Nat.cast_one] at hshift
  convert hshift using 1
  ext N
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem eventually_error_le_half {error : ℕ → ℝ} (B : ℝ) (d : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ N in atTop,
      error N ≤ B * (((N : ℝ) + 1) ^ d * Real.exp (-c * (N : ℝ)))) :
    ∀ᶠ N in atTop, error N ≤ 1 / 2 := by
  have hlim := (tendsto_polynomial_mul_exp_neg d hc).const_mul B
  have hsmall : ∀ᶠ N : ℕ in atTop,
      B * (((N : ℝ) + 1) ^ d * Real.exp (-c * (N : ℝ))) < 1 / 2 := by
    simpa only [mul_zero] using (tendsto_order.1 hlim).2 (1 / 2) (by simp)
  filter_upwards [hbound, hsmall] with N hb hs
  exact hb.trans hs.le

theorem tendsto_log_one_sub_error_div_nat {error : ℕ → ℝ}
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto (fun N => Real.log (1 - error N) / (N : ℝ)) atTop (𝓝 0) := by
  have hone : Tendsto (fun N => 1 - error N) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub herror
  exact (hone.log one_ne_zero).div_atTop tendsto_natCast_atTop_atTop

def hashModulus (H : ℝ) (N : ℕ) : ℕ :=
  37 ^ (⌊(N : ℝ) * H / Real.log 37⌋₊ + 1)

theorem hashModulus_ge (H : ℝ) (N : ℕ) : 37 ≤ hashModulus H N := by
  simpa only [hashModulus, pow_one] using
    (Nat.pow_le_pow_right (by norm_num : 0 < 37)
      (show 1 ≤ ⌊(N : ℝ) * H / Real.log 37⌋₊ + 1 by omega))

theorem hashModulus_log_bounds {H : ℝ} (hH : 0 ≤ H) (N : ℕ) :
    (N : ℝ) * H ≤ Real.log (hashModulus H N : ℝ) ∧
      Real.log (hashModulus H N : ℝ) ≤ (N : ℝ) * H + Real.log 37 := by
  have hl : 0 < Real.log (37 : ℝ) := Real.log_pos (by norm_num)
  have harg : 0 ≤ (N : ℝ) * H / Real.log 37 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg N) hH) hl.le
  have hfloor := mul_le_mul_of_nonneg_right (Nat.floor_le harg) hl.le
  have hceil := mul_lt_mul_of_pos_right
    (Nat.lt_floor_add_one ((N : ℝ) * H / Real.log 37)) hl
  have hcancel : (N : ℝ) * H / Real.log 37 * Real.log 37 = (N : ℝ) * H :=
    div_mul_cancel₀ _ hl.ne'
  simp only [hashModulus, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

theorem tendsto_log_hashModulus_div_nat {H : ℝ} (hH : 0 ≤ H) :
    Tendsto (fun N => Real.log (hashModulus H N : ℝ) / (N : ℝ))
      atTop (𝓝 H) := by
  have hc : Tendsto (fun N : ℕ => Real.log 37 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => H + Real.log 37 / (N : ℝ)) atTop (𝓝 H) := by
    simpa only [add_zero] using hc.const_add H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    apply (le_div_iff₀ hNr).2
    nlinarith [(hashModulus_log_bounds hH N).1]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := div_le_div_of_nonneg_right (hashModulus_log_bounds hH N).2 hNr.le
    simpa only [add_div, mul_div_cancel_left₀ H hNr.ne'] using hb

theorem eventual_log_upper_of_error {degree : ℕ → ℕ} {error : ℕ → ℝ} {D : ℝ}
    (herror : Tendsto (fun N => error N / (N : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop,
      Real.log (degree N : ℝ) ≤ (N : ℝ) * D + error N)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η := by
  filter_upwards [hbound, (tendsto_order.1 herror).2 η hη,
    eventually_ge_atTop (1 : ℕ)] with N hb he hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := div_le_div_of_nonneg_right hb hNr.le
  rw [add_div, mul_div_cancel_left₀ D hNr.ne'] at hd
  linarith

theorem eventually_ratio_le_exp_neg_of_log_bounds {degree M : ℕ → ℕ} {D H c : ℝ}
    (hdegree : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < M N)
    (hM : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 H))
    (hc : c < H - D) :
    ∀ᶠ N in atTop, (degree N : ℝ) / (M N : ℝ) ≤ Real.exp (-c * (N : ℝ)) := by
  let η : ℝ := (H - D - c) / 3
  have hη : 0 < η := by dsimp [η]; linarith
  filter_upwards [hdegree η hη, hpos,
    (tendsto_order.1 hM).1 (H - η) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with N hd hp hm hN
  by_cases hz : degree N = 0
  · simp only [hz, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le
  have hdpos : (0 : ℝ) < degree N := by
    exact_mod_cast Nat.pos_of_ne_zero hz
  have hmpos : (0 : ℝ) < M N := by exact_mod_cast hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdu := (div_le_iff₀ hNr).mp hd
  have hml := (lt_div_iff₀ hNr).mp hm
  have hcoefficient : D - H + 2 * η ≤ -c := by dsimp [η]; linarith
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient hNr.le
  have hdiff : Real.log (degree N : ℝ) - Real.log (M N : ℝ) ≤
      -c * (N : ℝ) := by nlinarith
  calc
    _ = Real.exp (Real.log (degree N : ℝ) - Real.log (M N : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log hdpos, Real.exp_log hmpos]
    _ ≤ _ := Real.exp_le_exp.mpr hdiff

theorem eventually_degree_div_hashModulus_le_exp {degree : ℕ → ℕ} {D H c : ℝ}
    (hH : 0 ≤ H)
    (hdegree : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hc : c < H - D) :
    ∀ᶠ N in atTop, (degree N : ℝ) / (hashModulus H N : ℝ) ≤
      Real.exp (-c * (N : ℝ)) := by
  apply eventually_ratio_le_exp_neg_of_log_bounds hdegree _
    (tendsto_log_hashModulus_div_nat hH) hc
  exact Eventually.of_forall fun N =>
    lt_of_lt_of_le (by decide : 0 < 37) (hashModulus_ge H N)

theorem tendsto_sqrt_div_nat_of_div_nat {a : ℕ → ℝ} {A : ℝ}
    (ha : ∀ N, 0 ≤ a N)
    (h : Tendsto (fun N => a N / (N : ℝ)) atTop (𝓝 A)) :
    Tendsto (fun N => Real.sqrt (a N) / (N : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hp := h.sqrt.mul hinv.sqrt
  simp only [Real.sqrt_zero, mul_zero] at hp
  convert hp using 1
  ext N
  symm
  rw [Real.sqrt_div (ha N), Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one, div_mul_div_comm, mul_one, Real.mul_self_sqrt (Nat.cast_nonneg N)]

theorem tendsto_log_modularSet_card_div_nat {M : ℕ → ℕ} {H : ℝ}
    (hM : ∀ᶠ N in atTop, 2 ≤ M N)
    (hlog : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun N => Real.log ((JointAPFree.modularSet (M N)).card : ℝ) / (N : ℝ))
      atTop (𝓝 H) := by
  have hsqrt := tendsto_sqrt_div_nat_of_div_nat
    (fun N => Real.log_natCast_nonneg (M N)) hlog
  have hconst : Tendsto (fun N : ℕ => Real.log 3 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N =>
      (Real.log (M N : ℝ) - Real.log 3 -
        4 * Real.sqrt (Real.log (M N : ℝ))) / (N : ℝ))
      atTop (𝓝 H) := by
    have h := (hlog.sub hconst).sub (hsqrt.const_mul 4)
    simp only [mul_zero, sub_zero] at h
    apply h.congr
    intro N
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hlog
  · filter_upwards [hM] with N hN
    exact div_le_div_of_nonneg_right
      (JointAPFree.modularSet_log_card_lower_modulus hN) (Nat.cast_nonneg N)
  · filter_upwards [hM] with N hN
    exact div_le_div_of_nonneg_right
      (JointAPFree.modularSet_log_card_le_modulus hN) (Nat.cast_nonneg N)

theorem tendsto_log_yield_lower {T U M : ℕ → ℕ} {A B C : ℝ}
    (hT : Tendsto (fun N => Real.log (T N : ℝ) / (N : ℝ)) atTop (𝓝 A))
    (hU : Tendsto (fun N => Real.log (U N : ℝ) / (N : ℝ)) atTop (𝓝 B))
    (hM : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun N =>
      (Real.log (T N : ℝ) + Real.log (U N : ℝ) -
        2 * Real.log (M N : ℝ) - Real.log 2) / (N : ℝ))
      atTop (𝓝 (A + B - 2 * C)) := by
  have hconst : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := ((hT.add hU).sub (hM.const_mul 2)).sub hconst
  simp only [sub_zero] at h
  apply h.congr
  intro N
  ring

theorem exp_log_yield_lower {T U M : ℕ} (hT : 0 < T) (hU : 0 < U) (hM : 0 < M) :
    Real.exp (Real.log (T : ℝ) + Real.log (U : ℝ) -
        2 * Real.log (M : ℝ) - Real.log 2) =
      (T : ℝ) * ((U : ℝ) / (M : ℝ) ^ 2 / 2) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hTr,
    Real.exp_log hUr, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show 2 * Real.log (M : ℝ) = Real.log ((M : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hMr 2)]
  ring

theorem eventually_floor_exp_le_of_log_lower {Y : ℕ → ℕ} {L : ℕ → ℝ} {R : ℝ}
    (hL : Tendsto (fun N => L N / (N : ℝ)) atTop (𝓝 R))
    (hY : ∀ᶠ N in atTop, Real.exp (L N) ≤ (Y N : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ⌊Real.exp ((N : ℝ) * (R - ε))⌋₊ ≤ Y N := by
  filter_upwards [(tendsto_order.1 hL).1 (R - ε) (by linarith), hY,
    (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hrate hy hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hexp : Real.exp ((N : ℝ) * (R - ε)) ≤ (Y N : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hy
    have hm := (lt_div_iff₀ hNr).mp hrate
    nlinarith
  simpa only [Nat.floor_natCast] using Nat.floor_le_floor hexp

theorem eventually_exists_many_good
    {Ω E : ℕ → Type*} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    [∀ N, Fintype (E N)]
    (good : ∀ N, Ω N → E N → Prop) (U M : ℕ → ℕ) {A H : ℝ}
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N) ∧ 0 < U N ∧ 0 < M N)
    (hinc : ∀ᶠ N in atTop, ∀ e,
      ((U N : ℝ) / (M N : ℝ) ^ 2 / 2) * (Fintype.card (Ω N) : ℝ) ≤
        (goodIncidence (good N) e : ℝ))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    (hU : Tendsto (fun N => Real.log (U N : ℝ) / (N : ℝ)) atTop (𝓝 H))
    (hM : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 H))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ ω : Ω N,
      ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ≤ goodCount (good N) ω := by
  let L : ℕ → ℝ := fun N => Real.log (Fintype.card (E N) : ℝ) +
    Real.log (U N : ℝ) - 2 * Real.log (M N : ℝ) - Real.log 2
  have hL : Tendsto (fun N => L N / (N : ℝ)) atTop (𝓝 (A - H)) := by
    simpa only [L, show A + H - 2 * H = A - H by ring] using
      tendsto_log_yield_lower hE hU hM
  filter_upwards [hpos, hinc, (tendsto_order.1 hL).1 (A - H - ε) (by linarith),
    (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hp hi hr hN
  obtain ⟨ω, hω⟩ := exists_goodCount_ge (good N) _ hi
  refine ⟨ω, ?_⟩
  have heq := exp_log_yield_lower hp.1 hp.2.1 hp.2.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : Real.exp ((N : ℝ) * (A - H - ε)) ≤
      (goodCount (good N) ω : ℝ) := by
    calc
      _ ≤ Real.exp (L N) := Real.exp_le_exp.mpr (by
        have hm := (lt_div_iff₀ hNr).mp hr
        nlinarith)
      _ = _ := heq
      _ ≤ _ := hω
  simpa only [Nat.floor_natCast] using Nat.floor_le_floor he

theorem eventually_exists_many_good_explicit
    {Ω E : ℕ → Type*} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    [∀ N, Fintype (E N)]
    (good : ∀ N, Ω N → E N → Prop) {A H : ℝ} (hH : 0 ≤ H)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) * (Fintype.card (Ω N) : ℝ) ≤
        (goodIncidence (good N) e : ℝ))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ ω : Ω N,
      ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ≤ goodCount (good N) ω := by
  have hM : ∀ N, 2 ≤ hashModulus H N := fun N =>
    (by norm_num : 2 ≤ 37).trans (hashModulus_ge H N)
  have hr := tendsto_log_hashModulus_div_nat hH
  apply eventually_exists_many_good good
    (fun N => (JointAPFree.modularSet (hashModulus H N)).card) (hashModulus H)
    _ hinc hE (tendsto_log_modularSet_card_div_nat (Eventually.of_forall hM) hr) hr hε
  filter_upwards [hpos] with N hN
  exact ⟨hN, JointAPFree.modularSet_card_pos (hM N),
    lt_of_lt_of_le (by decide : 0 < 2) (hM N)⟩

theorem fixed_product_subexponential {I : Type*} (s : Finset I) (R : I → ℕ → ℕ)
    (hpos : ∀ i ∈ s, ∀ N, 0 < R i N)
    (hR : ∀ i ∈ s,
      Tendsto (fun N => Real.log (R i N : ℝ) / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, R i N : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    MatrixMultiplication.Foundation.Separation.tendsto_log_nat_prod_div_nat s hpos hR

theorem presence_replications_subexponential (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => Real.log ((2 ^ (3 * L N) : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have h := hL.const_mul (3 * Real.log 2)
  simp only [mul_zero] at h
  apply h.congr
  intro N
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

end MatrixMultiplication.JointExtractionRates

end

end OAI
