import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointAPFree
import OAI.LinearAlgebra.MatrixFields.Extraction.ComplexFiniteSeparation

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

private theorem scale_exists (K : ℕ) : ∃ n : ℕ, K ≤ 2 ^ (n ^ 2) := by
  refine ⟨K + 1, ?_⟩
  have hK : K < 2 ^ K := Nat.lt_pow_self (by decide : 1 < 2)
  exact hK.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

noncomputable def gridScale (K : ℕ) : ℕ := Nat.find (scale_exists K)

theorem population_le_scale (K : ℕ) : K ≤ 2 ^ ((gridScale K) ^ 2) :=
  Nat.find_spec (scale_exists K)

theorem previous_scale_lt_population {K : ℕ} (hn : 0 < gridScale K) :
    2 ^ ((gridScale K - 1) ^ 2) < K := by
  exact lt_of_not_ge (Nat.find_min (scale_exists K) (Nat.sub_lt hn (by decide)))

theorem scale_pos {K : ℕ} (hK : 1 < K) : 0 < gridScale K := by
  have h := population_le_scale K
  by_contra hn
  have hz : gridScale K = 0 := Nat.eq_zero_of_not_pos hn
  simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at h
  exact (not_le_of_gt hK) h

theorem scale_gt_of_population_gt {K n : ℕ} (hK : 2 ^ (n ^ 2) < K) :
    n < gridScale K := by
  by_contra hn
  have hscale : gridScale K ≤ n := Nat.le_of_not_gt hn
  have hp : 2 ^ ((gridScale K) ^ 2) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hscale 2)
  exact (not_le_of_gt hK) ((population_le_scale K).trans hp)

theorem gridScale_monotone : Monotone gridScale := by
  intro K L hKL
  exact Nat.find_min' (scale_exists K) (hKL.trans (population_le_scale L))

def gridDimension (K : ℕ) : ℕ := gridScale K + 4

def gridWidth (K : ℕ) : ℕ := 2 ^ (gridScale K + 2)

def gridGroupOrder (K : ℕ) : ℕ := (4 * gridWidth K) ^ gridDimension K

theorem gridDimension_pos (K : ℕ) : 0 < gridDimension K := by
  simp [gridDimension]

theorem gridWidth_ge_two (K : ℕ) : 2 ≤ gridWidth K := by
  simpa only [gridWidth, pow_one] using
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ gridScale K + 2))

private theorem dimension_le_power (n : ℕ) : n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 2 ^ (n + 2 + 1) = 2 ^ (n + 2) * 2 := pow_succ _ _
    have he : n + 1 + 2 = n + 2 + 1 := by omega
    rw [he, hp]
    omega

theorem grid_population_bound (K : ℕ) :
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
      gridWidth K ^ gridDimension K := by
  let n := gridScale K
  have hd : n + 4 ≤ 2 ^ (n + 2) := dimension_le_power n
  have hq : 0 < 2 ^ (n + 2) := by positivity
  have hcolorpos : 0 < (n + 4) * (2 ^ (n + 2)) ^ 2 := by positivity
  have hcolor : (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤ 2 ^ (3 * n + 7) := by
    calc
      (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤
          2 * ((n + 4) * (2 ^ (n + 2)) ^ 2) := by nlinarith
      _ ≤ 2 * (2 ^ (n + 2) * (2 ^ (n + 2)) ^ 2) := by gcongr
      _ = 2 ^ (3 * n + 7) := by
        rw [← pow_mul, ← pow_add, ← pow_succ']
        congr 1
        omega
  calc
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
        2 ^ (3 * n + 7) * 2 ^ (n ^ 2) :=
      Nat.mul_le_mul hcolor (population_le_scale K)
    _ = 2 ^ (3 * n + 7 + n ^ 2) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((n + 2) * (n + 4)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ = gridWidth K ^ gridDimension K := by
      simp only [gridWidth, gridDimension, n, pow_mul]

theorem gridGroupOrder_eq (K : ℕ) :
    gridGroupOrder K = 2 ^ ((gridScale K + 4) ^ 2) := by
  unfold gridGroupOrder gridWidth gridDimension
  have hb : 4 * 2 ^ (gridScale K + 2) = 2 ^ (gridScale K + 4) := by
    calc
      4 * 2 ^ (gridScale K + 2) = 2 ^ 2 * 2 ^ (gridScale K + 2) := by norm_num
      _ = 2 ^ (2 + (gridScale K + 2)) := (pow_add _ _ _).symm
      _ = 2 ^ (gridScale K + 4) := by congr 1; omega
  rw [hb, ← pow_mul, pow_two]

theorem gridGroupOrder_pos (K : ℕ) : 0 < gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  positivity

theorem population_le_gridGroupOrder (K : ℕ) : K ≤ gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  exact (population_le_scale K).trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_left (Nat.le_add_right (gridScale K) 4) 2))

theorem gridGroupOrder_monotone : Monotone gridGroupOrder := by
  intro K L hKL
  rw [gridGroupOrder_eq, gridGroupOrder_eq]
  exact Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (gridScale_monotone hKL) 4) 2)

theorem asymptotic_grid_tags_slices (K : ℕ) :
    ∃ tags : Finset (Grid (gridDimension K) (gridWidth K)), tags.card = K ∧
      (∃ radius : Fin (gridDimension K * gridWidth K ^ 2 + 1),
        ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid (gridDimension K) (gridWidth K)),
        slice.card = K ∧ ∃ level : Fin (gridDimension K * gridWidth K ^ 2 + 1),
          ∀ u ∈ slice, dotColor t u = level :=
  grid_tags_slices (grid_population_bound K) (grid_population_bound K)

theorem log_gridGroupOrder (K : ℕ) :
    Real.log (gridGroupOrder K : ℝ) = ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := by
  rw [gridGroupOrder_eq, Nat.cast_pow, Real.log_pow]
  norm_cast

theorem log_population_le_log_gridGroupOrder {K : ℕ} (hK : 0 < K) :
    Real.log (K : ℝ) ≤ Real.log (gridGroupOrder K : ℝ) := by
  exact Real.log_le_log (by exact_mod_cast hK)
    (by exact_mod_cast population_le_gridGroupOrder K)

theorem previous_scale_log_lt {K : ℕ} (hK : 1 < K) :
    ((gridScale K : ℝ) - 1) ^ 2 * Real.log 2 < Real.log (K : ℝ) := by
  have hn : 1 ≤ gridScale K := scale_pos hK
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((gridScale K - 1) ^ 2) := by positivity
  have hc : (2 : ℝ) ^ ((gridScale K - 1) ^ 2) < (K : ℝ) := by
    exact_mod_cast previous_scale_lt_population (scale_pos hK)
  have h := Real.log_lt_log hp hc
  simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_sub hn, Nat.cast_one] using h

theorem log_gridGroupOrder_le_of_scale {K : ℕ} {ε : ℝ}
    (hK : 1 < K) (hε : 0 ≤ ε)
    (hscale : 10 * (gridScale K : ℝ) + 15 ≤
      ε * ((gridScale K : ℝ) - 1) ^ 2) :
    Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly : ((gridScale K : ℝ) + 4) ^ 2 ≤
      (1 + ε) * ((gridScale K : ℝ) - 1) ^ 2 := by nlinarith
  calc
    Real.log (gridGroupOrder K : ℝ) =
        ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := log_gridGroupOrder K
    _ ≤ ((1 + ε) * ((gridScale K : ℝ) - 1) ^ 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hpoly hlog2.le
    _ = (1 + ε) * (((gridScale K : ℝ) - 1) ^ 2 * Real.log 2) := by ring
    _ ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_le_mul_of_nonneg_left (previous_scale_log_lt hK).le (by positivity)

private theorem scale_error_bound {n ε : ℝ} (hn : 2 ≤ n) (hε : 0 ≤ ε)
    (hlarge : 72 ≤ ε * n) : 10 * n + 15 ≤ ε * (n - 1) ^ 2 := by
  have hsq : n ^ 2 ≤ 4 * (n - 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hε
  have hlarge' := mul_le_mul_of_nonneg_right hlarge (by linarith : 0 ≤ n)
  nlinarith

theorem eventually_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (max 2 (72 / ε))
  refine eventually_atTop.2 ⟨2 ^ (m ^ 2) + 1, ?_⟩
  intro K hK
  have hKm : 2 ^ (m ^ 2) < K := by omega
  have hn := scale_gt_of_population_gt hKm
  have hnR : (m : ℝ) < (gridScale K : ℝ) := by exact_mod_cast hn
  have hm2 : 2 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmε : 72 / ε < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hnε : 72 ≤ ε * (gridScale K : ℝ) := by
    have hdiv : 72 / ε < (gridScale K : ℝ) := hmε.trans hnR
    have hmul := (div_lt_iff₀ hε).1 hdiv
    nlinarith
  have hKone : 1 < K := by
    have hp : 1 ≤ 2 ^ (m ^ 2) := Nat.one_le_pow _ _ (by decide)
    omega
  exact log_gridGroupOrder_le_of_scale hKone hε.le
    (scale_error_bound (by linarith) hε.le hnε)

theorem uniform_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) + C := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (eventually_log_gridGroupOrder_le hε)
  refine ⟨Real.log (gridGroupOrder K₀ : ℝ), Real.log_natCast_nonneg _, ?_⟩
  intro K
  by_cases hK : K₀ ≤ K
  · exact (hK₀ K hK).trans (le_add_of_nonneg_right (Real.log_natCast_nonneg _))
  · have horder : gridGroupOrder K ≤ gridGroupOrder K₀ :=
      gridGroupOrder_monotone (Nat.le_of_lt (Nat.lt_of_not_ge hK))
    have hpos : (0 : ℝ) < (gridGroupOrder K : ℝ) := by
      rw [gridGroupOrder_eq, Nat.cast_pow]
      positivity
    have hcast : (gridGroupOrder K : ℝ) ≤ (gridGroupOrder K₀ : ℝ) := by
      exact_mod_cast horder
    have hlog := Real.log_le_log hpos hcast
    have hnonneg : 0 ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_nonneg (by linarith) (Real.log_natCast_nonneg K)
    linarith

theorem tendsto_log_gridGroupOrder_div_log_population :
    Tendsto (fun K : ℕ => Real.log (gridGroupOrder K : ℝ) / Real.log (K : ℝ))
      atTop (nhds 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    refine eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hKone : 1 < K := by omega
    have hlog : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast hKone)
    have hle := log_population_le_log_gridGroupOrder (by omega : 0 < K)
    exact ha.trans_le ((le_div_iff₀ hlog).2 (by simpa using hle))
  · intro b hb
    have he : 0 < (b - 1) / 2 := by linarith
    filter_upwards [eventually_log_gridGroupOrder_le he,
      (eventually_atTop.2 ⟨2, fun K (hK : 2 ≤ K) => hK⟩)] with K hcost hK
    have hlog : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < K by omega))
    have hratio : Real.log (gridGroupOrder K : ℝ) / Real.log (K : ℝ) ≤
        1 + (b - 1) / 2 := (div_le_iff₀ hlog).2 hcost
    linarith

theorem tendsto_log_gridGroupOrder_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ N, 0 < K N) (hH : 0 ≤ H)
    (hpop : Tendsto (fun N => Real.log (K N : ℝ) / (N : ℝ)) atTop (nhds H)) :
    Tendsto (fun N => Real.log (gridGroupOrder (K N) : ℝ) / (N : ℝ))
      atTop (nhds H) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [(tendsto_order.1 hpop).1 a ha,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N haN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact haN.trans_le (div_le_div_of_nonneg_right
      (log_population_le_log_gridGroupOrder (hK N)) hNpos.le)
  · intro b hb
    let ε := (b - H) / (2 * (H + 1))
    have hdenom : 0 < 2 * (H + 1) := by linarith
    have hε : 0 < ε := div_pos (by linarith) hdenom
    obtain ⟨C, hC, hbound⟩ := uniform_log_gridGroupOrder_le hε
    have hεeq : ε * (2 * (H + 1)) = b - H := div_mul_cancel₀ _ hdenom.ne'
    have hlimitlt : (1 + ε) * H < b := by nlinarith
    have hconstant : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hupper : Tendsto
        (fun N : ℕ => (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ))
        atTop (nhds ((1 + ε) * H)) := by
      simpa using (hpop.const_mul (1 + ε)).add hconstant
    filter_upwards [(tendsto_order.1 hupper).2 b hlimitlt,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hbN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hle := div_le_div_of_nonneg_right (hbound (K N)) hNpos.le
    have heq : ((1 + ε) * Real.log (K N : ℝ) + C) / (N : ℝ) =
        (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ) := by ring
    rw [heq] at hle
    exact hle.trans_lt hbN

theorem log_nat_prod {I : Type*} (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (a i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod fun i hi =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha i hi))

theorem tendsto_log_nat_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, K i N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  have hsum := tendsto_finsetSum s hpop
  apply hsum.congr
  intro N
  rw [log_nat_prod s (fun i => K i N) (fun i hi => hK i hi N)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem tendsto_log_gridGroupOrder_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, gridGroupOrder (K i N) : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  exact tendsto_log_nat_prod_div_nat s (fun i hi N => gridGroupOrder_pos (K i N))
    (fun i hi => tendsto_log_gridGroupOrder_div_nat (hK i hi) (hH i hi) (hpop i hi))

theorem tendsto_log_nat_weighted_prod_div_nat {I : Type*} (s : Finset I) (w : I → ℕ)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, (K i N) ^ w i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, (w i : ℝ) * H i)) := by
  apply tendsto_log_nat_prod_div_nat s
  · intro i hi N
    exact pow_pos (hK i hi N) _
  · intro i hi
    simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using
      (hpop i hi).const_mul (w i : ℝ)

theorem tendsto_log_gridGroupOrder_weighted_prod_div_nat {I : Type*}
    (s : Finset I) (w : I → ℕ) {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto
      (fun N => Real.log ((∏ i ∈ s, gridGroupOrder (K i N) ^ w i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, (w i : ℝ) * H i)) := by
  exact tendsto_log_nat_weighted_prod_div_nat s w
    (fun i hi N => gridGroupOrder_pos (K i N))
    (fun i hi => tendsto_log_gridGroupOrder_div_nat (hK i hi) (hH i hi) (hpop i hi))

end MatrixMultiplication.Foundation.Separation






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
end

end MatrixAllFields

end OAI
