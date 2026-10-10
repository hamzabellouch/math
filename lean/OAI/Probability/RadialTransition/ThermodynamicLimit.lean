import OAI.Probability.RadialTransition.SpatialReplication

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem separated_box_limit {F : ℝ → ℝ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hF0 : ∀ s, 0 ≤ s → 0 ≤ F s)
    (hFC : ∀ s, 0 ≤ s → F s ≤ C * s ^ 3)
    (hrep : ∀ (s L : ℝ) (n : ℕ), 0 ≤ s → (n : ℝ) * (s + δ) ≤ L →
      (n : ℝ) ^ 3 * F s ≤ F L) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ C ∧
      Tendsto (fun L : ℝ => F L / L ^ 3) atTop (nhds p) ∧
      ∀ s, 0 ≤ s → F s / (s + δ) ^ 3 ≤ p := by
  let S : Set ℝ := {r | ∃ s : ℝ, 0 ≤ s ∧ r = F s / (s + δ) ^ 3}
  have hnon : S.Nonempty := ⟨_, 0, le_rfl, rfl⟩
  have hbound : ∀ s, 0 ≤ s → F s / (s + δ) ^ 3 ≤ C := by
    intro s hs
    apply (div_le_iff₀ (by positivity : 0 < (s + δ) ^ 3)).mpr
    calc
      F s ≤ C * s ^ 3 := hFC s hs
      _ ≤ C * (s + δ) ^ 3 := by gcongr; linarith
  have hbd : BddAbove S := ⟨C, by rintro r ⟨s, hs, rfl⟩; exact hbound s hs⟩
  let p : ℝ := sSup S
  have hpC : p ≤ C := csSup_le hnon (by rintro r ⟨s, hs, rfl⟩; exact hbound s hs)
  have hsp (s : ℝ) (hs : 0 ≤ s) : F s / (s + δ) ^ 3 ≤ p := le_csSup hbd ⟨s, hs, rfl⟩
  have hp0 : 0 ≤ p := (div_nonneg (hF0 0 le_rfl) (by positivity)).trans (hsp 0 le_rfl)
  refine ⟨p, hp0, hpC, ?_, hsp⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, ⟨s, hs, rfl⟩, har⟩ := (lt_csSup_iff hbd hnon).mp ha
    have hlim : Tendsto (fun L : ℝ => ((⌊L / (s + δ)⌋₊ : ℝ) / L) ^ 3 * F s)
        atTop (nhds (F s / (s + δ) ^ 3)) := by
      have hh := ((tendsto_nat_floor_mul_div_atTop (show 0 ≤ (s + δ)⁻¹ by positivity)).pow 3).mul_const (F s)
      simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hh
    filter_upwards [hlim.eventually_const_lt har, eventually_gt_atTop (0 : ℝ)] with L hlo hL
    have hn : (⌊L / (s + δ)⌋₊ : ℝ) * (s + δ) ≤ L :=
      (le_div_iff₀ (by positivity : 0 < s + δ)).mp (Nat.floor_le (by positivity))
    have hh := div_le_div_of_nonneg_right (hrep s L ⌊L / (s + δ)⌋₊ hs hn)
      (show 0 ≤ L ^ 3 by positivity)
    have heq : ((⌊L / (s + δ)⌋₊ : ℝ) / L) ^ 3 * F s =
        ((⌊L / (s + δ)⌋₊ : ℝ) ^ 3 * F s) / L ^ 3 := by ring
    exact hlo.trans_le (heq ▸ hh)
  · intro a ha
    have hlim : Tendsto (fun L : ℝ => p * (1 + δ * L⁻¹) ^ 3) atTop (nhds p) := by
      have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_inv_atTop_zero.const_mul δ)).pow 3
      simpa using hh.const_mul p
    filter_upwards [hlim.eventually_lt_const ha, eventually_gt_atTop (0 : ℝ)] with L hhi hL
    apply lt_of_le_of_lt _ hhi
    apply (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (L + δ) ^ 3)).mp (hsp L hL.le)
    calc
      F L ≤ p * (L + δ) ^ 3 := hh
      _ = p * (1 + δ * L⁻¹) ^ 3 * L ^ 3 := by field_simp

theorem grandPressure_exists {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (h : ℝ) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ Real.exp (β * B + t * h) / t ∧
      Tendsto (fun L : ℝ => Real.log (grandPartition φ t L β h) / (t * L ^ 3))
        atTop (nhds p) := by
  have hbnd (s : ℝ) (hs : 0 ≤ s) := grandPartition_bounds hφ hb hstable hs hβ t h
  obtain ⟨p, hp0, hpC, hlim, _⟩ := separated_box_limit
    (F := fun L => Real.log (grandPartition φ t L β h))
    (C := Real.exp (β * B + t * h)) (δ := 2) (Real.exp_pos _).le (by norm_num)
    (fun s hs => Real.log_nonneg (hbnd s hs).1)
    (fun s hs => by
      have hh := Real.log_le_log (show 0 < grandPartition φ t s β h by linarith [(hbnd s hs).1])
        (hbnd s hs).2
      simpa only [Real.log_exp, mul_comm] using hh)
    (fun s L n hs hn => by
      have hh := Real.log_le_log
        (pow_pos (show 0 < grandPartition φ t s β h by linarith [(hbnd s hs).1]) _)
        (grandPartition_replication hφ hb hstable hβ hs hc n hn t h)
      simpa only [Real.log_pow, Nat.cast_pow] using hh)
  refine ⟨p / t, div_nonneg hp0 ht.le, (div_le_div_of_nonneg_right hpC ht.le), ?_⟩
  simpa only [div_div, mul_comm] using hlim.div_const t

theorem exists_bounded_fill (k c E : ℕ) (hc : 0 < c) (hE : E ≤ k * c) :
    ∃ v : Fin k → ℕ, (∀ i, v i ≤ c) ∧ (∑ i, v i) = E ∧
      (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ E / c + 1 := by
  classical
  let r := E / c
  let a := E % c
  have ha : a < c := Nat.mod_lt _ hc
  have hdecomp : r * c + a = E := by
    dsimp [r, a]
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div E c
  have hr : r ≤ k := by
    have hh : r * c ≤ k * c := by omega
    exact (mul_le_mul_iff_left₀ hc).mp (by simpa [Nat.mul_comm] using hh)
  let v : Fin k → ℕ := fun i => (if (i : ℕ) < r then c else 0) +
    (if (i : ℕ) = r then a else 0)
  have hv (i : Fin k) : v i ≤ c := by
    dsimp [v]
    split_ifs <;> omega
  have hsum1 : (∑ i : Fin k, if (i : ℕ) < r then c else 0) = r * c := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, Fin.card_filter_val_lt, min_eq_right hr, nsmul_eq_mul, Nat.cast_id]
  have hsum2 : (∑ i : Fin k, if (i : ℕ) = r then a else 0) = a := by
    by_cases hr' : r < k
    · let j : Fin k := ⟨r, hr'⟩
      have hiff (i : Fin k) : (i : ℕ) = r ↔ i = j := by
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp_rw [hiff]
      simp
    · have he : r = k := by omega
      have ha0 : a = 0 := by rw [he] at hdecomp; omega
      simp [ha0]
  have hcard : (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ r + 1 := by
    have hsub : Finset.univ.filter (fun i => v i ≠ 0) ⊆
        Finset.univ.filter (fun i : Fin k => (i : ℕ) < r + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hh
      have hge : r + 1 ≤ (i : ℕ) := by omega
      simp [v, show ¬(i : ℕ) < r by omega, show (i : ℕ) ≠ r by omega] at hi
    exact (Finset.card_le_card hsub).trans (by rw [Fin.card_filter_val_lt]; exact min_le_right _ _)
  refine ⟨v, hv, ?_, hcard⟩
  simp only [v, Finset.sum_add_distrib, hsum1, hsum2]
  exact hdecomp

theorem exists_integer_adjustment (k m q n : ℕ) (hm : 0 < m) (hmq : m < q)
    (hn : n ≤ k * q) {c : ℝ} (hc : 0 < c) (hcm : c ≤ (m : ℝ))
    (hcq : c ≤ ((q - m : ℕ) : ℝ)) :
    ∃ f : Fin k → ℕ, (∑ i, f i) = n ∧ (∀ i, f i ≤ q) ∧
      ((Finset.univ.filter (fun i => f i ≠ m)).card : ℝ) ≤
        |(n : ℝ) - (k : ℝ) * m| / c + 1 := by
  classical
  by_cases hmn : k * m ≤ n
  · have hE : n - k * m ≤ k * (q - m) := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.sub_le_sub_right hn _
    obtain ⟨v, hv, hsv, hcv⟩ := exists_bounded_fill k (q - m) (n - k * m)
      (Nat.sub_pos_of_lt hmq) hE
    let f : Fin k → ℕ := fun i => m + v i
    have hs : (∑ i, f i) = n := by
      simp only [f, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, hsv]
      omega
    have he : (Finset.univ.filter (fun i => f i ≠ m)) =
        Finset.univ.filter (fun i => v i ≠ 0) := by
      ext i
      simp [f]
    refine ⟨f, hs, (fun i => by dsimp [f]; have := hv i; omega), ?_⟩
    rw [he]
    have hvreal : ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) ≤
        ((n - k * m) / (q - m) : ℕ) + 1 := by exact_mod_cast hcv
    have hdiv : (((n - k * m) / (q - m) : ℕ) : ℝ) ≤
        ((n - k * m : ℕ) : ℝ) / c := by
      apply Nat.cast_div_le.trans
      exact div_le_div_of_nonneg_left (by positivity) hc hcq
    have hdiff : ((n - k * m : ℕ) : ℝ) = |(n : ℝ) - (k : ℝ) * m| := by
      rw [Nat.cast_sub hmn, Nat.cast_mul, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hmn)
    rw [hdiff] at hdiv
    linarith
  · have hnkm : n ≤ k * m := by omega
    obtain ⟨v, hv, hsv, hcv⟩ := exists_bounded_fill k m (k * m - n) hm (Nat.sub_le _ _)
    let f : Fin k → ℕ := fun i => m - v i
    have hs : (∑ i, f i) = n := by
      dsimp [f]
      rw [Finset.sum_tsub_distrib _ (fun i _ => hv i), Finset.sum_const, hsv]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      omega
    have he : (Finset.univ.filter (fun i => f i ≠ m)) =
        Finset.univ.filter (fun i => v i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
      have hvi := hv i
      omega
    refine ⟨f, hs, (fun i => (Nat.sub_le _ _).trans hmq.le), ?_⟩
    rw [he]
    have hvreal : ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) ≤
        ((k * m - n) / m : ℕ) + 1 := by exact_mod_cast hcv
    have hdiv : (((k * m - n) / m : ℕ) : ℝ) ≤
        ((k * m - n : ℕ) : ℝ) / c := by
      apply Nat.cast_div_le.trans
      exact div_le_div_of_nonneg_left (by positivity) hc hcm
    have hdiff : ((k * m - n : ℕ) : ℝ) = |(n : ℝ) - (k : ℝ) * m| := by
      rw [Nat.cast_sub hnkm, Nat.cast_mul, abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (by exact_mod_cast hnkm)
    rw [hdiff] at hdiv
    linarith

theorem sum_changed_cost {ι : Type uIndex} [Fintype ι] (f : ι → ℕ) (m : ℕ)
    (H : ℕ → ℝ) {K : ℝ} (hm : |H m| ≤ K) (hf : ∀ i, |H (f i)| ≤ K) :
    (∑ i, H (f i)) ≤ Fintype.card ι * H m +
      2 * K * (Finset.univ.filter (fun i => f i ≠ m)).card := by
  classical
  have hh : ∀ i, H (f i) ≤ H m + if f i ≠ m then 2 * K else 0 := by
    intro i
    split_ifs with hi
    · linarith [(abs_le.mp (hf i)).2, (abs_le.mp hm).1]
    · simp only [not_not] at hi
      simp [hi]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  have he : (∑ i, if f i ≠ m then 2 * K else 0) =
      2 * K * (Finset.univ.filter (fun i => f i ≠ m)).card := by
    rw [← Finset.sum_filter, Finset.sum_const]
    simp only [nsmul_eq_mul]
    ring
  rwa [he] at hs

theorem finiteCanonical_replication {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β t s L : ℝ} (hβ : 0 ≤ β) (ht : 0 < t)
    (hs : 0 < s) (hL : 0 < L)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (n : ℕ)
    (hn : (n : ℝ) * (s + 2) ≤ L) (m : Fin (n ^ 3) → ℕ) :
    finiteCanonical φ t L (∑ j, m j) β ≤
      s ^ 3 / L ^ 3 * ∑ j, finiteCanonical φ t s (m j) β := by
  classical
  let e : (Fin 3 → Fin n) ≃ Fin (n ^ 3) := Fintype.equivFinOfCardEq (by simp)
  have hp := partition_replication hφ hb hβ hs.le hc n hn (m ∘ e)
  have hsum : (∑ j, (m ∘ e) j) = ∑ j, m j := e.sum_comp m
  have hprod : (∏ j, partition φ s ((m ∘ e) j) β) =
      ∏ j, partition φ s (m j) β := e.prod_comp (fun j => partition φ s (m j) β)
  rw [hsum, hprod] at hp
  have hpos : ∀ j ∈ (Finset.univ : Finset (Fin (n ^ 3))), 0 < partition φ s (m j) β :=
    fun j _ => partition_pos hφ hb hs _ _
  have hlog := Real.log_le_log (Finset.prod_pos hpos) hp
  rw [Real.log_prod (fun j hj => (hpos j hj).ne')] at hlog
  have hpoint (j : Fin (n ^ 3)) : Real.log (partition φ s (m j) β) =
      -(t * s ^ 3) * finiteCanonical φ t s (m j) β := by
    dsimp only [finiteCanonical]
    field_simp
  simp_rw [hpoint] at hlog
  rw [← Finset.mul_sum] at hlog
  change -Real.log (partition φ L (∑ j, m j) β) / (t * L ^ 3) ≤ _
  rw [div_le_iff₀ (mul_pos ht (pow_pos hL 3))]
  have he : (s ^ 3 / L ^ 3 * ∑ j, finiteCanonical φ t s (m j) β) * (t * L ^ 3) =
      t * s ^ 3 * ∑ j, finiteCanonical φ t s (m j) β := by field_simp
  rw [he]
  linarith

theorem finiteCanonical_adjustment {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β t s L : ℝ} (hβ : 0 ≤ β) (ht : 0 < t)
    (hs : 0 < s) (hL : 0 < L)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (b m q N : ℕ)
    (hbL : (b : ℝ) * (s + 2) ≤ L) (hm : 0 < m) (hmq : m < q)
    (hN : N ≤ b ^ 3 * q) {c K : ℝ} (hc0 : 0 < c) (hcm : c ≤ (m : ℝ))
    (hcq : c ≤ ((q - m : ℕ) : ℝ)) (hK : 0 ≤ K)
    (hcost : ∀ j ≤ q, |finiteCanonical φ t s j β| ≤ K) :
    finiteCanonical φ t L N β ≤ s ^ 3 / L ^ 3 *
      ((b : ℝ) ^ 3 * finiteCanonical φ t s m β +
        2 * K * (|(N : ℝ) - (b : ℝ) ^ 3 * m| / c + 1)) := by
  obtain ⟨f, hfN, hfq, hfc⟩ := exists_integer_adjustment (b ^ 3) m q N hm hmq hN hc0 hcm hcq
  have hr := finiteCanonical_replication hφ hb hβ ht hs hL hc b hbL f
  rw [hfN] at hr
  have hsum := sum_changed_cost f m (fun j => finiteCanonical φ t s j β)
    (hcost m hmq.le) (fun i => hcost (f i) (hfq i))
  simp only [Fintype.card_fin, Nat.cast_pow] at hsum hfc
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hsum.trans (by gcongr)

def thermodynamicFilter (d : ℝ) : Filter (ℝ × ℕ) :=
  Filter.comap Prod.fst atTop ⊓
    Filter.comap (fun z : ℝ × ℕ => (z.2 : ℝ) / z.1 ^ 3) (nhds d)

theorem thermodynamicFilter_side (d : ℝ) :
    Tendsto Prod.fst (thermodynamicFilter d) atTop := by
  exact tendsto_comap.mono_left inf_le_left

theorem thermodynamicFilter_density (d : ℝ) :
    Tendsto (fun z : ℝ × ℕ => (z.2 : ℝ) / z.1 ^ 3)
      (thermodynamicFilter d) (nhds d) := by
  exact tendsto_comap.mono_left inf_le_right

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (⌊d * L ^ 3⌋₊ : ℝ) / L ^ 3) atTop (nhds d) := by
  have hh := (tendsto_nat_floor_mul_div_atTop hd).comp (tendsto_pow_atTop (by norm_num : 3 ≠ 0))
  simpa only [Function.comp_def, mul_comm] using hh

theorem floor_tendsto_thermodynamicFilter {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d * L ^ 3⌋₊)) atTop (thermodynamicFilter d) := by
  apply tendsto_inf.mpr
  constructor
  · exact tendsto_comap_iff.mpr tendsto_id
  · exact tendsto_comap_iff.mpr (floor_density_tendsto hd)

theorem thermodynamicFilter_neBot {d : ℝ} (hd : 0 ≤ d) : NeBot (thermodynamicFilter d) :=
  (floor_tendsto_thermodynamicFilter hd).neBot

end RadialTransition

end

end OAI
