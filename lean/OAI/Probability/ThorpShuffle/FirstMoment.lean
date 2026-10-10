import OAI.Probability.ThorpShuffle.ReciprocalDegrees

namespace OAI

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

/-- The FIRST reciprocal degree moment of the concrete symmetric-group
irreducible family. `Specht.degree` is the actual complex dimension. -/
def reciprocalFirst (n : ℕ) : ℝ :=
  ∑ p : Specht.NShape n, (Specht.degree p : ℝ)⁻¹

/-- Exactly the non-row, non-column shapes: defect is size minus the maximum
of first row length and first column length. For size≥1 defect=0 precisely
for the row or column; at size=1 they coincide and are counted once. -/
def exceptionalFirst (n : ℕ) : ℝ :=
  ∑ p : Specht.NShape n, if 0 < Specht.defect p then (Specht.degree p : ℝ)⁻¹ else 0

/-- The supremum of the first reciprocal degree moments over positive sizes. Boundedness is proved in `reciprocal_degrees`. -/
def C1 : ℝ := sSup (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val))

open Thorp.Specht Thorp.Young
variable {n : ℕ}

lemma partition_first_exponential_decay :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * Nat.sqrt n) / (2 : ℝ) ^ (n / 16)) atTop (𝓝 0) := by
  have hc : 0 < Real.log 2 / 256 := by positivity
  have he := Thorp.Analysis.sqrt_log_small (Real.log 2 / 256) hc
  have ht : Tendsto (fun n : ℕ => Real.exp (-(Real.log 2 / 64) * n)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity))
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [he, eventually_ge_atTop 32] with n hn hn32
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n + 1) := by
    apply Real.le_sqrt_of_sq_le
    have hh : ((Nat.sqrt n : ℝ)^2) ≤ n := by exact_mod_cast (show (Nat.sqrt n)^2 ≤ n by simpa only [pow_two] using Nat.sqrt_le n)
    linarith
  have hdiv : (n : ℝ) / 32 ≤ (n / 16 : ℕ) := by
    have hh : n ≤ 32 * (n / 16) := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr (by exact_mod_cast (by omega : n ≤ n / 16 * 32))
  have hp : 2 * (Nat.sqrt n : ℝ) * Real.log (n + 1) ≤ (Real.log 2 / 64) * n := by
    have hl : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
    have h₁ := mul_le_mul_of_nonneg_right hs hl
    have h₂ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg ((n : ℝ) + 1))
    have hh := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have hc0 : 0 ≤ Real.log 2 / 256 := hc.le
    have hsq : Real.sqrt (n + 1) * ((Real.log 2 / 256) * Real.sqrt (n + 1)) = (Real.log 2 / 256) * (n + 1) := by calc
      _ = (Real.log 2 / 256) * (Real.sqrt (n + 1))^2 := by ring
      _ = _ := by rw [hh]
    rw [hsq] at h₂
    have h₃ := mul_le_mul_of_nonneg_left (show (n : ℝ) + 1 ≤ 2 * n by linarith) hc0
    linarith only [h₁, h₂, h₃]
  have hq : -(Real.log 2 / 64) * n ≥
      (2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 2 := by
    push_cast
    have hh := mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  calc
    _ = Real.exp ((2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr hq


def inverseFirst (p : NShape n) : ℝ := (degree p : ℝ)⁻¹

def slice (n u : ℕ) : ℝ := ∑ p : {p : NShape n // defect p = u}, inverseFirst p.val

def smallSlice (n u : ℕ) : ℝ := if 0 < u ∧ 4 * u ≤ n then slice n u else 0


lemma inverseFirst_nonneg (p : NShape n) : 0 ≤ inverseFirst p := by unfold inverseFirst; positivity
lemma slice_nonneg (n u : ℕ) : 0 ≤ slice n u := Finset.sum_nonneg (fun _ _ => inverseFirst_nonneg _)
lemma smallSlice_nonneg (n u : ℕ) : 0 ≤ smallSlice n u := by unfold smallSlice; split_ifs; exact slice_nonneg _ _; rfl

lemma slice_bound (n u : ℕ) (K : ℝ) (hK : 0 < K)
    (hk : ∀ p : NShape n, defect p = u → K ≤ degree p) :
    slice n u ≤ (2 : ℝ)^(u+1) / K := by
  have hI (p : {p : NShape n // defect p = u}) : inverseFirst p.val ≤ K⁻¹ := by
    exact inv_anti₀ hK (hk p.val p.property)
  calc
    _ ≤ ∑ _ : {p : NShape n // defect p = u}, K⁻¹ := Finset.sum_le_sum (fun p _ => hI p)
    _ = (Fintype.card {p : NShape n // defect p = u} : ℝ) * K⁻¹ := by simp
    _ ≤ (2 : ℝ)^(u+1) * K⁻¹ := mul_le_mul_of_nonneg_right (by exact_mod_cast defect_card_bound n u) (by positivity)
    _ = _ := rfl

lemma smallSlice_bound (n u : ℕ) : smallSlice n u ≤ 2 * (2 / 3 : ℝ)^u := by
  unfold smallSlice
  split_ifs with h
  · have hk : ∀ p : NShape n, defect p = u → (3 : ℝ)^u ≤ degree p := by
      intro p hp
      have hh := small_defect_degree p (by rw [hp]; exact h.2)
      rw [hp] at hh
      exact_mod_cast hh
    have hh := slice_bound n u (3^u) (by positivity) hk
    have he : (2 : ℝ)^(u+1) / 3^u = 2 * (2/3 :ℝ)^u := by
      rw [pow_succ, div_pow]
      ring
    exact hh.trans_eq he
  · positivity

lemma smallSlice_tendsto (u : ℕ) : Tendsto (fun n => smallSlice n u) atTop (𝓝 0) := by
  by_cases hu : 0 < u
  · have ht : Tendsto (fun n : ℕ => ((n - 2*u + 1 : ℕ) : ℝ)) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_sub_atTop_nat (2*u)))
    have hi : Tendsto (fun n : ℕ => (((n - 2*u + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ht
    have he := hi.const_mul ((2 : ℝ)^(u+1))
    rw [mul_zero] at he
    apply squeeze_zero' (Eventually.of_forall (fun n => smallSlice_nonneg n u)) _ he
    filter_upwards [eventually_ge_atTop (4*u)] with n hn
    rw [smallSlice, ite_eq_left ⟨hu, hn⟩]
    exact slice_bound n u _ (by positivity) (fun p hp => by
      have hh := fixed_defect_degree p (by rwa [hp]) (by rw [hp]; omega)
      rw [hp] at hh
      exact_mod_cast hh)
  · simp only [smallSlice, hu, false_and, ↓reduceIte]
    exact tendsto_const_nhds

lemma smallSum_tendsto : Tendsto (fun n => ∑' u, smallSlice n u) atTop (𝓝 0) := by
  have hs : Summable (fun u : ℕ => 2 * (2/3 : ℝ)^u) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(2/3 : ℝ)‖ < 1)).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence hs smallSlice_tendsto
    (Eventually.of_forall (fun n u => by rw [Real.norm_of_nonneg (smallSlice_nonneg n u)]; exact smallSlice_bound n u))
  simpa only [tsum_zero] using h

end Thorp.Current

namespace Thorp.Current
open scoped Classical
open Filter Topology Thorp.Young Thorp.Specht

lemma smallSlice_as_sum (n u : ℕ) :
    smallSlice n u = ∑ p : NShape n,
      if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0 := by
  unfold smallSlice slice
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = u)) (by simp), Finset.sum_filter]
  by_cases h : 0 < u ∧ 4 * u ≤ n
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : defect p = u
    · simp only [hp, h.1, h.2, true_and, ↓reduceIte]
    · simp only [hp, false_and, ↓reduceIte]
  · rw [ite_eq_right h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with hp
    · exact (h (by simpa only [hp.1] using hp.2)).elim
    · rfl

lemma smallSlice_support (n u : ℕ) (hu : u ∉ Finset.range (n+1)) : smallSlice n u = 0 := by
  unfold smallSlice
  have hh : ¬(0 < u ∧ 4*u ≤ n) := by have := (Finset.mem_range.not.mp hu); omega
  exact ite_eq_right hh

lemma smallSum_eq (n : ℕ) :
    (∑' u, smallSlice n u) = ∑ p : NShape n,
      if 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0 := by
  rw [tsum_eq_sum (smallSlice_support n)]
  simp_rw [smallSlice_as_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hd : defect p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by have := defect_add_longest p; omega)
  have he (u : ℕ) : (if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0) =
      if defect p = u then (if 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0) else 0 := by
    split_ifs <;> tauto
  simp only [he, Finset.sum_ite_eq, hd, ↓reduceIte]

lemma bulkSum_bound (n : ℕ) (hn : 0 < n) :
    (∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) ≤
      ((n : ℝ)+1)^(2*Nat.sqrt n) / (2:ℝ)^(n/16) := by
  have hb (p : NShape n) : (if n < 4*defect p then inverseFirst p else 0) ≤ ((2:ℝ)^(n/16))⁻¹ := by
    by_cases hp : n < 4*defect p
    · rw [ite_eq_left hp]
      have hh := bulk_degree p hn hp
      exact inv_anti₀ (by positivity) hh
    · rw [ite_eq_right hp]; positivity
  have hc : Fintype.card (NShape n) ≤ (n+1)^(2*Nat.sqrt n) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Nat.Partition (Fintype.card (Fin n))) ≤ _
    rw [Fintype.card_fin, ← Fintype.card_eq_nat_card]
    exact partition_count_le_sqrt_pow n
  calc
    _ ≤ ∑ _ : NShape n, ((2:ℝ)^(n/16))⁻¹ := Finset.sum_le_sum (fun p _ => hb p)
    _ = (Fintype.card (NShape n) : ℝ) * ((2:ℝ)^(n/16))⁻¹ := by simp
    _ ≤ ((n:ℝ)+1)^(2*Nat.sqrt n) * ((2:ℝ)^(n/16))⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := rfl

lemma exceptionalFirst_split (n : ℕ) : exceptionalFirst n =
    (∑' u, smallSlice n u) + (∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) := by
  unfold exceptionalFirst
  change (∑ p : NShape n, if 0 < defect p then inverseFirst p else 0) = _
  rw [smallSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all
  all_goals omega

/-- The contribution of positive-defect Specht modules tends to zero. -/
theorem exceptionalFirst_tendsto : Tendsto exceptionalFirst atTop (𝓝 0) := by
  have hb : Tendsto (fun n => ∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun p _ => by split_ifs; exact inverseFirst_nonneg p; rfl)))
      ((eventually_gt_atTop 0).mono (fun n hn => bulkSum_bound n hn)) Thorp.Current.partition_first_exponential_decay
  have he : exceptionalFirst = (fun n => (∑' u, smallSlice n u) + ∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) := funext exceptionalFirst_split
  rw [he]
  simpa only [zero_add] using smallSum_tendsto.add hb

end Thorp.Current

namespace Thorp.Current
open scoped Classical
open Thorp.Specht Filter Topology

lemma reciprocalFirst_nonneg (n : ℕ) : 0 ≤ reciprocalFirst n :=
  Finset.sum_nonneg (fun _p _ => inv_nonneg.mpr (Nat.cast_nonneg _))

lemma full_reciprocalFirst_bound (n : ℕ) :
    reciprocalFirst n ≤ 2 + exceptionalFirst n := by
  have hzero : slice n 0 ≤ 2 := by
    have h := slice_bound n 0 1 (by norm_num)
      (fun p _ => by exact_mod_cast degree_pos p)
    norm_num at h
    exact h
  have he : reciprocalFirst n = slice n 0 + exceptionalFirst n := by
    unfold slice
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = 0))
      (by simp), Finset.sum_filter]
    unfold exceptionalFirst reciprocalFirst
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    change inverseFirst p = _
    by_cases hp : defect p = 0
    · simp only [hp, lt_self_iff_false, ↓reduceIte, add_zero]
    · simp only [hp, Nat.pos_of_ne_zero hp, ↓reduceIte, zero_add]
      rfl
  rw [he]
  linarith

/-- Uniform first-moment bound, including the finitely many initial sizes. -/
lemma reciprocalFirst_bddAbove :
    BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) := by
  obtain ⟨B, hB⟩ := exceptionalFirst_tendsto.bddAbove_range
  refine ⟨2 + B, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (full_reciprocalFirst_bound n).trans (add_le_add le_rfl (hB ⟨n.val, rfl⟩))

lemma reciprocalFirst_le_C1 (n : ℕ) (hn : 1 ≤ n) : reciprocalFirst n ≤ C1 :=
  le_csSup reciprocalFirst_bddAbove ⟨⟨n, hn⟩, rfl⟩

lemma C1_nonneg : 0 ≤ C1 :=
  (reciprocalFirst_nonneg 1).trans (reciprocalFirst_le_C1 1 le_rfl)

theorem reciprocal_degrees :
    BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0) :=
  ⟨reciprocalFirst_bddAbove, reciprocalFirst_le_C1, exceptionalFirst_tendsto⟩

end Thorp.Current

end

end OAI
