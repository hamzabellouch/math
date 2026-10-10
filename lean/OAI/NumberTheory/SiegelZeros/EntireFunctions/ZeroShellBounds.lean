import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.W04

theorem summable_dyadic_shell_majorant (C : ℝ) :
    Summable (fun k : ℕ => 2 * C * ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k) := by
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by norm_num)
  have hconstant := summable_geometric_two.mul_left (2 : ℝ)
  convert (hlinear.add hconstant).mul_left (2 * C) using 1
  ext k
  ring

theorem summable_inv_norm_sq_of_dyadic_count
    {ι : Type*} (ρ : ι → ℂ) (C : ℝ)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ,
      ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
        C * ((k : ℝ) + 1) * (2 : ℝ) ^ k) :
    Summable (fun i => 1 / ‖ρ i‖ ^ 2) := by
  classical
  have hex (i : ι) : ∃ k : ℕ, ‖ρ i‖ ≤ (2 : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖ρ i‖
    refine ⟨k, hk.le.trans ?_⟩
    exact_mod_cast (show k < 2 ^ k from Nat.lt_two_pow_self).le
  let level (i : ι) : ℕ := Nat.find (hex i)
  let shell (k : ℕ) : Set ι := {i | level i = k}
  have hupper (k : ℕ) : shell k ⊆ {i | ‖ρ i‖ ≤ (2 : ℝ) ^ k} := by
    intro i hi
    have h := Nat.find_spec (hex i)
    change level i = k at hi
    change ‖ρ i‖ ≤ (2 : ℝ) ^ level i at h
    simpa [hi] using h
  have hfin (k : ℕ) : (shell k).Finite :=
    (hfinite ((2 : ℝ) ^ k)).subset (hupper k)
  let (k : ℕ) : Fintype (shell k) := (hfin k).fintype
  have hpartition : ∀ i : ι, ∃! k : ℕ, i ∈ shell k := by
    intro i
    exact ⟨level i, rfl, fun k hk => hk.symm⟩
  apply (summable_partition (f := fun i => 1 / ‖ρ i‖ ^ 2)
    (fun i => by positivity) hpartition).2
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  rw [← summable_nat_add_iff 1]
  apply (summable_dyadic_shell_majorant C).of_nonneg_of_le
  · intro k
    exact tsum_nonneg (fun i => by positivity)
  · intro k
    have hnorm (i : shell (k + 1)) : (2 : ℝ) ^ k < ‖ρ i.val‖ := by
      have hi : level i.val = k + 1 := i.property
      apply lt_of_not_ge
      exact Nat.find_min (hex i.val) (by change k < level i.val; omega)
    have hpoint (i : shell (k + 1)) :
        1 / ‖ρ i.val‖ ^ 2 ≤ 1 / ((2 : ℝ) ^ k) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos (by positivity))
      exact pow_le_pow_left₀ (by positivity) (hnorm i).le 2
    have hcard : ((shell (k + 1)).ncard : ℝ) ≤
        C * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1) := by
      have hsub := Set.ncard_le_ncard (hupper (k + 1))
        (hfinite ((2 : ℝ) ^ (k + 1)))
      have hc := hcount (k + 1)
      have hcast : ((shell (k + 1)).ncard : ℝ) ≤
          ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ (k + 1)}.ncard : ℝ) := by
        exact_mod_cast hsub
      push_cast at hc
      linarith
    calc
      (∑' i : shell (k + 1), 1 / ‖ρ i.val‖ ^ 2) =
          ∑ i : shell (k + 1), 1 / ‖ρ i.val‖ ^ 2 := tsum_fintype _
      _ ≤ ∑ _i : shell (k + 1), 1 / ((2 : ℝ) ^ k) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = ((shell (k + 1)).ncard : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        ring
      _ ≤ (C * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1)) /
          ((2 : ℝ) ^ k) ^ 2 :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = 2 * C * ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k := by
        rw [div_pow, one_pow, pow_succ]
        field_simp

theorem summable_inv_norm_sq_of_nonzero_dyadic_count
    {ι : Type*} (ρ : ι → ℂ) (_hnonzero : ∀ i, ρ i ≠ 0) (C : ℝ)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ,
      ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
        C * ((k : ℝ) + 1) * (2 : ℝ) ^ k) :
    Summable (fun i => 1 / ‖ρ i‖ ^ 2) :=
  summable_inv_norm_sq_of_dyadic_count ρ C hfinite hcount

end WeightedTorusJets.W04

end

end

section

noncomputable section
open scoped BigOperators
open Filter

namespace WeightedTorusJets.W48

private theorem exists_dyadic_bound {ι : Type*} (ρ : ι → ℂ) (K : ℕ) (i : ι) :
    ∃ n : ℕ, ‖ρ i‖ ≤ (2 : ℝ) ^ (K + n + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ‖ρ i‖
  refine ⟨n, hn.le.trans ?_⟩
  have hnat : n ≤ 2 ^ (K + n + 1) :=
    (show n < 2 ^ n from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact_mod_cast hnat

def dyadicShellIndex {ι : Type*} (ρ : ι → ℂ) (K : ℕ) (i : ι) : ℕ :=
  Nat.find (exists_dyadic_bound ρ K i)

theorem dyadicShell_upper {ι : Type*} (ρ : ι → ℂ) (K : ℕ) (i : ι) :
    ‖ρ i‖ ≤ (2 : ℝ) ^ (K + dyadicShellIndex ρ K i + 1) :=
  Nat.find_spec (exists_dyadic_bound ρ K i)

theorem dyadicShell_lower {ι : Type*} (ρ : ι → ℂ) (K : ℕ) (i : ι)
    (hi : (2 : ℝ) ^ K < ‖ρ i‖) :
    (2 : ℝ) ^ (K + dyadicShellIndex ρ K i) < ‖ρ i‖ := by
  cases hn : dyadicShellIndex ρ K i with
  | zero => simpa only [hn, Nat.add_zero] using hi
  | succ n =>
    have hmin := Nat.find_min (exists_dyadic_bound ρ K i)
      (show n < Nat.find (exists_dyadic_bound ρ K i) by
        change n < dyadicShellIndex ρ K i
        omega)
    simpa only [hn, Nat.succ_eq_add_one, Nat.add_assoc] using lt_of_not_ge hmin

private theorem finite_count_le {ι : Type*} (ρ : ι → ℂ) (C : ℝ)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k)
    (s : Finset ι) (k : ℕ) (hs : ∀ i ∈ s, ‖ρ i‖ ≤ (2 : ℝ) ^ k) :
    (s.card : ℝ) ≤ C * ((k : ℝ) + 1) * (2 : ℝ) ^ k := by
  have hn := Set.ncard_le_ncard (show (s : Set ι) ⊆ {i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}
    from fun i hi => hs i hi) (hfinite _)
  simp only [Set.ncard_coe_finset] at hn
  exact (show (s.card : ℝ) ≤ ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ)
    by exact_mod_cast hn).trans (hcount k)

theorem finite_shell_reciprocal_le {ι : Type*} (ρ : ι → ℂ) (C : ℝ)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k)
    (s : Finset ι) (k : ℕ)
    (hlo : ∀ i ∈ s, (2 : ℝ) ^ k ≤ ‖ρ i‖)
    (hhi : ∀ i ∈ s, ‖ρ i‖ ≤ (2 : ℝ) ^ (k + 1)) :
    ∑ i ∈ s, 1 / ‖ρ i‖ ≤ 2 * C * ((k : ℝ) + 2) := by
  have hc := finite_count_le ρ C hfinite hcount s (k + 1) hhi
  push_cast at hc
  simp only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] at hc
  calc
    _ ≤ ∑ _i ∈ s, 1 / (2 : ℝ) ^ k := Finset.sum_le_sum fun i hi =>
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (hlo i hi)
    _ = (s.card : ℝ) / (2 : ℝ) ^ k := by simp [div_eq_mul_inv]
    _ ≤ (C * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1)) / (2 : ℝ) ^ k :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

theorem finite_shell_inverse_square_le {ι : Type*} (ρ : ι → ℂ) (C : ℝ)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k)
    (s : Finset ι) (k : ℕ)
    (hlo : ∀ i ∈ s, (2 : ℝ) ^ k ≤ ‖ρ i‖)
    (hhi : ∀ i ∈ s, ‖ρ i‖ ≤ (2 : ℝ) ^ (k + 1)) :
    ∑ i ∈ s, 1 / ‖ρ i‖ ^ 2 ≤ 2 * C * ((k : ℝ) + 2) / (2 : ℝ) ^ k := by
  have hc := finite_count_le ρ C hfinite hcount s (k + 1) hhi
  push_cast at hc
  simp only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] at hc
  calc
    _ ≤ ∑ _i ∈ s, 1 / ((2 : ℝ) ^ k) ^ 2 := Finset.sum_le_sum fun i hi =>
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) (hlo i hi) 2)
    _ = (s.card : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by simp [div_eq_mul_inv]
    _ ≤ (C * ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1)) / ((2 : ℝ) ^ k) ^ 2 :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

theorem dyadic_tail_majorant_hasSum (C : ℝ) (K : ℕ) :
    HasSum (fun n : ℕ => 2 * C * ((K + n : ℕ) + 2 : ℝ) /
      (2 : ℝ) ^ (K + n)) (4 * C * ((K : ℝ) + 3) / (2 : ℝ) ^ K) := by
  have hg : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 :=
    hasSum_geometric_two
  have hn : HasSum (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) using 1
    norm_num
  convert ((hg.mul_left ((K : ℝ) + 2)).add hn).mul_left
    (2 * C / (2 : ℝ) ^ K) using 1
  · ext n
    push_cast
    rw [pow_add, div_pow, one_pow]
    field_simp
    ring
  · ring

theorem finite_tail_inverse_square_le {ι : Type*} (ρ : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k)
    (s : Finset ι) (K : ℕ) (hs : ∀ i ∈ s, (2 : ℝ) ^ K < ‖ρ i‖) :
    ∑ i ∈ s, 1 / ‖ρ i‖ ^ 2 ≤ 4 * C * ((K : ℝ) + 3) / (2 : ℝ) ^ K := by
  classical
  let level := dyadicShellIndex ρ K
  let t := s.image level
  have hmaps : ∀ i ∈ s, level i ∈ t := fun i hi => Finset.mem_image_of_mem level hi
  calc
    _ = ∑ n ∈ t, ∑ i ∈ s.filter (fun i => level i = n), 1 / ‖ρ i‖ ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ t, 2 * C * ((K + n : ℕ) + 2 : ℝ) / (2 : ℝ) ^ (K + n) := by
      apply Finset.sum_le_sum
      intro n hn
      apply finite_shell_inverse_square_le ρ C hfinite hcount _ (K + n)
      · intro i hi
        obtain ⟨his, hil⟩ := Finset.mem_filter.mp hi
        have hh := (dyadicShell_lower ρ K i (hs i his)).le
        change (2 : ℝ) ^ (K + level i) ≤ ‖ρ i‖ at hh
        simpa only [hil] using hh
      · intro i hi
        obtain ⟨_, hil⟩ := Finset.mem_filter.mp hi
        have hh := dyadicShell_upper ρ K i
        change ‖ρ i‖ ≤ (2 : ℝ) ^ (K + level i + 1) at hh
        simpa only [hil] using hh
    _ ≤ ∑' n : ℕ, 2 * C * ((K + n : ℕ) + 2 : ℝ) / (2 : ℝ) ^ (K + n) :=
      (dyadic_tail_majorant_hasSum C K).summable.sum_le_tsum t (fun n _ => by positivity)
    _ = _ := (dyadic_tail_majorant_hasSum C K).tsum_eq

theorem tail_inverse_square_le {ι : Type*} (ρ : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k) (K : ℕ) :
    ∑' i : {i // (2 : ℝ) ^ K < ‖ρ i‖}, 1 / ‖ρ i.val‖ ^ 2 ≤
      4 * C * ((K : ℝ) + 3) / (2 : ℝ) ^ K := by
  classical
  apply Real.tsum_le_of_sum_le (fun i => by positivity)
  intro s
  have h := finite_tail_inverse_square_le ρ C hC hfinite hcount
    (s.image Subtype.val) K (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.property)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
  exact h

theorem finite_near_reciprocal_le {ι : Type*} (ρ : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k)
    (s : Finset ι) (L : ℕ) (hs : ∀ i ∈ s, ‖ρ i‖ ≤ (2 : ℝ) ^ L) :
    ∑ i ∈ s, 1 / ‖ρ i‖ ≤
      (∑ i ∈ (hfinite 1).toFinset, 1 / ‖ρ i‖) +
        2 * C * (L : ℝ) * ((L : ℝ) + 1) := by
  classical
  let small := s.filter (fun i => ‖ρ i‖ ≤ 1)
  let outer := s.filter (fun i => ¬ ‖ρ i‖ ≤ 1)
  let level := dyadicShellIndex ρ 0
  have hsmall : ∑ i ∈ small, 1 / ‖ρ i‖ ≤
      ∑ i ∈ (hfinite 1).toFinset, 1 / ‖ρ i‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact (hfinite 1).mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    · intro i _ _
      positivity
  have hmaps : ∀ i ∈ outer, level i ∈ Finset.range L := by
    intro i hi
    obtain ⟨his, hiout⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range]
    by_contra h
    have hn := dyadicShell_lower ρ 0 i (by simpa using lt_of_not_ge hiout)
    have hp : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ level i :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt h)
    simp only [Nat.zero_add] at hn
    exact (not_lt_of_ge (hs i his)) (hp.trans_lt hn)
  have houter : ∑ i ∈ outer, 1 / ‖ρ i‖ ≤
      2 * C * (L : ℝ) * ((L : ℝ) + 1) := by
    calc
      _ = ∑ n ∈ Finset.range L,
          ∑ i ∈ outer.filter (fun i => level i = n), 1 / ‖ρ i‖ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ _n ∈ Finset.range L, 2 * C * ((L : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro n hn
        have hshell : ∑ i ∈ outer.filter (fun i => level i = n), 1 / ‖ρ i‖ ≤
            2 * C * ((n : ℝ) + 2) := by
          apply finite_shell_reciprocal_le ρ C hfinite hcount _ n
          · intro i hi
            obtain ⟨hiout, hil⟩ := Finset.mem_filter.mp hi
            have hi1 : (2 : ℝ) ^ 0 < ‖ρ i‖ := by
              simpa using lt_of_not_ge (Finset.mem_filter.mp hiout).2
            have hh := (dyadicShell_lower ρ 0 i hi1).le
            change (2 : ℝ) ^ (0 + level i) ≤ ‖ρ i‖ at hh
            simpa only [hil, Nat.zero_add] using hh
          · intro i hi
            have hil := (Finset.mem_filter.mp hi).2
            have hh := dyadicShell_upper ρ 0 i
            change ‖ρ i‖ ≤ (2 : ℝ) ^ (0 + level i + 1) at hh
            simpa only [hil, Nat.zero_add] using hh
        apply hshell.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hn' : n + 1 ≤ L := Finset.mem_range.mp hn
        have hnR : (n : ℝ) + 1 ≤ L := by exact_mod_cast hn'
        linarith
      _ = _ := by simp; ring
  have hsplit : (∑ i ∈ small, 1 / ‖ρ i‖) + (∑ i ∈ outer, 1 / ‖ρ i‖) =
      ∑ i ∈ s, 1 / ‖ρ i‖ := Finset.sum_filter_add_sum_filter_not s _ _
  linarith

theorem tail_inverse_square_le_of_threshold {ι : Type*} (ρ : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k)
    (K : ℕ) (R : ℝ) (hR : (2 : ℝ) ^ K ≤ R) :
    ∑' i : {i // R < ‖ρ i‖}, 1 / ‖ρ i.val‖ ^ 2 ≤
      4 * C * ((K : ℝ) + 3) / (2 : ℝ) ^ K := by
  classical
  apply Real.tsum_le_of_sum_le (fun i => by positivity)
  intro s
  have h := finite_tail_inverse_square_le ρ C hC hfinite hcount
    (s.image Subtype.val) K (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact hR.trans_lt j.property)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
  exact h

theorem dyadic_log_index (K : ℕ) :
    Real.log ((2 : ℝ) ^ K) / Real.log 2 = (K : ℝ) := by
  rw [Real.log_pow]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))

end WeightedTorusJets.W48

end

end

end SiegelZeros

end OAI
