import Mathlib

namespace OAI

namespace Balanced.ProfileMomentCompactness
open scoped BigOperators
open Filter Topology

abbrev Index := ℕ × ℕ

def box (n : ℕ) : Finset Index :=
  Finset.range (n + 1) ×ˢ Finset.range (n + 1)

def weight (i : Index) : ℝ := i.1 + i.2

lemma weight_nonneg (i : Index) : 0 ≤ weight i := by
  unfold weight
  positivity

lemma weight_ge_of_not_mem_box {n : ℕ} {i : Index} (hi : i ∉ box n) :
    (n : ℝ) + 1 ≤ weight i := by
  simp only [box, Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hi
  unfold weight
  rcases hi with hi | hi
  · have hh : n + 1 ≤ i.1 + i.2 := by omega
    exact_mod_cast hh
  · have hh : n + 1 ≤ i.1 + i.2 := by omega
    exact_mod_cast hh

theorem finite_tail_bound (p : Index → ℝ) (M : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hM : ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M)
    (n : ℕ) (s : Finset Index) :
    ∑ i ∈ s \ box n, p i ≤ M / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hn).2
  calc
    (∑ i ∈ s \ box n, p i) * ((n : ℝ) + 1) =
        ∑ i ∈ s \ box n, ((n : ℝ) + 1) * p i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ s \ box n, weight i * p i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (weight_ge_of_not_mem_box (Finset.mem_sdiff.mp hi).2) (hp i)
    _ ≤ M := hM _

theorem box_mass_lower (p : Index → ℝ) (M : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (hM : ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M) (n : ℕ) :
    1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i := by
  have htotal : ∑' i, p i ≤ (∑ i ∈ box n, p i) + M / ((n : ℝ) + 1) := by
    apply Real.tsum_le_of_sum_le hp
    intro s
    have ht := finite_tail_bound p M hp hM n s
    have hi : ∑ i ∈ s ∩ box n, p i ≤ ∑ i ∈ box n, p i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by
        intro i hi hni
        exact hp i)
    have he : (∑ i ∈ s ∩ box n, p i) + (∑ i ∈ s \ box n, p i) = ∑ i ∈ s, p i := by
      exact Finset.sum_inter_add_sum_sdiff s (box n) p
    linarith
  rw [hs.tsum_eq] at htotal
  linarith

theorem hasSum_one_of_box_lower (p : Index → ℝ) (M : ℝ)
    (_hM : 0 ≤ M) (hp : ∀ i, 0 ≤ p i)
    (hs : ∀ s : Finset Index, ∑ i ∈ s, p i ≤ 1)
    (hb : ∀ n : ℕ, 1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i) :
    HasSum p 1 := by
  have hsum : Summable p := summable_of_sum_le hp hs
  have hle : ∑' i, p i ≤ 1 := Real.tsum_le_of_sum_le hp hs
  have hge : 1 ≤ ∑' i, p i := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
    have hnp : 0 < (n : ℝ) + 1 := by positivity
    have hsmall : M / ((n : ℝ) + 1) ≤ ε := by
      apply (div_le_iff₀ hnp).2
      have hh : M < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
      nlinarith
    have hpart : ∑ i ∈ box n, p i ≤ ∑' i, p i :=
      hsum.sum_le_tsum (box n) (by intro i hi; exact hp i)
    linarith [hb n]
  simpa [le_antisymm hle hge] using hsum.hasSum

def profiles (M : ℝ) : Set (Index → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧
    ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M}

lemma profiles_eq_closed_constraints (M : ℝ) (hM : 0 ≤ M) :
    profiles M = {p | (∀ i, 0 ≤ p i) ∧
      (∀ s : Finset Index, ∑ i ∈ s, p i ≤ 1) ∧
      (∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M) ∧
      ∀ n : ℕ, 1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i} := by
  ext p
  constructor
  · rintro ⟨hp, hs, hm⟩
    refine ⟨hp, ?_, hm, box_mass_lower p M hp hs hm⟩
    intro s
    calc
      ∑ i ∈ s, p i ≤ ∑' i, p i :=
        hs.summable.sum_le_tsum s (by intro i hi; exact hp i)
      _ = 1 := hs.tsum_eq
  · rintro ⟨hp, hs, hm, hb⟩
    exact ⟨hp, hasSum_one_of_box_lower p M hM hp hs hb, hm⟩

theorem isClosed_profiles (M : ℝ) (hM : 0 ≤ M) : IsClosed (profiles M) := by
  rw [profiles_eq_closed_constraints M hM]
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter ?_
  refine (isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum s fun i hi => continuous_apply i) continuous_const).inter ?_
  refine (isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum s fun i hi => continuous_const.mul (continuous_apply i))
    continuous_const).inter ?_
  exact isClosed_iInter fun n => isClosed_le continuous_const
    (continuous_finsetSum (box n) fun i hi => continuous_apply i)

theorem isCompact_profiles (M : ℝ) (hM : 0 ≤ M) : IsCompact (profiles M) := by
  apply (isCompact_univ_pi fun _ : Index =>
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).of_isClosed_subset
    (isClosed_profiles M hM)
  intro p hp i hi
  refine ⟨hp.1 i, ?_⟩
  have hh := hp.2.1.summable.sum_le_tsum ({i} : Finset Index)
    (show ∀ j, j ∉ ({i} : Finset Index) → 0 ≤ p j from fun j hj => hp.1 j)
  simpa [hp.2.1.tsum_eq] using hh

theorem exists_profile_subsequence (M : ℝ) (hM : 0 ≤ M)
    (p : ℕ → Index → ℝ) (hp : ∀ n, p n ∈ profiles M) :
    ∃ P ∈ profiles M, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (p ∘ φ) atTop (𝓝 P) :=
  (isCompact_profiles M hM).tendsto_subseq hp

theorem mem_profiles_iff (M : ℝ) (p : Index → ℝ) :
    p ∈ profiles M ↔ (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧
      Summable (fun i => weight i * p i) ∧
      (∑' i, weight i * p i) ≤ M := by
  constructor
  · rintro ⟨hp, hs, hm⟩
    have hw : ∀ i, 0 ≤ weight i * p i := fun i =>
      mul_nonneg (weight_nonneg i) (hp i)
    exact ⟨hp, hs, summable_of_sum_le hw hm, Real.tsum_le_of_sum_le hw hm⟩
  · rintro ⟨hp, hs, hw, hm⟩
    refine ⟨hp, hs, fun s => ?_⟩
    exact (hw.sum_le_tsum s (fun i hi =>
      mul_nonneg (weight_nonneg i) (hp i))).trans hm

theorem isCompact_probability_arrays (M : ℝ) (hM : 0 ≤ M) :
    IsCompact {p : (ℕ × ℕ) → ℝ | (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧
      Summable (fun i => ((i.1 : ℝ) + i.2) * p i) ∧
      (∑' i, ((i.1 : ℝ) + i.2) * p i) ≤ M} := by
  have he : {p : (ℕ × ℕ) → ℝ | (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧
      Summable (fun i => ((i.1 : ℝ) + i.2) * p i) ∧
      (∑' i, ((i.1 : ℝ) + i.2) * p i) ≤ M} = profiles M := by
    ext p
    exact (mem_profiles_iff M p).symm
  rw [he]
  exact isCompact_profiles M hM

theorem exists_coordinatewise_profile_subsequence (M : ℝ) (hM : 0 ≤ M)
    (p : ℕ → Index → ℝ) (hp : ∀ n, p n ∈ profiles M) :
    ∃ P ∈ profiles M, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun n => p (φ n) i) atTop (𝓝 (P i)) := by
  obtain ⟨P, hP, φ, hφ, ht⟩ := exists_profile_subsequence M hM p hp
  refine ⟨P, hP, φ, hφ, fun i => ?_⟩
  exact ((continuous_apply i).tendsto P).comp ht

end Balanced.ProfileMomentCompactness

end OAI
