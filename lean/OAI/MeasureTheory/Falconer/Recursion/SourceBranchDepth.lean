import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchValidity

namespace OAI

namespace PlanarFalconer

def branchNonlowCount (label : ℕ → BranchLabel) (n : ℕ) : ℕ :=
  branchCount label n .high + branchCount label n .direct + branchCount label n .near +
    branchCount label n .far + branchCount label n .suffix

theorem branch_count_total (label : ℕ → BranchLabel) (n : ℕ) :
    branchNonlowCount label n + branchCount label n .low = n := by
  induction n with
  | zero => simp [branchNonlowCount,branchCount]
  | succ n ih =>
    simp only [branchNonlowCount] at *
    simp only [branchCount_succ]
    cases h : label n <;> simp <;> omega

theorem source_branch_count_bounds {A : ℕ → ℝ} {N n : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n) :
    (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig := by
  have hq := sourcePolicyBlock_pos hN hkap
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hstart := BranchState.valid_depths (b.valid 0 (Nat.zero_le _))
  have hS := b.suffix_total_decrease hq
  have hSR : (branchCount b.label n .suffix:ℝ)*(sourcePolicyBlock N kap:ℝ) ≤ N := by
    exact_mod_cast (show branchCount b.label n .suffix*sourcePolicyBlock N kap ≤ N by omega)
  have hblock := source_policy_block_lower N kap
  have hSb := mul_le_mul_of_nonneg_left hblock (Nat.cast_nonneg (branchCount b.label n .suffix))
  have hSbound : (branchCount b.label n .suffix:ℝ) ≤ 1/kap := by
    apply (le_div_iff₀ hkap).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [hSb.trans hSR]
  have hL := b.low_total_decrease hq
  have hLR : ((b.state 0).finish:ℝ) ≤ N := Nat.cast_le.mpr hstart.2
  have hLbound : (branchCount b.label n .low:ℝ) ≤ 1/sig := by
    apply (le_div_iff₀ hsig).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [show (0:ℝ) ≤ (b.state n).finish from Nat.cast_nonneg _]
  have hG := (b.representative_counts hq).1
  have hK := b.near_count hq hceil
  have hF := b.far_count
  have hB := source_representatives_real_bound A hN hkap hkap1
  have hnonlow : branchNonlowCount b.label n ≤
      2*(policyRepresentatives A N (sourcePolicyBlock N kap)).card + branchCount b.label n .suffix+2 := by
    dsimp only [branchNonlowCount]
    omega
  have hnonlowR : (branchNonlowCount b.label n:ℝ) ≤
      2*((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) +
        (branchCount b.label n .suffix:ℝ)+2 := by exact_mod_cast hnonlow
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  have hbound : (branchNonlowCount b.label n:ℝ) ≤ 20/kap := by
    have he : 20/kap = 20*(1/kap) := by ring
    have he2 : 2/kap = 2*(1/kap) := by ring
    rw [he2] at hB
    rw [he]
    linarith
  refine ⟨hbound,hLbound,?_⟩
  have ht : (branchNonlowCount b.label n:ℝ)+(branchCount b.label n .low:ℝ) = n := by
    exact_mod_cast branch_count_total b.label n
  linarith

theorem source_smoothing_reserve {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    1+20/kap+1/sig < (sourceSmoothingLevels sig kap:ℝ) := by
  have hceil : 100*(1/sig+1/kap)+100 ≤ (sourceSmoothingLevels sig kap:ℝ) := Nat.le_ceil _
  have he : 20/kap = 20*(1/kap) := by ring
  rw [he]
  have hk : 0 < 1/kap := by positivity
  have hs : 0 < 1/sig := by positivity
  linarith

theorem source_branch_index_bound {A : ℕ → ℝ} {N n : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n) (hi : (b.state 0).index = 0)
    {j : ℕ} (hj : j ≤ n) :
    ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧ (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  let c := b.initialSegment j hj
  have hc := source_branch_count_bounds hN hsig hkap hkap1 hceil c
  have hind := c.index_identity
  change (b.state j).index = (b.state 0).index + branchCount b.label j .suffix +
    branchCount b.label j .low + branchCount b.label j .far at hind
  rw [hi] at hind
  have hn : (b.state j).index ≤ branchNonlowCount b.label j + branchCount b.label j .low := by
    dsimp only [branchNonlowCount]
    omega
  have hnR : ((b.state j).index:ℝ) ≤ (branchNonlowCount b.label j:ℝ)+(branchCount b.label j .low:ℝ) := by
    exact_mod_cast hn
  change (branchNonlowCount b.label j:ℝ) ≤ _ ∧ (branchCount b.label j .low:ℝ) ≤ _ ∧ _ at hc
  have hb : ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig := by linarith [hc.1,hc.2.1]
  refine ⟨hb,?_⟩
  have hh := hb.trans_lt (source_smoothing_reserve hsig hkap)
  exact_mod_cast hh

theorem uniform_source_branch_depth {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig ∧
      ∀ j ≤ n, ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧
        (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := source_branch_count_bounds hNp hsig hkap hkap1 (h₀ N hN).1 b
  exact ⟨hc.1,hc.2.1,hc.2.2,fun j hj => source_branch_index_bound
    hNp hsig hkap hkap1 (h₀ N hN).1 b hi hj⟩

end PlanarFalconer

end OAI
