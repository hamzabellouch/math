import OAI.MeasureTheory.Falconer.Recursion.ProfileLipschitz

namespace OAI

/-! Values at the actual block depths, and the complementary descendant-count
values used by the Frostman profile lower bound. -/
namespace Falconer.Regularization

theorem finiteRampProfile_prefix (d c : ℕ → ℝ) {K k : ℕ} (hd : Antitone d) (hk : k ≤ K) :
    finiteRampProfile d c K (d 0)-finiteRampProfile d c K (d k) =
      ∑ j ∈ Finset.range k, c j*(d j-d (j+1)) := by
  classical
  have hr (j : ℕ) : intervalRamp (d (j+1)) (d j) (d 0)-
      intervalRamp (d (j+1)) (d j) (d k) = if j < k then d j-d (j+1) else 0 := by
    unfold intervalRamp
    rw [min_eq_right (hd (Nat.zero_le j)),min_eq_right (hd (Nat.zero_le (j+1)))]
    by_cases hj : j < k
    · rw [ite_eq_left hj,min_eq_left (hd (Nat.le_of_lt hj)),
        min_eq_left (hd (Nat.succ_le_of_lt hj))]
      ring
    · rw [ite_eq_right hj,min_eq_right (hd (Nat.le_of_not_gt hj)),
        min_eq_right (hd (Nat.le_succ_of_le (Nat.le_of_not_gt hj)))]
      ring
  have he : finiteRampProfile d c K (d 0)-finiteRampProfile d c K (d k) =
      ∑ j ∈ Finset.range K, c j*(intervalRamp (d (j+1)) (d j) (d 0)-
        intervalRamp (d (j+1)) (d j) (d k)) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  rw [he]
  calc
    _ = ∑ j ∈ Finset.range K, if j < k then c j*(d j-d (j+1)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hr]
      split_ifs <;> simp
    _ = ∑ j ∈ Finset.range k, c j*(d j-d (j+1)) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter,Finset.mem_range]
      omega

noncomputable def terminalBranchingProfile (L : Finset (CellPath 2)) (F : CellPath 2 → List ℕ)
    (N B K : ℕ) (p : CellPath 2) (x : ℝ) : ℝ :=
  regularizedProfile L F N B K p N-regularizedProfile L F N B K p ((N : ℝ)*(1-x))

@[simp] theorem terminalBranchingProfile_zero (L : Finset (CellPath 2)) (F : CellPath 2 → List ℕ)
    (N B K : ℕ) (p : CellPath 2) : terminalBranchingProfile L F N B K p 0 = 0 := by
  simp [terminalBranchingProfile]

theorem terminalBranchingProfile_lipschitz {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (F : CellPath 2 → List ℕ) (B K : ℕ) (p : CellPath 2) :
    LipschitzWith 2 (terminalBranchingProfile L F N B K p) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat,terminalBranchingProfile]
  rw [show (regularizedProfile L F N B K p N-regularizedProfile L F N B K p ((N : ℝ)*(1-x)))-
      (regularizedProfile L F N B K p N-regularizedProfile L F N B K p ((N : ℝ)*(1-y))) =
      -(regularizedProfile L F N B K p ((N : ℝ)*(1-x))-
        regularizedProfile L F N B K p ((N : ℝ)*(1-y))) by ring,abs_neg]
  have hh : |(1-x)-(1-y)| = |x-y| := by
    rw [show (1-x)-(1-y) = -(x-y) by ring,abs_neg]
  have hb := (planarProfile_lipschitz hN hL F B K p).dist_le_mul (1-x) (1-y)
  simpa only [Real.dist_eq,NNReal.coe_ofNat,hh] using hb

end Falconer.Regularization

end OAI
