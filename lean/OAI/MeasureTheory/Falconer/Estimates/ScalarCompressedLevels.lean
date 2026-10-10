import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchTree

namespace OAI

/-! Consecutive original blocks collapse to a separated level. Its gap is
 controlled by the final original block, so prescribed porous endpoints
 supply the separation needed after bunching. -/
namespace Falconer.Regularization

 theorem scalar_branch_scale_mono {M : ℕ} {Q : Finset (CellPath 1)}
    (d k n : ℕ → ℕ) (hd : Monotone d)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    {i j : ℕ} (hij : i ≤ j) (hj : j < M) : n i ≤ n j := by
  rcases hij.eq_or_lt with heq | hij
  · subst i
    exact le_rfl
  · exact (hlevel i (hij.trans hj)).level_hi.trans
      ((hd (show i+1 ≤ j by omega)).trans (hlevel j hj).level_lo)

 theorem scalar_grouped_path_level {N M : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    {a b : ℕ} (hab : a < b) (hb : b ≤ M) :
    ScalarPathLevel Q (d a) (d b) (2^(∑ i ∈ Finset.Ico a b, k i))
      (6*(1/2:ℝ)^(n (b-1))) := by
  refine ⟨hd hab.le,?_,?_⟩
  · exact fun p hp => scalar_grouped_children_card Q d k hd M
      (fun i hi => (hlevel i hi).children_card) hab.le hb p hp
  · intro p hp
    apply scalar_grouped_children_separated hQ d k n hd hdN hlevel hab.le hb
    intro i hai hib hki
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (scalar_branch_scale_mono d k n hd hlevel (by omega : i ≤ b-1) (by omega)))
      (by norm_num)

def scalarCompressedBranch (e k : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (e j) (e (j+1)), k i

 theorem scalar_compressed_path_level {N M T : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T ≤ M) {j : ℕ} (hj : j < T) :
    ScalarPathLevel Q (d (e j)) (d (e (j+1))) (2^(scalarCompressedBranch e k j))
      (6*(1/2:ℝ)^(n (e (j+1)-1))) := by
  exact scalar_grouped_path_level hQ d k n hd hdN hlevel (he (Nat.lt_succ_self j))
    ((he.monotone (show j+1 ≤ T by omega)).trans heT)

 theorem scalar_compressed_group_separated {N M T : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T ≤ M)
    {a b : ℕ} (hab : a < b) (hb : b ≤ T) :
    ∀ p ∈ Q.image (List.take (d (e a))),
      ∀ u ∈ prefixChildren Q (d (e a)) (d (e b)) p,
      ∀ v ∈ prefixChildren Q (d (e a)) (d (e b)) p,
      u ≠ v → 6*(1/2:ℝ)^(n (e b-1)) ≤ |scalarPathCenter u-scalarPathCenter v| :=
  (scalar_grouped_path_level hQ d k n hd hdN hlevel (he hab)
    ((he.monotone hb).trans heT)).separated

end Falconer.Regularization

end OAI
