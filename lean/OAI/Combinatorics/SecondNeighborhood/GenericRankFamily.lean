import OAI.Combinatorics.SecondNeighborhood.GenericRank
import OAI.Combinatorics.SecondNeighborhood.GenericRankMatching
import OAI.Combinatorics.SecondNeighborhood.GenericRankSupport
import OAI.Combinatorics.SecondNeighborhood.MatchingCover

namespace OAI

namespace SeymourSecondNeighborhood

open Bipartite

theorem rank_le_card_of_maximum_matching
    {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    {support : I → J → Prop} {matching : Finset (I × J)}
    (hmatching : IsMaximumMatching support matching) (D : Matrix I J K)
    (hD : ∀ i j, ¬ support i j → D i j = 0) : D.rank ≤ matching.card := by
  classical
  obtain ⟨rows, cols, hcover, hcard, _, _⟩ :=
    exists_vertexCover_card_eq_of_isMaximumMatching hmatching
  rw [← hcard]
  apply rank_le_vertexCover_card
  intro i j hij
  apply hcover i j
  by_contra hs
  exact hij (hD i j hs)

theorem rank_eq_card_of_maximum_matching_minor
    {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    {support : I → J → Prop} {matching : Finset (I × J)}
    [DecidableEq ↥matching]
    (hmatching : IsMaximumMatching support matching) (D : Matrix I J K)
    (hD : ∀ i j, ¬ support i j → D i j = 0)
    (hdet : (D.submatrix (fun e : ↥matching => e.1.1)
      (fun e : ↥matching => e.1.2)).det ≠ 0) : D.rank = matching.card := by
  apply le_antisymm (rank_le_card_of_maximum_matching hmatching D hD)
  calc
    matching.card = (D.submatrix (fun e : ↥matching => e.1.1)
        (fun e : ↥matching => e.1.2)).rank := by
      simpa only [Fintype.card_coe] using (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ D.rank := Matrix.rank_submatrix_le _ _ _

variable {σ κ τ K : Type*} [Field K] [Infinite K] [Fintype κ] [Fintype τ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

theorem exists_eval_maximal_support_rank
    (support : ∀ k, I k → J k → Prop) (label : ∀ k, I k → J k → σ)
    (hlabel : ∀ k i j i' j', support k i j → support k i' j' →
      label k i j = label k i' j' → i = i' ∧ j = j')
    (extra : τ → MvPolynomial σ K) (hextra : ∀ t, extra t ≠ 0) :
    ∃ a : σ → K, (∀ t, MvPolynomial.eval a (extra t) ≠ 0) ∧
      ∀ k (D : Matrix (I k) (J k) K),
        (∀ i j, ¬ support k i j → D i j = 0) →
        D.rank ≤ (evalPolynomialMatrix a
          (supportedVariableMatrix (R := K) (support k) (label k))).rank := by
  classical
  choose matching hmatching using fun k => exists_maximum_matching (support k)
  let row (k : κ) : ↥(matching k) → I k := fun e => e.1.1
  let col (k : κ) : ↥(matching k) → J k := fun e => e.1.2
  let matrix (k : κ) := supportedVariableMatrix (R := K) (support k) (label k)
  let minor (k : κ) := (matrix k).submatrix (row k) (col k)
  have hminor : ∀ k, (minor k).det ≠ 0 := by
    intro k
    apply det_matchingMinor_ne_zero
    · intro e
      exact (hmatching k).1.1 e.1 e.2
    · intro e f g h hef hgh heq
      obtain ⟨heg, hfh⟩ := hlabel k _ _ _ _ hef hgh heq
      exact ⟨Subtype.ext ((hmatching k).1.2.1 e.2 g.2 heg),
        Subtype.ext ((hmatching k).1.2.2 f.2 h.2 hfh)⟩
  let polynomials : Sum κ τ → MvPolynomial σ K :=
    Sum.elim (fun k => (minor k).det) extra
  have hpolynomials : ∀ t, polynomials t ≠ 0 := by
    intro t
    cases t with
    | inl k => exact hminor k
    | inr t => exact hextra t
  obtain ⟨a, ha⟩ := exists_eval_family_ne_zero polynomials hpolynomials
  refine ⟨a, fun t => ha (Sum.inr t), ?_⟩
  intro k D hD
  have hupper : D.rank ≤ (matching k).card :=
    rank_le_card_of_maximum_matching (hmatching k) D hD
  have hdet : ((evalPolynomialMatrix a (matrix k)).submatrix (row k) (col k)).det
      ≠ 0 := by
    rw [← evalPolynomialMatrix_submatrix, det_evalPolynomialMatrix]
    exact ha (Sum.inl k)
  have hlower : (matching k).card ≤ (evalPolynomialMatrix a (matrix k)).rank := by
    calc
      (matching k).card =
          ((evalPolynomialMatrix a (matrix k)).submatrix (row k) (col k)).rank := by
        simpa only [Fintype.card_coe] using (Matrix.rank_of_det_ne_zero hdet).symm
      _ ≤ (evalPolynomialMatrix a (matrix k)).rank :=
        Matrix.rank_submatrix_le _ (row k) (col k)
  exact hupper.trans hlower

end SeymourSecondNeighborhood

end OAI
