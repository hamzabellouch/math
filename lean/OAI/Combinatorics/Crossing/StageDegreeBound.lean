import OAI.Combinatorics.Crossing.NodeRankLoss
import OAI.Combinatorics.Crossing.RankMultiplicity

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
open scoped BigOperators
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem polynomial_columns_rank_le {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (b : Basis κ ℝ Z) (p : ρ → PolynomialModule ℝ Z) (k : ℕ)
    (hp : ∀ j, p j ∈ constrained U node Z k) (t : ℝ) :
    ((polynomialColumnMatrix b p).map (Polynomial.eval t)).rank ≤
      finrank ℝ (evaluationFiltration U node Z t k) := by
  let A := (polynomialColumnMatrix b p).map (Polynomial.eval t)
  have hcol : A.col = b.equivFun ∘ (fun j => eval t (p j)) := by
    funext j i
    exact polynomialColumnMatrix_eval b p t i j
  have hspan : span ℝ (Set.range (fun j => eval t (p j))) ≤ evaluationFiltration U node Z t k := by
    apply span_le.mpr
    rintro z ⟨j, rfl⟩
    exact ⟨⟨p j, hp j⟩, rfl⟩
  change A.rank ≤ _
  rw [Matrix.rank_eq_finrank_span_cols, hcol, Set.range_comp]
  calc
    _ ≤ finrank ℝ ((evaluationFiltration U node Z t k).map b.equivFun.toLinearMap) := by
      apply Submodule.finrank_mono
      apply span_le.mpr
      rintro z ⟨v, ⟨j, rfl⟩, rfl⟩
      exact ⟨eval t (p j), ⟨⟨p j, hp j⟩, rfl⟩, rfl⟩
    _ = _ := b.equivFun.finrank_map_eq _

theorem stage_degree_bound [Fintype ι] (U V : ι → Submodule ℝ W) (node : ι → ℝ)
    (hn : Function.Injective node) (hUV : ∀ i, Disjoint (U i) (V i))
    (tstar : ℝ) (htstar : ∀ i, node i ≠ tstar) (h : ℕ) :
    (∑ j, rankIncrement U node (V j) h) ≤
      ∑ e ∈ Finset.range (h+1), e * columnIncrement U node ⊤ tstar e := by
  let b := finBasis ℝ (⊤ : Submodule ℝ W)
  obtain ⟨p, d, r, hp, hr, hdt, hdeg⟩ := exists_adapted_minor U node ⊤ b tstar htstar h
  let M := (polynomialColumnMatrix b p).submatrix r id
  have hM : M.det ≠ 0 := by
    intro hz
    apply hdt
    change M.det.eval tstar = 0
    rw [hz, Polynomial.eval_zero]
  have hcard : Fintype.card (Fin (finrank ℝ (evaluationFiltration U node ⊤ tstar (h+1)))) =
      rankIncrement U node ⊤ h := by
    rw [Fintype.card_fin]
    exact finrank_eval_range U node ⊤ h tstar htstar
  have hp' : ∀ j, p j ∈ constrained U node ⊤ (h+1) := by
    intro j
    exact ⟨bounded_mono (hp j).1.1 (Nat.add_le_add_right (hp j).2 1), (hp j).1.2⟩
  have hfactor : ∀ j, (Polynomial.X-Polynomial.C (node j))^(rankIncrement U node (V j) h) ∣ M.det := by
    intro j
    have hnode := node_rank_loss U node (V j) j (hUV j) h tstar htstar
    rw [finrank_ambientEvalRange] at hnode
    have hcols := polynomial_columns_rank_le U node ⊤ b p (h+1) hp' (node j)
    have hminor := Matrix.rank_submatrix_le
      ((polynomialColumnMatrix b p).map (Polynomial.eval (node j))) r id
    have hbound : ((Polynomial.evalRingHom (node j)).mapMatrix M).rank ≤
        finrank ℝ (evaluationFiltration U node ⊤ (node j) (h+1)) :=
      hminor.trans hcols
    apply pow_dvd_det_of_rank_le
    rw [hcard]
    omega
  exact (sum_multiplicities_le_natDegree node hn (fun j => rankIncrement U node (V j) h)
    M.det hM hfactor).trans hdeg

end Zarankiewicz

end

end OAI
