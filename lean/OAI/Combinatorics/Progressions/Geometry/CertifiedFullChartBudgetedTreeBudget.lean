import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {stageBudget : ℕ → ℝ}
variable {depth : ℕ} {p : ℝ}

omit [Fintype X] in
theorem BudgetedBranchTree.card_children_le_uniform
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hcaps : ∀ n, n < depth → stageBudget n ≤ p)
    (n : ℕ) (hn : n < depth) (H : State n) :
    (T.children n H).card ≤ fullChartFiniteTreeBranching depth p := by
  apply (T.card n hn H).trans
  apply Nat.ceil_mono
  exact Real.exp_le_exp.mpr (finiteStageTree_stage_log_le depth
    (fun k => fullChartStageCountConstant k 254) hp hη (hcaps n hn) hn)

omit [Fintype X] in
theorem BudgetedBranchTree.card_vertices_le_exp
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hcaps : ∀ n, n < depth → stageBudget n ≤ p) :
    (T.vertices.card : ℝ) ≤ Real.exp ((p + fullChartTreeExponent depth) ^ fullChartTreeExponent depth) := by
  have hcard := finiteGradedBranchVertices_card_le
    (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth (fullChartFiniteTreeBranching depth p)
    (fun n hn H _ => T.card_children_le_uniform hp hη hcaps n hn H)
  exact (Nat.cast_le.mpr hcard).trans
    ((Classical.choose_spec (exists_fullChartFiniteTree_budget depth)).2 p hp).2

theorem exists_bounded_budgeted_branch_tree (depth : ℕ)
    (hcaps : ∀ n, n < depth → stageBudget n ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hbudget : Bphase ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p,
      (T.vertices.card : ℝ) ≤
        Real.exp ((p + fullChartTreeExponent depth) ^ fullChartTreeExponent depth) := by
  obtain ⟨T⟩ := exists_budgeted_branch_tree (F := F) (b := b) (ω := ω) (hF := hF)
    (J := J) (fast := fast) (basis := basis) (lift := lift) (Z := Z)
    depth hcaps hp hbudget hX hm hJ hη hblocks hpoly hN
  exact ⟨T, T.card_vertices_le_exp hp hη (fun n hn => (hcaps n hn).trans hbudget)⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
