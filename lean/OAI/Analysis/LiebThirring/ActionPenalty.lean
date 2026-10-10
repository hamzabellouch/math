import OAI.Analysis.LiebThirring.FieldPrimitive

namespace OAI

universe u35

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ActionProof
open Set Filter

/-- The compact penalty argument, with no convergence of
minimizers or chosen coefficients required. -/
lemma compact_penalty_bound {E : Type u35} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) (hzero : ∀ x ∈ K, g x = 0 → f x ≤ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ x ∈ K, f x - g x / ε ≤ η := by
  let S := K ∩ {x | η ≤ f x}
  have hS : IsCompact S := hK.inter_right (isClosed_le continuous_const hf)
  obtain ⟨F, hF⟩ := (hK.image hf).bddAbove
  by_cases hne : S.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    have hgy : 0 < g y := lt_of_le_of_ne (hg0 y hy.1) (by
      intro he
      have := hzero y hy.1 he.symm
      dsimp [S] at hy
      have hηy : η ≤ f y := hy.2
      linarith)
    have hF1 : 0 < max F 1 := lt_of_lt_of_le (by norm_num) (le_max_right F 1)
    refine ⟨g y / max F 1, div_pos hgy hF1, ?_⟩
    intro ε hε hε₀ x hx
    by_cases hfx : η ≤ f x
    · have hxy : g y ≤ g x := hmin ⟨hx, hfx⟩
      have hprod : ε * max F 1 ≤ g y := (le_div_iff₀ hF1).mp hε₀
      have hr : max F 1 ≤ g x / ε := (le_div_iff₀ hε).mpr (by nlinarith)
      have := (hF (Set.mem_image_of_mem f hx)).trans (le_max_left F 1)
      linarith
    · exact (sub_le_self _ (div_nonneg (hg0 x hx) hε.le)).trans (le_of_not_ge hfx)
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε _ x hx
    have hfx : f x < η := lt_of_not_ge (fun hh ↦ hne ⟨x, hx, hh⟩)
    exact (sub_le_self _ (div_nonneg (hg0 x hx) hε.le)).trans hfx.le

end SharpLiebThirring.ActionProof

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

def actionDefect (σ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) : ℝ :=
  (∑ i, z.2 i ^ 2) ^ (1 + 1 / σ) -
    ∑ i, z.2 i * ((diagonal (fun i ↦ k i ^ 2) - (z.1 : Matrix (Fin N) (Fin N) ℝ) ^ 2) *ᵥ z.2) i

def constraintDefect (σ δ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) : ℝ :=
  ∑ i, ∑ j, (matrixField σ δ k z.1 i j - z.2 i * z.2 j) ^ 2

lemma actionDefect_continuous {σ : ℝ} (hσ : 0 < σ) (k : Fin N → ℝ) :
    Continuous (actionDefect σ k) := by
  apply Continuous.sub
  · exact (by fun_prop : Continuous (fun z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) ↦
      ∑ i, z.2 i ^ 2)).rpow_const (fun _ ↦ Or.inr (by positivity))
  · unfold mulVec dotProduct
    fun_prop

lemma constraintDefect_continuous {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    Continuous (constraintDefect σ δ k) := by
  have hc : Continuous (fun z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) ↦
      matrixField σ δ k z.1) := (matrixField_continuous hσ hδ k).comp continuous_fst
  unfold constraintDefect
  fun_prop

lemma constraintDefect_nonneg (σ δ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) :
    0 ≤ constraintDefect σ δ k z := by
  unfold constraintDefect
  exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))

lemma constraintDefect_eq_zero_iff (σ δ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) :
    constraintDefect σ δ k z = 0 ↔ matrixField σ δ k z.1 = vecMulVec z.2 z.2 := by
  constructor
  · intro h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg
        (matrixField σ δ k z.1 i j - z.2 i * z.2 j)))).mp h i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
      (matrixField σ δ k z.1 i j - z.2 i * z.2 j))).mp hi j (Finset.mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hij)
  · intro h
    simp [constraintDefect, h, vecMulVec]

/-- Uniform compact penalty estimate for the matrix field and rank-one
constraint. -/
lemma matrix_compact_penalty {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ)
    {K : Set (selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ))} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ∈ K,
      actionDefect σ k z - constraintDefect σ δ k z / ε ≤ η := by
  apply compact_penalty_bound hK (actionDefect_continuous hσ₀ k)
    (constraintDefect_continuous hσ₁ hδ k) (fun z _ ↦ constraintDefect_nonneg σ δ k z) _ hη
  intro z _ hz
  exact sub_nonpos.mpr (source_rankone_comparison hσ₀ hσ₁ hδ k z.1.prop z.2
    ((constraintDefect_eq_zero_iff σ δ k z).mp hz))

end SharpLiebThirring.ActionProof
namespace SharpLiebThirring.PathProof
open Matrix
variable {N : ℕ}

/-- The initial row-sign orbit calculation, without assuming invertibility
of any later matching solution. -/
lemma lower_gram_diagonal {C : Matrix (Fin N) (Fin N) ℝ} (hC : LowerTriangular C)
    {d : Fin N → ℝ} (hd : ∀ i, 0 < d i) (hgram : C * C.transpose = diagonal d) :
    (∀ i j, i ≠ j → C i j = 0) ∧ (∀ i, C i i ^ 2 = d i) := by
  have hrow : ∀ i : Fin N, (∀ j, i ≠ j → C i j = 0) ∧ C i i ^ 2 = d i := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hoff : ∀ j, i ≠ j → C i j = 0 := by
        intro j hij
        rcases lt_or_gt_of_ne hij with hijlt | hjilt
        · exact hC i j hijlt
        · have hj := ih j hjilt
          have hne : C j j ≠ 0 := by
            intro he
            have := hd j
            rw [← hj.2, he] at this
            norm_num at this
          have hg := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i j) hgram
          have hsum : (C * C.transpose) i j = C i j * C j j := by
            simp only [mul_apply, transpose_apply]
            apply Finset.sum_eq_single j
            · intro b _ hbj
              rw [hj.1 b hbj.symm, mul_zero]
            · simp
          rw [hsum, diagonal_apply_ne _ hij] at hg
          exact (mul_eq_zero.mp hg).resolve_right hne
      refine ⟨hoff, ?_⟩
      have hg := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i i) hgram
      have hsum : (C * C.transpose) i i = C i i ^ 2 := by
        simp only [mul_apply, transpose_apply]
        rw [Finset.sum_eq_single i]
        · ring
        · intro b _ hbi
          rw [hoff b hbi.symm, zero_mul]
        · simp
      simpa only [hsum, diagonal_apply_eq] using hg
  exact ⟨fun i j hij ↦ (hrow i).1 j hij, fun i ↦ (hrow i).2⟩

lemma lower_gram_initial_orbit {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ)
    (hk : ∀ i, 0 < k i) {C : Matrix (Fin N) (Fin N) ℝ} (hC : LowerTriangular C)
    (hgram : C * C.transpose = diagonal (fun i ↦ 2 * ε * k i)) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      C = diagonal (fun i ↦ s i * Real.sqrt (2 * ε * k i)) := by
  have hpos (i : Fin N) : 0 < 2 * ε * k i := mul_pos (mul_pos (by norm_num) hε) (hk i)
  obtain ⟨hoff, hdiag⟩ := lower_gram_diagonal hC hpos hgram
  let s := fun i ↦ C i i / Real.sqrt (2 * ε * k i)
  refine ⟨s, ?_, ?_⟩
  · intro i
    have hsqrt : 0 < Real.sqrt (2 * ε * k i) := Real.sqrt_pos.2 (hpos i)
    have hs : s i ^ 2 = 1 := by
      dsimp [s]
      rw [div_pow, hdiag i, Real.sq_sqrt (hpos i).le]
      exact div_self (ne_of_gt (hpos i))
    rcases (sq_eq_one_iff).mp hs with h | h
    · exact Or.inl h
    · exact Or.inr h
  · ext i j
    by_cases hij : i = j
    · subst j
      rw [diagonal_apply_eq]
      dsimp [s]
      rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 (hpos i)))]
    · rw [diagonal_apply_ne _ hij, hoff i j hij]

/-- Explicit inverse for the initial linearized endpoint map, apart from
its nonzero scalar factor -1/ε. -/
def triangularLinearInverse (c : Fin N → ℝ) (Z : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ if i < j then 0 else if i = j then Z i j / (2 * c i) else Z i j / c j

lemma triangularLinearInverse_lower (c : Fin N → ℝ) (Z : Matrix (Fin N) (Fin N) ℝ) :
    LowerTriangular (triangularLinearInverse c Z) := by
  intro i j hij
  simp [triangularLinearInverse, hij]

lemma triangularLinearInverse_right (c : Fin N → ℝ) (hc : ∀ i, c i ≠ 0)
    {Z : Matrix (Fin N) (Fin N) ℝ} (hZ : Z.IsHermitian) :
    triangularLinearInverse c Z * (diagonal c).transpose +
      diagonal c * (triangularLinearInverse c Z).transpose = Z := by
  ext i j
  simp only [diagonal_transpose, Matrix.add_apply, mul_diagonal, diagonal_mul, transpose_apply]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hji : ¬ j < i := not_lt_of_gt hij
    have hne : i ≠ j := ne_of_lt hij
    have hsym : Z j i = Z i j := by simpa using congrArg (fun A ↦ A i j) hZ
    simp [triangularLinearInverse, hij, hji, hne.symm, hsym]
    field_simp [hc]
  · subst j
    simp [triangularLinearInverse]
    field_simp [hc]
    ring
  · have hji : ¬ i < j := not_lt_of_gt hij
    have hne : i ≠ j := ne_of_gt hij
    simp [triangularLinearInverse, hij, hji, hne]
    field_simp [hc]

end SharpLiebThirring.PathProof

end
end
end

end OAI
