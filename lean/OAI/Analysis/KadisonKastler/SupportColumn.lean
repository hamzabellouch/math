import OAI.Analysis.KadisonKastler.SupportColumnConstruction
import OAI.Analysis.KadisonKastler.Column
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # The column estimate on a small diagonal support -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

local instance supportColumnOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance supportColumnOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance supportColumnAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance supportColumnAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The entrywise spatial commutator, also for rectangular matrices. -/
def matrixCommutator (h : H →L[ℂ] H) (X : CStarMatrix m n (H →L[ℂ] H)) :
    CStarMatrix m n (H →L[ℂ] H) := CStarMatrix.mapₗ (innerDerivation h) X

omit [CompleteSpace H] [Fintype m] [Fintype n] in
@[simp]
theorem matrixCommutator_apply (h : H →L[ℂ] H)
    (X : CStarMatrix m n (H →L[ℂ] H)) (i : m) (j : n) :
    matrixCommutator h X i j = h * X i j - X i j * h := rfl

/-- The entrywise commutator agrees with the usual amplified commutator. -/
theorem matrixCommutator_eq_diagonal [DecidableEq m] [DecidableEq n]
    (h : H →L[ℂ] H) (X : CStarMatrix m n (H →L[ℂ] H)) :
    matrixCommutator h X = diagonalAmplification h * X - X * diagonalAmplification h := by
  apply CStarMatrix.ext
  intro i j
  change h * X i j - X i j * h =
    (Matrix.diagonal (fun _ : m => h) * CStarMatrix.ofMatrix.symm X) i j -
      (CStarMatrix.ofMatrix.symm X * Matrix.diagonal (fun _ : n => h)) i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

omit [CompleteSpace H] [Fintype l] [Fintype n] in
theorem matrixCommutator_mul (h : H →L[ℂ] H)
    (X : CStarMatrix l m (H →L[ℂ] H)) (Y : CStarMatrix m n (H →L[ℂ] H)) :
    matrixCommutator h (X * Y) = matrixCommutator h X * Y + X * matrixCommutator h Y := by
  apply CStarMatrix.ext
  intro i j
  simp only [matrixCommutator_apply, CStarMatrix.mul_apply, CStarMatrix.add_apply,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  noncomm_ring

omit [CompleteSpace H] [Fintype m] [Fintype n] in
theorem matrixCommutator_eq_zero (h : H →L[ℂ] H)
    (X : CStarMatrix m n (H →L[ℂ] H)) (hX : ∀ i j, Commute h (X i j)) :
    matrixCommutator h X = 0 := by
  apply CStarMatrix.ext
  intro i j
  exact sub_eq_zero.mpr (hX i j).eq

variable {k : Type*} [Fintype k] [DecidableEq k] [DecidableEq m]

omit [Fintype m] in
/-- Each entry of the partial-isometry column lies in the given matrix algebra. -/
theorem supportColumn_entry_mem (E : Generator.MatrixUnitSystem k (H →L[ℂ] H))
    (S : Finset (m × k)) (f : S ↪ k) (i : m) (j : Fin 1) :
    supportColumn E S f i j ∈ E.algebra := by
  change (∑ s : S, Matrix.single s.val.1 0 (E.entry s.val.2 (f s))) i j ∈ E.algebra
  rw [Matrix.sum_apply]
  apply E.algebra.sum_mem
  intro s _
  change (if s.val.1 = i ∧ (0 : Fin 1) = j then E.entry s.val.2 (f s) else 0) ∈ E.algebra
  split_ifs
  · exact E.entry_mem _ _
  · exact E.algebra.zero_mem

/-- The support column is a contraction because its range projection is a projection. -/
theorem norm_supportColumn_le_one (E : Generator.MatrixUnitSystem k (H →L[ℂ] H))
    (S : Finset (m × k)) (f : S ↪ k) : ‖supportColumn E S f‖ ≤ 1 := by
  have hs : ‖supportColumn E S f‖ ^ 2 ≤ 1 := by
    rw [← norm_rectangular_mul_star, supportColumn_mul_conjTranspose]
    exact (supportProjection_isStarProjection E S).norm_le _
  nlinarith [norm_nonneg (supportColumn E S f)]

/-- The cardinality assumption constructs the required column, including the empty case. -/
theorem exists_supportColumn (E : Generator.MatrixUnitSystem k (H →L[ℂ] H))
    (S : Finset (m × k)) (hS : S.card ≤ Fintype.card k) :
    ∃ V : CStarMatrix m (Fin 1) (H →L[ℂ] H),
      V * V.conjTranspose = supportProjection E S ∧ ‖V‖ ≤ 1 ∧
      ∀ i j, V i j ∈ E.algebra := by
  have hc : Fintype.card S ≤ Fintype.card k := by simpa using hS
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  exact ⟨supportColumn E S f, supportColumn_mul_conjTranspose E S f,
    norm_supportColumn_le_one E S f, supportColumn_entry_mem E S f⟩

/-- Applying the established column theorem to a column with entries in a concrete algebra. -/
theorem matrixCommutator_column_bound (M : VonNeumannAlgebra H)
    (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (p : ℕ) (X : CStarMatrix (Fin p) (Fin 1) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M) : ‖matrixCommutator h X‖ ≤ 8 * δ * ‖X‖ := by
  let ρ : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype
  let Y : CStarMatrix (Fin p) (Fin 1) (Algebra M) :=
    CStarMatrix.ofMatrix (fun i j => ⟨X i j, hX i j⟩)
  have hmap : CStarMatrix.mapₗ ρ.toAlgHom.toLinearMap Y = X := rfl
  have hnorm : ‖Y‖ = ‖X‖ := by
    have ht := injective_starAlgHom_completelyIsometric ρ Subtype.val_injective p 1 Y
    simpa only [hmap] using ht.symm
  have ht := commutator_column_bound hPublished ρ h hδ
    (fun a => hb a.val a.property) p Y
  change ‖matrixCommutator h X‖ ≤ 8 * δ * ‖Y‖ at ht
  rwa [hnorm] at ht

/-- A clipped coefficient has the uniform column bound on its small support. -/
theorem small_support_commutator_bound (M : VonNeumannAlgebra H)
    (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (p q : ℕ) (E : Generator.MatrixUnitSystem (Fin q) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra)
    (S : Finset (Fin p × Fin q)) (hS : S.card ≤ q)
    (K : CStarMatrix (Fin p) (Fin p) (H →L[ℂ] H)) (hK : ∀ i j, K i j ∈ M)
    (hKP : K = K * supportProjection E S)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (hc : ∀ a ∈ E.algebra, Commute h a) (z : Generator.FiniteHilbert (Fin p) H) :
    ‖rectangularHilbertMatrix (matrixCommutator h K) z‖ ≤
      8 * δ * ‖K‖ * ‖rectangularHilbertMatrix (supportProjection E S) z‖ := by
  obtain ⟨V, hVP, hVnorm, hVmem⟩ := exists_supportColumn E S (by simpa using hS)
  have hVTzero : matrixCommutator h V.conjTranspose = 0 := by
    apply matrixCommutator_eq_zero
    intro i j
    exact hc _ (E.algebra.star_mem' (hVmem j i))
  have hfactor : matrixCommutator h K = matrixCommutator h (K * V) * V.conjTranspose := by
    calc
      _ = matrixCommutator h ((K * V) * V.conjTranspose) := by
        congr 1
        have hassoc : (K * V) * V.conjTranspose = K * (V * V.conjTranspose) :=
          Matrix.mul_assoc K V V.conjTranspose
        rw [hassoc, hVP, ← hKP]
      _ = _ := by rw [matrixCommutator_mul, hVTzero, CStarMatrix.mul_zero, add_zero]
  have hKVmem : ∀ i j, (K * V) i j ∈ M := by
    intro i j
    rw [CStarMatrix.mul_apply]
    exact M.sum_mem (fun k _ => M.mul_mem (hK i k) (hE (hVmem k j)))
  have hbound := matrixCommutator_column_bound M hPublished h hδ hb p (K * V) hKVmem
  have hKVnorm : ‖K * V‖ ≤ ‖K‖ := by
    exact (rectangular_norm_mul_le K V).trans
      (by simpa using mul_le_mul_of_nonneg_left hVnorm (norm_nonneg K))
  have hVPproj : IsStarProjection (V * V.conjTranspose) := by
    rw [hVP]
    exact supportProjection_isStarProjection E S
  calc
    _ = ‖rectangularHilbertMatrix (matrixCommutator h (K * V))
        (rectangularHilbertMatrix V.conjTranspose z)‖ := by
      rw [hfactor, rectangularHilbertMatrix_mul]
      rfl
    _ ≤ ‖matrixCommutator h (K * V)‖ * ‖rectangularHilbertMatrix V.conjTranspose z‖ := by
      rw [← norm_rectangularHilbertMatrix]
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (8 * δ * ‖K‖) * ‖rectangularHilbertMatrix V.conjTranspose z‖ :=
      mul_le_mul_of_nonneg_right
        (hbound.trans (mul_le_mul_of_nonneg_left hKVnorm (by positivity))) (norm_nonneg _)
    _ = _ := by rw [norm_rectangular_star_apply_of_projection V hVPproj, hVP]

end

end KadisonKastler

end OAI
