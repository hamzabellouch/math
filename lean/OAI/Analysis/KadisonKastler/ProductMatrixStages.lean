import OAI.Analysis.KadisonKastler.MatrixProductStateSwap
import OAI.Analysis.KadisonKastler.ProductStateIrreducible
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition

namespace OAI

/-! # Deriving the product-state argument from finite matrix data

A remote copy of a finite tensor block has identical matrix moments.
Every other finite block embeds in the product of these two blocks and
a finite complement. These are finite tensor-product statements; no
centralizer irreducibility or crossed-product conclusion is assumed.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite data obtained by moving a block to unused sites of the same
types. Complements witness the product formula on every finite stage. -/
structure RemoteProductBlock (s : ℕ → ℕ)
    (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H)) (Ω : H) (k n : ℕ) where
  copy : MatrixUnitSystem (Fin (s k)) (H →L[ℂ] H)
  copy_mem : copy.algebra ≤
    (generatedVonNeumannAlgebra (⨆ j, (E j).algebra)).toStarSubalgebra
  commutes : ∀ i j a b, Commute ((E k).entry i j) (copy.entry a b)
  independent : ∀ i j (b : (E n).algebra),
    productVectorState Ω (copy.entry i j * b) =
      productVectorState Ω ((E k).entry i j) * productVectorState Ω b
  complement : ∀ m, ∃ (r : ℕ) (C : MatrixUnitSystem (Fin r) (H →L[ℂ] H))
      (hc : ∀ i j a b, Commute (((E k).product copy commutes).entry i j) (C.entry a b)),
    (E m).algebra ≤ (((E k).product copy commutes).product C hc).algebra ∧
    ∃ β : Fin r → Fin r → ℂ, ∀ i j a b c d,
      productVectorState Ω (((E k).product copy commutes).entry (i, j) (a, b) *
        C.entry c d) = productVectorState Ω ((E k).entry i a) *
          productVectorState Ω ((E k).entry j b) * β c d

/-- An increasing sequence of finite product matrix algebras, in its
cyclic separating product representation. This describes the construction
data rather than any of its centralizer or factor consequences. -/
structure ProductMatrixStages where
  size : ℕ → ℕ
  matrix : ∀ n, MatrixUnitSystem (Fin (size n)) (H →L[ℂ] H)
  increasing : Monotone (fun n => (matrix n).algebra)
  vector : H
  unit_vector : ‖vector‖ = 1
  local_cyclic : DenseRange
    (fun p : Σ n, (matrix n).algebra => (p.2 : H →L[ℂ] H) vector)
  separating : Function.Injective (algebraVectorMap
    (generatedVonNeumannAlgebra (⨆ n, (matrix n).algebra)) vector)
  remote : ∀ k n, Nonempty (RemoteProductBlock size matrix vector k n)

namespace ProductMatrixStages

variable (P : ProductMatrixStages (H := H))

def algebra : VonNeumannAlgebra H :=
  generatedVonNeumannAlgebra (⨆ n, (P.matrix n).algebra)

theorem local_le (n : ℕ) : (P.matrix n).algebra ≤ P.algebra.toStarSubalgebra := by
  intro x hx
  exact subset_generatedVonNeumannAlgebra _
    ((le_iSup (fun n => (P.matrix n).algebra) n) hx)

/-- The actual finite swap is assembled from the two matrix systems.
Triple product moments put it in the centralizer of the full algebra. -/
def localSwaps : LocalProductSwaps P.algebra P.vector where
  localAlgebra n := (P.matrix n).algebra
  local_le := P.local_le
  dense := P.local_cyclic
  independent_swap k a n := by
    classical
    let R := Classical.choice (P.remote k n)
    let E := (P.matrix k).product R.copy R.commutes
    let u := finiteMatrixBlockSwap E
    have hE : E.algebra ≤ P.algebra.toStarSubalgebra := by
      dsimp [E]
      rw [MatrixUnitSystem.product_algebra_eq_sup]
      exact sup_le (P.local_le k) R.copy_mem
    have hu : (u : H →L[ℂ] H) ∈ P.algebra := hE (finiteMatrixBlockSwap_mem E)
    refine ⟨u, hu, ?_, ?_⟩
    · apply productStateCentralizes_of_local (fun j => (P.matrix j).algebra) P.increasing
      intro m x hx
      obtain ⟨r, C, hc, hle, β, hβ⟩ := R.complement m
      exact finiteMatrixBlockSwap_product_centralizes E C hc (productVectorLinear P.vector)
        (fun i j => productVectorState P.vector ((P.matrix k).entry i j)) β hβ x (hle hx)
    · intro b
      exact finiteMatrixBlockSwap_independent (P.matrix k) R.copy R.commutes
        (productVectorLinear P.vector) b (fun i j => R.independent i j b) a a.property

/-- The finite-product construction implies the irreducibility of its
state centralizer. -/
theorem state_centralizer_irreducible (x : H →L[ℂ] H) (hx : x ∈ P.algebra)
    (hc : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ P.algebra →
      ProductStateCentralizes P.algebra P.vector u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState P.vector x • (1 : H →L[ℂ] H) :=
  P.localSwaps.scalar_of_commutes P.unit_vector P.separating x hx hc

theorem scalarCenter : ScalarCenter P.algebra := by
  intro x hx hc
  exact ⟨productVectorState P.vector x,
    P.state_centralizer_irreducible x hx (fun u hu _ => hc u hu)⟩

end ProductMatrixStages

end

end KadisonKastler

end OAI
