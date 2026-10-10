import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPerturbedBox
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarPrefixCoordinates

namespace OAI

/-! # Box bounds survive thickening of an endpoint tuple

Each successive increment keeps its own template. In particular, this
applies to alternating reflected templates, without replacing them by
their union before the polynomial multiplication argument.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [MeasurableSpace N]
  [MeasurableMul₂ N] [MeasurableInv N]

theorem exists_subexponential_tuple_perturbation
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (h : ℕ) (E : Fin h → Set W) (hE : ∀ i, IsCompact (E i))
    (h0 : ∀ i, (0 : W) ∈ E i) (β : Fin h → M.Bases)
    (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (E i)) (β i).val)
    (scale R S : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n) (hS0 : ∀ n, 0 ≤ S n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (hS : HasSubexponentialUpperBoundSeq scale S) :
    ∃ Q : Fin h → ℕ → ℝ,
      (∀ i n, 0 ≤ Q i n) ∧ (∀ i, HasSubexponentialUpperBoundSeq scale (Q i)) ∧
      ∀ n (y η : Fin h → N),
        (∀ i, (prefixCoordinateEquiv h).symm y i ∈
          M.groupBox T hunimod eW (Exp ∘ eN) (E i) (β i) (scale n) (R n)) →
        (∀ i j, η j ∈ exponentialCoordinateBox (Exp ∘ eN)
          (WordBasisSelections.basis M.letter M.wordList (β i)) (S n)) →
        ∀ i, (prefixCoordinateEquiv h).symm (fun j => y j * η j) i ∈
          M.groupBox T hunimod eW (Exp ∘ eN) (E i) (β i) (scale n) (Q i n) := by
  choose Q hQ0 hQ hbound using fun i =>
    M.exists_subexponential_perturbed_groupBox T hunimod eW eN Exp hExp dynkin b₀
      (hE i) (h0 i) (β i) (hβ i) scale R S hs hscale hR0 hS0 hR hS
  refine ⟨Q, hQ0, hQ, ?_⟩
  intro n y η hy hη i
  cases h with
  | zero => exact Fin.elim0 i
  | succ k =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [prefixCoordinateEquiv_symm_zero]
      have hone : (1 : N) ∈ exponentialCoordinateBox (Exp ∘ eN)
          (WordBasisSelections.basis M.letter M.wordList (β 0)) (S n) :=
        ⟨0, by simp [hExp.map_zero], by simpa using hS0 n⟩
      have hb := hbound 0 n 1 ((prefixCoordinateEquiv (k + 1)).symm y 0) (η 0)
        hone (hy 0) (hη 0 0)
      simpa only [inv_one, one_mul, prefixCoordinateEquiv_symm_zero] using hb
    · rw [prefixCoordinateEquiv_symm_mul_increment]
      exact hbound j.succ n (η j.castSucc)
        ((prefixCoordinateEquiv (k + 1)).symm y j.succ) (η j.succ)
        (hη j.succ j.castSucc) (hy j.succ) (hη j.succ j.succ)

end PolycyclicRecognition.CartanWordModel

end

end OAI
