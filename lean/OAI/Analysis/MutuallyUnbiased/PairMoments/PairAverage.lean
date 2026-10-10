import Mathlib.Data.Fintype.EquivFin
import OAI.Analysis.MutuallyUnbiased.Moments.NormalizedPartitions

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem injectiveMoment_empty (H : CMatrix) :
    injectiveMoment H (0 : Matrix (Fin 0) (Fin 0) ℤ) = 1 := by
  let : Nonempty ((Fin 0 ↪ Coord) × (Fin 0 ↪ Coord)) :=
    ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty⟩
  unfold injectiveMoment
  have hf : (fun s : (Fin 0 ↪ Coord) × (Fin 0 ↪ Coord) =>
      ((exponentMonomial H (0 : Matrix (Fin 0) (Fin 0) ℤ) s.1 s.2).re +
        (exponentMonomial H.transpose (0 : Matrix (Fin 0) (Fin 0) ℤ) s.1 s.2).re) / 2) =
      (fun _ => (1 : ℝ)) := by
    funext s
    norm_num [exponentMonomial]
  rw [hf]
  exact average_const 1

/-- A uniform injection of all six row indices is a uniform permutation.
This identifies the general partition theorem with the paper's pair average. -/
theorem averagedRowProducts_eq_pairAverage {n : ℕ} (H : CMatrix)
    (A : Matrix Coord (Fin n) ℤ) :
    averagedRowProducts H A =
      pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) := by
  let f : Equiv.Perm Coord → ℝ := fun π =>
    ((∏ j, g (fun i k => H (π i) k) (fun i => A i j)).re +
      (∏ j, g (fun i k => H k (π i)) (fun i => A i j)).re) / 2
  calc
    averagedRowProducts H A =
        average (f ∘ Equiv.embeddingEquivOfFinite Coord) := by rfl
    _ = average f := average_equiv (Equiv.embeddingEquivOfFinite Coord) f
    _ = _ := rfl

theorem pairAverage_products_partition {n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix Coord (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    pairAverage H (fun K => (∏ j, g K (fun i => A i j)).re) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  rw [← averagedRowProducts_eq_pairAverage H A]
  exact averagedRowProducts_partition hH A F cover

end MUB6

end

end OAI
