import OAI.NumberTheory.TwoPoint.Bounds.CoordinateSampling
import OAI.NumberTheory.TwoPoint.Walks.ColumnRankRelations

namespace OAI

/-! The selected high-rank congruences under the full product prime law. -/

namespace TwoPointCorrelations

open Finset Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Outside variables are truly integrated, rather than conditioned away.
Repeated numerical primes remain allowed by the independent product law. -/
theorem full_coordinate_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (w : ρ → α → ℤ) (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (hdet : (Matrix.of fun i j => w i (pivot j)).det ≠ 0)
    (M : ℕ) (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (hsize : ∀ y z : ρ → P, ∀ i,
      (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ M) :
    (FiniteLaw.independent (fun _ : α => μ)).probability (fun x =>
      ∀ i, ((x (control i)).val : ℤ) ∣ ∑ z, w i z * ((x z).val : ℤ)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ) := by
  classical
  rw [FiniteLaw.probability, independent_average_three control pivot hc hp hdisjoint]
  apply (FiniteLaw.average_mono _ (g := fun _ =>
    Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ)) ?_).trans_eq
      (FiniteLaw.average_const _ _)
  intro base
  let base' : α → ℤ := fun z =>
    if hz : z ∈ outsideCoordinates control pivot then ((base ⟨z, hz⟩).val : ℤ) else 0
  have h := split_coordinate_prime_rank_bound P hP μ w control pivot hc hp hdisjoint
    hdet base' M a ha hatom hsize
  dsimp only at h
  convert h using 1
  apply congrArg (FiniteLaw.independent (fun _ : ρ => μ)).average
  funext c
  unfold FiniteLaw.probability
  apply congrArg (FiniteLaw.independent (fun _ : ρ => μ)).average
  funext y
  congr 1
  apply propext
  have heq := coordinateAssignment_integer control pivot hc hp hdisjoint
    (fun p : P => (p.val : ℤ)) base c y
  simp_rw [show ∀ i,
      (coordinateAssignment control pivot hc hp hdisjoint base c y (control i)) = c i from
    fun i => coordinateAssignment_index control pivot hc hp hdisjoint base c y (Sum.inl i)]
  exact Iff.of_eq (congrArg (fun x : α → ℤ =>
    ∀ i, ((c i).val : ℤ) ∣ ∑ z, w i z * x z) heq)

/-- Jointly independent difference/control pairs supply all algebraic
premises of the full-coordinate probability bound. -/
theorem independent_pairs_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (w : ρ → α → ℤ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim (fun i z => (w i z : ℝ))
      (fun i => Pi.basisFun ℝ α (control i))))
    (M : ℕ) (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (hsize : ∀ pivot : ρ → α, Function.Injective pivot →
      (∀ i j, pivot i ≠ control j) → ∀ y z : ρ → P, ∀ i,
      (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ M) :
    (FiniteLaw.independent (fun _ : α => μ)).probability (fun x =>
      ∀ i, ((x (control i)).val : ℤ) ∣ ∑ z, w i z * ((x z).val : ℤ)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ) := by
  obtain ⟨hc, pivot, hp, hd, hdet⟩ := integral_independent_pairs_disjoint_minor w control hind
  exact full_coordinate_prime_rank_bound P hP μ w control pivot hc hp hd hdet M a ha hatom
    (hsize pivot hp hd)

end TwoPointCorrelations

end OAI
