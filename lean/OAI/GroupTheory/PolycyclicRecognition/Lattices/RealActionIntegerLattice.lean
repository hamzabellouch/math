import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerTimeLattice
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SemidirectUniformLattice

namespace OAI

/-! # Time-one invariance constructs a lattice in a real semidirect product -/

noncomputable section
namespace PolycyclicRecognition
variable {N : Type*} [Group N] [TopologicalSpace N]

omit [TopologicalSpace N] in
theorem subgroup_mem_mulAut_zpow (Λ : Subgroup N) (f : MulAut N)
    (hf : ∀ x ∈ Λ, f x ∈ Λ) (hi : ∀ x ∈ Λ, f.symm x ∈ Λ)
    (n : ℤ) (x : N) (hx : x ∈ Λ) : (f ^ n) x ∈ Λ := by
  have hp (a : MulAut N) (ha : ∀ y ∈ Λ, a y ∈ Λ) (k : ℕ) :
      ∀ y ∈ Λ, (a ^ k) y ∈ Λ := by
    induction k with
    | zero => exact fun _ h => h
    | succ k ih =>
      intro y hy
      rw [pow_succ']
      exact ha _ (ih y hy)
  cases n with
  | ofNat n => exact hp f hf n x hx
  | negSucc n =>
    change (f ^ (-((n + 1 : ℕ) : ℤ))) x ∈ Λ
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hp f.symm hi (n + 1) x hx

omit [TopologicalSpace N] in
theorem realAction_integerLattice_preserves (φ : Multiplicative ℝ →* MulAut N)
    (Λ : Subgroup N)
    (hf : ∀ x ∈ Λ, φ (Multiplicative.ofAdd 1) x ∈ Λ)
    (hi : ∀ x ∈ Λ, (φ (Multiplicative.ofAdd 1)).symm x ∈ Λ) :
    ∀ t ∈ integerTimeLattice, ∀ x ∈ Λ, φ t x ∈ Λ := by
  intro t ht x hx
  obtain ⟨n, rfl⟩ := integerTimeLattice_exists ht
  have he : (Multiplicative.ofAdd (1 : ℝ)) ^ n = Multiplicative.ofAdd (n : ℝ) := by
    apply Multiplicative.ext
    change n • (1 : ℝ) = (n : ℝ)
    simp
  rw [← he, map_zpow]
  exact subgroup_mem_mulAut_zpow Λ _ hf hi n x hx

attribute [local instance] semidirectProductTopology

theorem realAction_integerLattice_uniform (φ : Multiplicative ℝ →* MulAut N)
    (Λ : Subgroup N) (hΛ : IsUniformLattice Λ)
    (hf : ∀ x ∈ Λ, φ (Multiplicative.ofAdd 1) x ∈ Λ)
    (hi : ∀ x ∈ Λ, (φ (Multiplicative.ofAdd 1)).symm x ∈ Λ) :
    IsUniformLattice (semidirectLattice φ Λ integerTimeLattice
      (realAction_integerLattice_preserves φ Λ hf hi)) :=
  semidirectLattice_uniform φ Λ integerTimeLattice
    (realAction_integerLattice_preserves φ Λ hf hi) hΛ integerTimeLattice_uniform

end PolycyclicRecognition

end

end OAI
