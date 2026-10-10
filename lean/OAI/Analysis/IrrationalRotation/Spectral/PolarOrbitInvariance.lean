import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

noncomputable section
open scoped Pointwise

namespace Invariant233.PolarOrbit

theorem centralizer_mem_iff_of_mulEquiv
    {A : Type*} [Mul A] (e : A ≃* A) (s : Set A)
    (hs : ∀ a, e a ∈ s ↔ a ∈ s) (a : A) :
    e a ∈ Set.centralizer s ↔ a ∈ Set.centralizer s := by
  constructor
  · intro ha b hb
    apply e.injective
    simpa only [map_mul] using ha (e b) ((hs b).mpr hb)
  · intro ha b hb
    obtain ⟨c, rfl⟩ := e.surjective b
    simpa only [map_mul] using congrArg e (ha c ((hs c).mp hb))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem generated_mem_iff
    (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : Set (H →L[ℂ] H)) (hs : ∀ A, Φ A ∈ s ↔ A ∈ s)
    (A : H →L[ℂ] H) :
    Φ A ∈ vonNeumannGenerated s ↔ A ∈ vonNeumannGenerated s := by
  have hstar : ∀ B, Φ B ∈ s ∪ star s ↔ B ∈ s ∪ star s := by
    intro B
    change (Φ B ∈ s ∨ star (Φ B) ∈ s) ↔ (B ∈ s ∨ star B ∈ s)
    have he : Φ (star B) = star (Φ B) := by
      exact Φ.map_star' B
    rw [← he, hs B, hs (star B)]
  have hc := centralizer_mem_iff_of_mulEquiv Φ.toMulEquiv (s ∪ star s) hstar
  change Φ A ∈ (vonNeumannGenerated s : Set (H →L[ℂ] H)) ↔
    A ∈ (vonNeumannGenerated s : Set (H →L[ℂ] H))
  rw [coe_vonNeumannGenerated]
  exact centralizer_mem_iff_of_mulEquiv Φ.toMulEquiv _ hc A

theorem polarConjugate_eq_conj_zpow (U : unitary (H →L[ℂ] H))
    (B : H →L[ℂ] H) (n : ℤ) :
    polarConjugate (U : H →L[ℂ] H) B n =
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ n) B := by
  rw [Unitary.conjStarAlgAut_apply]
  cases n with
  | ofNat k =>
    simp [polarConjugate, star_pow]
  | negSucc k =>
    simp [polarConjugate, zpow_negSucc,
      ← Unitary.star_eq_inv, Unitary.coe_star, star_pow]

theorem conj_zpow_polarConjugate (U : unitary (H →L[ℂ] H))
    (B : H →L[ℂ] H) (m n : ℤ) :
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ m)
        (polarConjugate (U : H →L[ℂ] H) B n) =
      polarConjugate (U : H →L[ℂ] H) B (m + n) := by
  rw [polarConjugate_eq_conj_zpow, polarConjugate_eq_conj_zpow,
    zpow_add, Unitary.conjStarAlgAut_mul_apply]

theorem mem_range_polarConjugate_iff (U : unitary (H →L[ℂ] H))
    (B A : H →L[ℂ] H) (m : ℤ) :
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ m) A ∈
        Set.range (polarConjugate (U : H →L[ℂ] H) B) ↔
      A ∈ Set.range (polarConjugate (U : H →L[ℂ] H) B) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n - m, ?_⟩
    apply (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ m)).injective
    change Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ m)
        (polarConjugate (U : H →L[ℂ] H) B (n - m)) =
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ m) A
    rw [conj_zpow_polarConjugate]
    have hadd : m + (n - m) = n := by omega
    simpa only [hadd] using hn
  · rintro ⟨n, rfl⟩
    exact ⟨m + n, (conj_zpow_polarConjugate U B m n).symm⟩

theorem fullPolarAlgebra_mem_iff_zpow (U : unitary (H →L[ℂ] H))
    (B A : H →L[ℂ] H) (m : ℤ) :
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ m) A ∈
        fullPolarAlgebra (U : H →L[ℂ] H) B ↔
      A ∈ fullPolarAlgebra (U : H →L[ℂ] H) B :=
  generated_mem_iff _ _ (fun C => mem_range_polarConjugate_iff U B C m) A

theorem fullPolarAlgebra_mem_iff (U : unitary (H →L[ℂ] H))
    (B A : H →L[ℂ] H) :
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U A ∈
        fullPolarAlgebra (U : H →L[ℂ] H) B ↔
      A ∈ fullPolarAlgebra (U : H →L[ℂ] H) B := by
  simpa using fullPolarAlgebra_mem_iff_zpow U B A 1

theorem iterate_conjStarAlgAut (U : unitary (H →L[ℂ] H))
    (A : H →L[ℂ] H) (n : ℕ) :
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U :
        (H →L[ℂ] H) → (H →L[ℂ] H))^[n] A =
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U ^ n) A := by
  simp only [map_pow, StarAlgEquiv.coe_pow]

theorem fullPolarAlgebra_le (U : H →L[ℂ] H) (B : H →L[ℂ] H)
    (N : VonNeumannAlgebra H) (hU : U ∈ N) (hB : B ∈ N) :
    fullPolarAlgebra U B ≤ N := by
  apply vonNeumannGenerated_le
  rintro A ⟨n, rfl⟩
  unfold polarConjugate
  split
  · exact mul_mem (mul_mem (pow_mem hU _) hB) (pow_mem (star_mem hU) _)
  · exact mul_mem (mul_mem (pow_mem (star_mem hU) _) hB) (pow_mem hU _)

theorem mem_fullPolarAlgebra (U B : H →L[ℂ] H) : B ∈ fullPolarAlgebra U B := by
  apply subset_vonNeumannGenerated
  exact ⟨0, by simp [polarConjugate]⟩

end Invariant233.PolarOrbit

end

end OAI
