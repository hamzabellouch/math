import OAI.RepresentationTheory.FoulkesHowe.Model
import OAI.RepresentationTheory.FoulkesHowe.LinearCase
import OAI.RepresentationTheory.FoulkesHowe.PairingConstruction
import OAI.RepresentationTheory.FoulkesHowe.Surjectivity
import OAI.RepresentationTheory.FoulkesHowe.ProductVanishing

namespace OAI

noncomputable section

universe u

namespace Problem346

theorem canonical_foulkes_howe_surjective :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧ ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V ν → ν = μ := by
  intro V _ _ _ a b ha hab
  apply canonical_surjective_unique_of_vanishing a b V
  have hb : 1 ≤ b := by
    have hpred : 1 ≤ a - 1 := by omega
    have hprod := Nat.mul_le_mul ha hpred
    omega
  exact vanishing_on_products_aux V a b (by omega) hb hab

theorem canonical_foulkes_howe_a_one :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : ℕ), ∃ μ : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V), IsFoulkesMap 1 b V μ ∧ Function.Bijective μ ∧ ∀ ν : SymPow b (SymPow 1 V) →ₗ[ℂ] SymPow 1 (SymPow b V), IsFoulkesMap 1 b V ν → ν = μ := by
  intro V _ _ _ b
  exact canonical_foulkes_howe_a_one_aux V b

theorem vanishing_on_products :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 1 ≤ a → 1 ≤ b → a * (a - 1) ≤ b → ∀ T : SymmetricMultilinearForm a b V, IsSymmetricMultilinearForm a b V T → (∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) → T = 0 := by
  intro V _ _ _ a b ha hb hab T hT hdiag
  exact vanishing_on_products_aux V a b ha hb hab T hT hdiag

theorem foulkes_comparison_embedding :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V), IsGLEquivariantEmbedding a b V ι := by
  intro V _ _ _ a b ha hab
  obtain ⟨μ, hμ, hsurj, _⟩ :=
    canonical_foulkes_howe_surjective (Module.Dual ℂ V) a b ha hab
  exact PairingConstruction.comparison_of_surjection V a b ⟨μ, hμ, hsurj⟩

theorem sixth_symmetric_power_comparison :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : ℕ), 30 ≤ b → ∃ ι : SymPow 6 (SymPow b V) →ₗ[ℂ] SymPow b (SymPow 6 V), IsGLEquivariantEmbedding 6 b V ι := by
  intro V _ _ _ b hb
  exact foulkes_comparison_embedding V 6 b (by norm_num) (by simpa using hb)

end Problem346

end

end OAI
