import OAI.Analysis.KadisonKastler.SeparableReduction
import OAI.Analysis.KadisonKastler.CenterAlignment

namespace OAI

/-! # Removing the common-center premise

Center alignment reduces unrestricted separable stability to stability
for algebras with a common center, with explicit tolerance estimates.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u

/-- Strong stability for algebras with a common center, uniform over
separable Hilbert-space representations. -/
def CommonCenterSeparableStability : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [SeparableSpace H], ∀ M N : VonNeumannAlgebra H,
        concreteCenter M = concreteCenter N →
        kkDistance M N < δ → NearConjugacy M N a

theorem separableStrongStability_of_common_center
    (hcommon : CommonCenterSeparableStability.{u})
    (hDix : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H, PublishedDixmierAveraging M) :
    SeparableStrongStability.{u} := by
  intro a ha
  obtain ⟨τ, hτ, hlocal⟩ := hcommon (a / 2) (by positivity)
  let δ := min (1 / 8000) (min (a / 1800) (τ / 1802))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ₁ : δ ≤ 1 / 8000 := min_le_left _ _
  have hδ₂ : δ ≤ a / 1800 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ ≤ τ / 1802 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro H _ _ _ _ M N hMN
  obtain ⟨w, hw, hc, hd⟩ := exists_common_center_neighbor
    M N (hDix H M) (hDix H N) hMN (by linarith only [hδ₁])
  let N₀ := unitaryConjugateAlgebra (star w) N
  have hdτ : kkDistance M N₀ < τ :=
    hd.trans (by linarith only [hδ₃, hτ])
  obtain ⟨v, hv, hva⟩ := hlocal H M N₀ hc.symm hdτ
  have hwN : Conjugates w N₀ N := by
    simpa only [star_star] using (conjugates_unitaryConjugateAlgebra (star w) N).symm
  refine ⟨w * v, hv.trans hwN, ?_⟩
  have hnorm := norm_unitary_mul_sub_one_le w v
  linarith only [hnorm, hw, hva, hδ₂, ha]

end

end KadisonKastler

end OAI
