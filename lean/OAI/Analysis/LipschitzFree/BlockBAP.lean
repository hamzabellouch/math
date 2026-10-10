import OAI.Analysis.LipschitzFree.BlockObstruction

namespace OAI

/-!
# Finite anchor obstructions exclude bounded approximation constants
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree

theorem not_hasBAP_of_finite_obstruction {M : Type*} [MetricSpace M] (o : M)
    (A : Finset M) (p ε : ℝ) (hε : 0 < ε)
    (hobs : ∀ T : FreeSpace o →L[ℝ] FreeSpace o,
      Module.Finite ℝ (LinearMap.range T.toLinearMap) → ‖T‖ ≤ p →
        ∃ a ∈ A, ε ≤ ‖T (delta o a) - delta o a‖)
    (Λ : ℝ) (hΛ : Λ ≤ p) : ¬ HasBAP (FreeSpace o) Λ := by
  intro h
  let C := (delta o) '' (A : Set M)
  have hC : IsCompact C := (A.finite_toSet.image (delta o)).isCompact
  obtain ⟨T,hT,hTnorm,η,hη,he⟩ := h C hC ε hε
  obtain ⟨a,ha,herr⟩ := hobs T hT (hTnorm.trans hΛ)
  have herror := he (delta o a) ⟨a,ha,rfl⟩
  linarith

namespace BlockConstruction
open BlockParameters
variable (p : ℕ) [Fact (0 < R p)]

theorem noBAP (hp : 1 ≤ p) (Λ : ℝ) (hΛ : Λ ≤ (p : ℝ)) :
    ¬ HasBAP (FreeSpace (base p)) Λ :=
  not_hasBAP_of_finite_obstruction (base p) (anchors p) p (1/2) (by norm_num)
    (fun T => obstruction p hp T) Λ hΛ

end BlockConstruction
end DiscreteFree
end

end

end OAI
