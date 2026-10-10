import OAI.InformationTheory.SecretKey.Extensions

namespace OAI

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace ZeroKey

universe u

theorem class_uniformProtocolGap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) (hc : InClass R) :
    UniformProtocolGap.{u} R hR := by
  intro k O M _ _ _ _ _ _ d A B _ _ _ _ _ _ _ _ TA TB CA CB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p e P hP sigma hs
  exact p.uniform_gap_purification (positiveCopies R k) (hc.positiveCopies k) P hP sigma hs

theorem class_uniformCompletedGap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) (hc : InClass R) :
    UniformCompletedGap.{u} R hR := by
  intro k ell hell p
  exact p.uniform_error (hc.positiveCopies k) hell

namespace Explicit

/-- The explicit density witness removes a proof dependency from the challenge statement.
This is equivalent to the original five-clause formulation. -/
theorem mainClaim_iff_original : MainClaim.{u} ↔
    (Density rhoFin ∧ ¬ Separable rhoFin ∧
      distillableSecretKey.{u} rhoFin rhoFin_density = 0 ∧
      UniformProtocolGap.{u} rhoFin rhoFin_density ∧
      UniformCompletedGap.{u} rhoFin rhoFin_density) := by
  constructor
  · rintro ⟨hR, hsep, hkey, hprotocol, hcompleted⟩
    exact ⟨hR, hsep, hkey, hprotocol, hcompleted⟩
  · rintro ⟨hR, hsep, hkey, hprotocol, hcompleted⟩
    exact ⟨hR, hsep, hkey, hprotocol, hcompleted⟩

theorem main : MainClaim.{u} := by
  exact ⟨rhoFin_density, rhoFin_not_separable,
    class_distillableSecretKey_zero rhoFin rhoFin_density rhoFin_inClass,
    class_uniformProtocolGap rhoFin rhoFin_density rhoFin_inClass,
    class_uniformCompletedGap rhoFin rhoFin_density rhoFin_inClass⟩

end Explicit

end ZeroKey

end

end OAI
