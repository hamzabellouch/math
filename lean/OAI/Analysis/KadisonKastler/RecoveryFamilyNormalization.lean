import OAI.Analysis.KadisonKastler.RecoveryRowNormalization
import OAI.Analysis.KadisonKastler.RandomizedRMS

namespace OAI

/-! # Normalization over all the finite choices in the recovery rows -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

private theorem finiteRMS_independent_family
    {Θ Ω A H : Type*} [Fintype Θ] [Nonempty Θ] [Fintype Ω] [Fintype A]
    [NormedAddCommGroup H]
    (f : Θ → Ω × A → H) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ θ, finiteRMS (f θ) = C) :
    finiteRMS (fun t : (Θ × Ω) × A => f t.1.1 (t.1.2, t.2)) = C := by
  have hsq (θ : Θ) : (𝔼 za : Ω × A, ‖f θ za‖ ^ 2) = C ^ 2 := by
    have hh := congrArg (fun r : ℝ => r ^ 2) (hf θ)
    rwa [finiteRMS_sq] at hh
  unfold finiteRMS
  have heq := Fintype.expect_equiv (Equiv.prodAssoc Θ Ω A)
    (fun t : (Θ × Ω) × A => ‖f t.1.1 (t.1.2, t.2)‖ ^ 2)
    (fun t : Θ × (Ω × A) => ‖f t.1 t.2‖ ^ 2) (fun _ => rfl)
  rw [heq, ← univ_product_univ, expect_product]
  simp_rw [hsq]
  simp [Real.sqrt_sq hC]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ] {n N q : ℕ} [NeZero q]

/-- Averaging the forward rows over the independent unitary choice retains
exactly the norm of the tested vector. -/
theorem recoveryForwardFamily_finiteRMS (M : VonNeumannAlgebra H)
    (v : Θ → unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (hN : 0 < N) (hNq : N < q) (ξ : Generator.FiniteHilbert (Fin n) H) :
    finiteRMS (fun t : (Θ × ZMod q) × Fin n =>
      recoveryForwardRow M N t.2 (scalarPhaseTwist t.1.2 (v t.1.1)) ξ) = ‖ξ‖ := by
  exact finiteRMS_independent_family
    (fun θ (za : ZMod q × Fin n) => recoveryForwardRow M N za.2 (scalarPhaseTwist za.1 (v θ)) ξ)
    (norm_nonneg ξ) (fun θ => recoveryForwardRows_finiteRMS M (v θ) hN hNq ξ)

/-- The full backward row family has the same exact normalization. -/
theorem recoveryBackwardFamily_finiteRMS (M : VonNeumannAlgebra H)
    (v : Θ → unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (hN : 0 < N) (hNq : N < q) (ξ : Generator.FiniteHilbert (Fin n) H) :
    finiteRMS (fun t : (Θ × ZMod q) × Fin n =>
      recoveryBackwardRow M N t.2 (scalarPhaseTwist t.1.2 (v t.1.1)) ξ) = ‖ξ‖ := by
  exact finiteRMS_independent_family
    (fun θ (za : ZMod q × Fin n) => recoveryBackwardRow M N za.2 (scalarPhaseTwist za.1 (v θ)) ξ)
    (norm_nonneg ξ) (fun θ => recoveryBackwardRows_finiteRMS M (v θ) hN hNq ξ)

end

end KadisonKastler

end OAI
