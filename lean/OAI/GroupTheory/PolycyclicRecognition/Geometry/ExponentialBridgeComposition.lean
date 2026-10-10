import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorBridgeComposition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Exponential error bounds in the composition of two factor lifts -/

namespace PolycyclicRecognition

theorem exists_thickened_factor_bridge_of_bounds
    {N D G V I Q : Type*} [Group N] [Group D] [Group G]
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (Exp : V → N) (ExpI : I → N) (qsec : Q → N)
    (vnorm : V → ℝ) (dnorm : D → ℝ) (ideal : I → Prop) (DF Extra : D → Prop)
    (cell : Set (N × D)) (u₂ : N) (d₂ : D) (g : G)
    (RE RB A δ r : ℝ) (hRE : 0 ≤ RE) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (habsorb : ∀ v, vnorm v ≤ RE * Real.exp (((A + 1) * δ) * r) →
      ∃ i q, u₂ * φ d₂ (Exp v) = ExpI i * qsec q ∧ ideal i)
    (hD : ∀ d, dnorm d ≤ RB → DF (d₂ * d))
    (hbridge : ∃ ub db, ι ub * κ db = g ∧ Extra db ∧ ∀ z ∈ cell,
      (∃ v, Exp v = ub * φ db z.1 ∧ vnorm v ≤ RE * Real.exp (A * δ * r)) ∧
        dnorm (db * z.2) ≤ RB) :
    ∃ u d, ι u * κ d = (ι u₂ * κ d₂) * g ∧ ∀ z ∈ cell,
      (∃ i q, u * φ d z.1 = ExpI i * qsec q ∧ ideal i) ∧ DF (d * z.2) := by
  apply exists_thickened_factor_bridge φ ι κ hc Exp ExpI qsec
    (fun v => vnorm v ≤ RE * Real.exp (((A + 1) * δ) * r)) ideal
    (fun d => dnorm d ≤ RB) DF cell u₂ d₂ g habsorb hD
  obtain ⟨ub, db, hg, _, hb⟩ := hbridge
  refine ⟨ub, db, hg, ?_⟩
  intro z hz
  obtain ⟨⟨v, hv, hvbound⟩, hdb⟩ := hb z hz
  refine ⟨⟨v, hv, hvbound.trans ?_⟩, hdb⟩
  apply mul_le_mul_of_nonneg_left _ hRE
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hδ hr]

end PolycyclicRecognition

end OAI
