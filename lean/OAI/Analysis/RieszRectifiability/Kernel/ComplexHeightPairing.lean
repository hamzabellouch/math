import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.HeightPairingRegions
import OAI.Analysis.RieszRectifiability.Rigidity.FiniteFractionalHeightPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

def complexHeightInteriorIntegrand {d : ℕ} (m : ℕ) (w : Ambient d → ℝ)
    (g : Ambient d → ℂ) (q : Ambient d × Ambient d) : ℂ :=
  (w q.1 - w q.2) • (inverseDistancePow (m + 1) q.1 q.2 • (g q.1 - g q.2))

def complexRenormalizedNormalIntegrand {d : ℕ} (m : ℕ) (w : Ambient d → ℝ)
    (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) : ℂ :=
  (w q.1 * inverseDistancePow (m + 1) q.1 q.2 -
    w q.2 * (inverseDistancePow (m + 1) q.1 q.2 - inverseDistancePow (m + 1) a q.2)) • g q.1

def complexHeightPairingOn {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ) : ℂ :=
  (1 / 2 : ℝ) • (∫ q, complexHeightInteriorIntegrand m w g q ∂(μ.restrict s).prod (μ.restrict s)) +
    ∫ q, complexRenormalizedNormalIntegrand m w g a q ∂(μ.restrict s).prod (μ.restrict sᶜ)

theorem complexHeightInteriorIntegrand_ofReal {d : ℕ} (m : ℕ)
    (w φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    complexHeightInteriorIntegrand m w (fun x => (φ x : ℂ)) q =
      (fractionalBilinear m w φ q.1 q.2 : ℂ) := by
  unfold complexHeightInteriorIntegrand fractionalBilinear inverseDistancePow
  simp only [Complex.real_smul]
  push_cast
  ring

theorem complexRenormalizedNormalIntegrand_ofReal {d : ℕ} (m : ℕ)
    (w φ : Ambient d → ℝ) (a : Ambient d) (q : Ambient d × Ambient d) :
    complexRenormalizedNormalIntegrand m w (fun x => (φ x : ℂ)) a q =
      (renormalizedNormalIntegrand m w φ a q : ℂ) := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  simp only [Complex.real_smul]
  push_cast
  ring

theorem complexHeightPairingOn_ofReal {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w φ : Ambient d → ℝ) :
    complexHeightPairingOn m μ a s w (fun x => (φ x : ℂ)) =
      (heightPairingOn m μ a s w φ : ℂ) := by
  unfold complexHeightPairingOn heightPairingOn
  simp_rw [complexHeightInteriorIntegrand_ofReal, complexRenormalizedNormalIntegrand_ofReal]
  rw [integral_complex_ofReal, integral_complex_ofReal]
  norm_num [Complex.real_smul]

end

end RieszRectifiability

end OAI
