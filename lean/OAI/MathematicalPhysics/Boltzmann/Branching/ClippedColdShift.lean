import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdFiniteLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdTime
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative

namespace OAI

section

/-! # Vanishing components in the clipped and normalized cold construction -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedColdPicard_zero (q b L T : ℝ) {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) (n : ℕ) : clippedColdPicard q b L T F 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [clippedColdPicard,ih,coldForcing_zero]
    simp [PositiveIntegral.value,min_eq_right (hF u)]

theorem clippedColdLimit_zero (q b L T : ℝ) {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) : clippedColdLimit q b L T F 0 = 0 := by
  funext u
  simp [clippedColdLimit,clippedColdPicard_zero q b L T hF]

theorem normalizedFamily_zero {I : Type*} (F : ℝ × JetPrototype.Phase → ℝ)
    {c : I → ℝ × JetPrototype.Phase → ℝ} {i : I} (hi : c i = 0) :
    normalizedFamily F c i = 0 := by
  funext u
  simp [normalizedFamily,hi]

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Geometric barriers for spatially translated clipped cold solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_shifted_envelope {q b L T R K α γ s d : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) (y : Space)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (hseed : ∀ p, VelocityWeight.H q p.2*c₀ p ≤ density η K α γ s d a (shift y p))
    {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (clippedColdLimit q b L T F c₀) (t,p) ≤
      JetSupersolution.U η K α γ s d t a (shift y p) := by
  have hs' (u) : VelocityWeight.H q u.2*c₀ (shift (-y) u) ≤ density η K α γ s d a u := by
    have h := hseed (shift (-y) u)
    change VelocityWeight.H q u.2*c₀ (shift (-y) u) ≤
      density η K α γ s d a (shift y (shift (-y) u)) at h
    rwa [shift_shift_neg] at h
  have h := clippedCold_envelope hq hb hL hT hR hloss hK hα hγ hs hd hTmax hε η a
    (measurable_pull hFm (-y)) (hc₀m.comp (measurable_shift (-y)))
    (fun u => hF (u.1,shift (-y) u.2)) (fun u => hc₀ (shift (-y) u)) hs' t ht (shift y p)
  change VelocityWeight.H q p.2 *
    clippedColdLimit q b L T (pull (-y) F) (fun u => c₀ (shift (-y) u)) (t,shift y p) ≤ _ at h
  rw [clippedColdLimit_pull] at h
  change VelocityWeight.H q p.2 * clippedColdLimit q b L T F c₀ (t,shift (-y) (shift y p)) ≤ _ at h
  rwa [shift_neg_shift] at h

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
