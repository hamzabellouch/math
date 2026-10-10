import OAI.NumberTheory.TwoPoint.Bounds.WeightedCenteredWord
import OAI.NumberTheory.TwoPoint.Bounds.ResidueCentering

namespace OAI

/-! Convert the full residue-weighted divisor word to its exact centered form. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem uniform_weighted_divisor_word_average {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (offset : τ → ℤ) (R G : (ι → Fin B) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R z * (∏ t,
        ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
          (p (label t) : ℝ)⁻¹)) * G z) =
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R z * (∏ t,
        ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
          then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G z) := by
  have he := uniform_divisor_word_average B p hp hpB label offset 1 (fun z => R z * G z)
  have hl : (fun z : ι → Fin B => R z * (∏ t,
      ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
        (p (label t) : ℝ)⁻¹)) * G z) =
      (fun z => (1 : ℝ) * (∏ t,
      ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
        (p (label t) : ℝ)⁻¹)) * (R z * G z)) := by
    funext z
    ring
  have hr : (fun z : ι → Fin B => R z * (∏ t,
      ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
        then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G z) =
      (fun z => (1 : ℝ) * (∏ t,
      ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
        then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * (R z * G z)) := by
    funext z
    ring
  rw [hl, hr]
  exact he

end TwoPointCorrelations

end OAI
