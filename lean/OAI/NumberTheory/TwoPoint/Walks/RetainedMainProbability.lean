import OAI.NumberTheory.TwoPoint.Bounds.PaddingWitnessProbability

namespace OAI

/-! Baseline tuple reciprocals and the retained padding event pay every main prime exactly once. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem tuple_weight_mul_retained_main_probability_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B h : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (main : List SignedStep)
    (hS : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport main, ∃ i, p i = q) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (RetainedMainTests p S h B main) ≤
      ∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹ := by
  have hrecord : recordedWitnessWord main (fun i : Fin 0 => i.elim0) = main := by
    simp [recordedWitnessWord]
  have hc : ∀ q ∈ wordDivisorPrimeSupport
      (recordedWitnessWord main (fun i : Fin 0 => i.elim0)), ∃ i, p i = q := by
    simpa only [hrecord] using hcover
  have hb := tuple_weight_mul_padding_hybrid_probability_le 0 B h p hinj hp hpB S main
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) hS hc
  have he (x : ι → Fin B) :
      (RetainedMainTests p S h B main x ∧
        ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
          ∀ j : Fin 0, AttachedResiduePositiveWord p h j.elim0 j.elim0 B y) ↔
      RetainedMainTests p S h B main x := by
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, x, (fun _ _ => rfl), (fun j => j.elim0)⟩
  simpa only [he, hrecord] using hb

end TwoPointCorrelations

end OAI
