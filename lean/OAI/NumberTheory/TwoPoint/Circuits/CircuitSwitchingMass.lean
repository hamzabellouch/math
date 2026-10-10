import OAI.NumberTheory.TwoPoint.Circuits.CircuitWalkCode
import OAI.NumberTheory.TwoPoint.Circuits.CircuitFiniteCodes

namespace OAI

/-! The weighted injection bounds the probability of canonical query walks
of any specified length. The bound depends on term width and query count,
and is independent of the number of terms. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem canonicalWalk_probability {n w h : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ w)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    (restrictionLaw n p hp hp1.le).probability
        (fun ρ => ∃ bs, CanonicalDNFWalk F ρ bs ∧ DNFQueryBlock.length bs = h) ≤
      ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) ^ h * (2 * p / (1 - p)) ^ h := by
  let E := fun ρ : PartialAssignment n =>
    ∃ bs, CanonicalDNFWalk F ρ bs ∧ DNFQueryBlock.length bs = h
  let pick (ρ : PartialAssignment n) (he : E ρ) := Classical.choose he
  have hpick (ρ : PartialAssignment n) (he : E ρ) :
      CanonicalDNFWalk F ρ (pick ρ he) ∧ DNFQueryBlock.length (pick ρ he) = h :=
    Classical.choose_spec he
  let code (ρ : PartialAssignment n) (he : E ρ) : BoundedRestrictionCode w (2 * h) :=
    packRestrictionCode w (2 * h) (DNFQueryBlock.codes (pick ρ he))
      (by rw [← (hpick ρ he).2]; exact (hpick ρ he).1.codes_length_le)
      ((hpick ρ he).1.code_positions_le hF)
  let empty : BoundedRestrictionCode w (2 * h) :=
    ⟨⟨0, Nat.succ_pos _⟩, Fin.elim0⟩
  let encode (ρ : PartialAssignment n) : PartialAssignment n × BoundedRestrictionCode w (2 * h) :=
    if he : E ρ then (DNFQueryBlock.image ρ (pick ρ he), code ρ he) else (ρ, empty)
  have hinj : ∀ ρ, E ρ → ∀ τ, E τ → encode ρ = encode τ → ρ = τ := by
    intro ρ hρ τ hτ heq
    have heq' : (DNFQueryBlock.image ρ (pick ρ hρ), code ρ hρ) =
        (DNFQueryBlock.image τ (pick τ hτ), code τ hτ) := by
      simpa only [encode, dite_eq_left hρ, dite_eq_left hτ] using heq
    have hc := congrArg (fun z : PartialAssignment n × BoundedRestrictionCode w (2 * h) =>
      readRestrictionCode z.2) heq'
    simp only [code, read_packRestrictionCode] at hc
    exact (hpick ρ hρ).1.image_code_injective (hpick τ hτ).1 (congrArg Prod.fst heq') hc
  have hr : 0 ≤ (2 * p / (1 - p)) ^ h := by positivity
  have hw : ∀ ρ, E ρ → (restrictionLaw n p hp hp1.le).weight ρ ≤
      (2 * p / (1 - p)) ^ h * (restrictionLaw n p hp hp1.le).weight (encode ρ).1 := by
    intro ρ he
    have heq := (hpick ρ he).1.image_weight p hp hp1
    rw [(hpick ρ he).2] at heq
    simpa only [encode, dite_eq_left he] using heq.le
  have hprob := (restrictionLaw n p hp hp1.le).probability_le_of_encoding E encode
    ((2 * p / (1 - p)) ^ h) hr hinj hw
  apply hprob.trans
  apply mul_le_mul_of_nonneg_right _ hr
  exact_mod_cast boundedRestrictionCode_card_queries w h

end TwoPointCorrelations

end OAI
