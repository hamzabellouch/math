import OAI.Combinatorics.ProgressionColoring.Arrangement

namespace OAI

/-!
# Exact finite output families determined by affine comparisons

The output type may be infinite, for example an integer-valued floor word.
One representative is selected for each realized ternary sign vector. The
factorization hypothesis then proves that this finite image is exactly the
actual output image on the specified parameter domain. This proves finiteness
and a cardinality bound without assuming either conclusion about the outputs.
-/

universe uAlpha

namespace QuantitativeVanDerWaerden

theorem finite_outputs_of_comparisons {e s : ℕ} {α : Type uAlpha}
    (forms : Fin s → AffineForm e) (domain : Set (Fin e → ℝ))
    (out : (Fin e → ℝ) → α)
    (hfactor : ∀ x ∈ domain, ∀ y ∈ domain,
      signVector forms x = signVector forms y → out x = out y) :
    ∃ S : Finset α, (∀ w, w ∈ S ↔ ∃ x ∈ domain, out x = w) ∧
      S.card ≤ (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) := by
  classical
  let signs := realizedSigns forms domain
  have hrep : ∀ σ : signs, ∃ x ∈ domain, signVector forms x = σ.val := by
    intro σ
    exact (mem_realizedSigns forms domain σ.val).mp σ.property
  choose point hpoint hsign using hrep
  let outputs : Finset α := signs.attach.image (fun σ => out (point σ))
  refine ⟨outputs, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      change w ∈ signs.attach.image (fun σ => out (point σ)) at hw
      obtain ⟨σ, _, heq⟩ := Finset.mem_image.mp hw
      exact ⟨point σ, hpoint σ, heq⟩
    · rintro ⟨x, hx, rfl⟩
      let σ : signs := ⟨signVector forms x,
        (mem_realizedSigns forms domain _).mpr ⟨x, hx, rfl⟩⟩
      change out x ∈ signs.attach.image (fun σ => out (point σ))
      refine Finset.mem_image.mpr ⟨σ, Finset.mem_attach _ _, ?_⟩
      exact hfactor (point σ) (hpoint σ) x hx (hsign σ)
  · calc
      outputs.card ≤ signs.attach.card := Finset.card_image_le
      _ = signs.card := Finset.card_attach
      _ ≤ (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) :=
        card_realizedSigns_le forms domain

end QuantitativeVanDerWaerden

end OAI
