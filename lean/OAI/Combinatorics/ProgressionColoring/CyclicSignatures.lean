import OAI.Combinatorics.ProgressionColoring.Perturbation
import OAI.Combinatorics.ProgressionColoring.KeyMultiplicity
import OAI.Combinatorics.ProgressionColoring.SignatureCounting

namespace OAI

/-!
# Literal signatures of the actual affine cyclic progressions

The family below is defined from the actual centered representative sequence.
Its signatures retain the adaptive mesh's interval identities and the integer
norm band. The label color is fixed before the Bernoulli perturbation.
-/

noncomputable section

universe uU

namespace QuantitativeVanDerWaerden
namespace CyclicColoring

open SparsePerturbation

/-- The designated affine family is the actual nonzero-step family whose
centered representative vectors are affine in the sample index. -/
def affineProgressions (q D dilation k : ℕ) [NeZero (q ^ D)] :
    Finset (CyclicGroup q D × CyclicGroup q D) := by
  classical
  exact (nonzeroProgressions (q ^ D)).filter fun ad =>
    ∃ A B : Vec D, ∀ j : Fin k,
      yRep q D dilation (ad.1 + (j.val : CyclicGroup q D) * ad.2) =
        fun i => A i + (j.val : ℝ) * B i

theorem affineProgressions_subset (q D dilation k : ℕ) [NeZero (q ^ D)] :
    affineProgressions q D dilation k ⊆ nonzeroProgressions (q ^ D) := by
  classical
  exact Finset.filter_subset _ _

@[simp] theorem mem_affineProgressions {q D dilation k : ℕ} [NeZero (q ^ D)]
    (ad : CyclicGroup q D × CyclicGroup q D) :
    ad ∈ affineProgressions q D dilation k ↔ ad.2 ≠ 0 ∧
      ∃ A B : Vec D, ∀ j : Fin k,
        yRep q D dilation (ad.1 + (j.val : CyclicGroup q D) * ad.2) =
          fun i => A i + (j.val : ℝ) * B i := by
  classical
  simp [affineProgressions]

/-- The first-system labels together with the actual second-system boxes. -/
def actualFullLabel {U : Type uU} (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (first : CyclicGroup q D → Fin D → U) (n : CyclicGroup q D) :
    FullLabel D U mesh.Label :=
  (first n, secondBox mesh q D dilation n)

def actualFullLabelWord {U : Type uU} {k : ℕ}
    (mesh : AdaptiveMesh) (q D dilation : ℕ)
    (first : CyclicGroup q D → Fin D → U)
    (ad : CyclicGroup q D × CyclicGroup q D) : Fin k → FullLabel D U mesh.Label :=
  fun j => actualFullLabel mesh q D dilation first
    (ad.1 + (j.val : CyclicGroup q D) * ad.2)

/-- The actual signature count used by the sparse-perturbation budget. Its only
label-count term is the full nonzero-step cyclic label-word image. -/
theorem card_actual_affine_signatures_le {U : Type uU} [DecidableEq U]
    (mesh : AdaptiveMesh) (q D dilation k : ℕ) [NeZero (q ^ D)]
    (first : CyclicGroup q D → Fin D → U)
    (color : FullLabel D U mesh.Label → Bool) :
    ((affineProgressions q D dilation k).image (cyclicSignature (k := k)
      (fun n => color (actualFullLabel mesh q D dilation first n))
      (perturbationKey mesh q D dilation))).card ≤
      ((nonzeroProgressions (q ^ D)).image
        (actualFullLabelWord (k := k) mesh q D dilation first)).card *
        (25 * (k * (D * q ^ 2 + 1) + 1) ^ 8) := by
  classical
  have hcount := card_affine_yRep_fullLabel_signatures_le
    (affineProgressions q D dilation k)
    (actualFullLabelWord (k := k) mesh q D dilation first)
    (fun ad j => ad.1 + (j.val : CyclicGroup q D) * ad.2) color
    (show ∀ ad ∈ affineProgressions q D dilation k, ∃ A B : Vec D, ∀ j : Fin k,
      (fun i => (q : ℝ) * yRep q D dilation
        (ad.1 + (j.val : CyclicGroup q D) * ad.2) i) =
          fun i => A i + (j.val : ℝ) * B i from by
      intro ad had
      obtain ⟨A, B, hAB⟩ := ((mem_affineProgressions ad).mp had).2
      refine ⟨fun i => (q : ℝ) * A i, fun i => (q : ℝ) * B i, ?_⟩
      intro j
      funext i
      rw [hAB j]
      ring)
  have hlabels :
      ((affineProgressions q D dilation k).image
        (actualFullLabelWord (k := k) mesh q D dilation first)).card ≤
      ((nonzeroProgressions (q ^ D)).image
        (actualFullLabelWord (k := k) mesh q D dilation first)).card :=
    Finset.card_le_card (Finset.image_subset_image (affineProgressions_subset q D dilation k))
  apply le_trans _ (Nat.mul_le_mul_right _ hlabels)
  simpa +instances +unfoldPartialApp only [cyclicSignature, actualFullLabelWord, actualFullLabel, literalSignature,
    perturbationKey, yGeometricKey, geometricKey, scaledYRep] using hcount

end CyclicColoring
end QuantitativeVanDerWaerden

end

end OAI
