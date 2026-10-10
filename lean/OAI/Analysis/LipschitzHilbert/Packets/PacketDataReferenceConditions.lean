import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCoefficient

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def referenceCondition (oldSlope newSlope referenceLength cone w : ℝ)
    (j : Fin N) (l : P.labels j) : Prop :=
  P.length j ≤ referenceLength ∧
    |oldSlope+P.rowSlope j l-newSlope| ≤ cone*w/P.length j

def referenceLabelsEquiv (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    P.referenceLabels oldSlope newSlope referenceLength cone w j ≃
      {l : P.labels j // P.referenceCondition oldSlope newSlope referenceLength cone w j l} where
  toFun := fun l => ⟨P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,by
    obtain ⟨h,hlen,hangle⟩ := (Finset.mem_filter.mp l.property).2
    exact ⟨hlen,hangle⟩⟩
  invFun := fun l => ⟨l.val.val,Finset.mem_filter.mpr
    ⟨l.val.property,⟨l.val.property,l.property⟩⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext (Subtype.ext rfl)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

/-- Nonzero frozen selector values force both shortness and narrow
angular membership. Any term annihilated by a zero frozen selector can
therefore be restricted exactly, including positive norm envelopes. -/
theorem sum_reference_frozen {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (c : ∀ l : P.labels j, Item j l → κ → ℂ)
    (f : ∀ l : P.labels j, Item j l → E)
    (hshort : ∀ l u k, c l u k ≠ 0 → P.length j ≤ referenceLength)
    (hsupport : ∀ l u k, c l u k ≠ 0 →
      |oldSlope+P.rowSlope j l-newSlope| ≤ cone*w/P.length j)
    (hvanish : ∀ l u, (∀ k, c l u k = 0) → f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  apply P.sum_referenceLabels_of_zero oldSlope newSlope referenceLength cone w j f
  intro l hout u
  apply hvanish l u
  intro k
  by_contra hn
  exact hout ⟨hshort l u k hn,hsupport l u k hn⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
