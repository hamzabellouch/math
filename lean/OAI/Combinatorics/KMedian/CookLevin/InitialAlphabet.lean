import Mathlib
import OAI.Combinatorics.KMedian.Machines.Box
import OAI.Combinatorics.KMedian.CookLevin.FiniteConstraints

namespace OAI

section Inline_PCPInitialAlphabet

namespace MetricKMedian.PCP
open Function Finset
open scoped Classical

namespace BinaryCSP
variable {V E A : Type} [Fintype E] [DecidableEq A] (C : BinaryCSP V E A)
omit [DecidableEq A] in
lemma rejection_zero_iff (a : V → A) : C.rejection a=0 ↔ C.Satisfies a := by
  rw [rejection,testRate_eq_zero_iff]
  simp only [not_not,Satisfies]
end BinaryCSP
namespace AlphabetReduction
variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))
omit [Fintype V] in
lemma binary_iff : (∃ a, (binary C).Satisfies a) ↔ ∃ a, C.Satisfies a := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨decoded C (IncidenceReduction.decoded a),?_⟩
    have h := binary_sound C a
    rw [(binary C).rejection_zero_iff _ |>.mpr ha] at h
    apply (C.rejection_zero_iff _).mp
    have hn := testRate_nonneg (fun e =>
      (decoded C (IncidenceReduction.decoded a) (C.left e),
        decoded C (IncidenceReduction.decoded a) (C.right e)) ∉ C.allowed e)
    change 0 ≤ C.rejection _ at hn
    linarith
  · rintro ⟨a,ha⟩
    exact binary_complete C a ha
end AlphabetReduction
namespace InitialAlphabet
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
def oneHot (a : A) : BitVector A := fun b => if b=a then 1 else 0
omit [Fintype A] [Nonempty A] in
lemma oneHot_injective : Injective (oneHot A) := by
  intro a b hab
  by_contra h
  have hh := congrFun hab a
  simp only [oneHot,ite_true,ite_eq_right h] at hh
  exact one_ne_zero hh
noncomputable def decode : BitVector A → A := invFun (oneHot A)
omit [Fintype A] in
lemma decode_oneHot : LeftInverse (decode A) (oneHot A) := leftInverse_invFun (oneHot_injective A)
variable {V E : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
noncomputable def bits : BinaryCSP V E (BitVector A) := C.pullLabels (decode A)
omit [Fintype V] [Fintype E] in
lemma bits_iff : (∃ a, (bits A C).Satisfies a) ↔ ∃ a, C.Satisfies a := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨decode A ∘ a,(C.pullLabels_satisfies (decode A) a).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨oneHot A ∘ a,C.pullLabels_complete (decode A) (oneHot A) (decode_oneHot A) a ha⟩
noncomputable def reduced := AlphabetReduction.binary (bits A C)
omit [Fintype V] in
lemma reduced_iff : (∃ a, (reduced A C).Satisfies a) ↔ ∃ a, C.Satisfies a :=
  (AlphabetReduction.binary_iff (bits A C)).trans (bits_iff A C)
variable [Nonempty E]
noncomputable instance edgeNonempty : Nonempty (AlphabetReduction.Test (E := E) (K := A) × Fin 4) :=
  inferInstance
noncomputable def box : Amplifier.Box := Amplifier.Box.ofCSP (reduced A C)
lemma box_iff : (box A C).Perfect ↔ ∃ a, C.Satisfies a :=
  (Amplifier.Box.ofCSP_iff (reduced A C)).trans (reduced_iff A C)
end InitialAlphabet
end MetricKMedian.PCP

end Inline_PCPInitialAlphabet

end OAI
