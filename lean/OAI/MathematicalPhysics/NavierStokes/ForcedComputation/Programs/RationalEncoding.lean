import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RadixEncoding

namespace OAI

/-! The finite input supplies an actual rational coordinate to the loader. -/

namespace ForcedComputation.Radix

variable {A : Type*}

def prefixValueQ (B : ℚ) (digit : A → ℚ) : List A → ℚ :=
  List.rec 0 (fun a _ value => (digit a + value) / B)

def finiteCode (B : ℚ) (digit : A → ℚ) (w : List A) (blank : A) : ℚ :=
  prefixValueQ B digit w + B⁻¹ ^ w.length * (digit blank / (B - 1))

theorem prefixValueQ_cast (B : ℚ) (digit : A → ℚ) (w : List A) :
    (prefixValueQ B digit w : ℝ) = prefixValue B (fun a => (digit a : ℝ)) w := by
  induction w with
  | nil => simp [prefixValueQ, prefixValue]
  | cons a w ih =>
    change (((digit a + prefixValueQ B digit w) / B : ℚ) : ℝ) = _
    rw [Rat.cast_div, Rat.cast_add, ih]
    rfl

theorem finiteCode_spec {B : ℚ} (hB : 1 < B) {digit : A → ℚ}
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (w : List A) (blank : A) :
    encode (B : ℝ) (fun a => (digit a : ℝ)) (prependWord w (fun _ => blank)) =
      (finiteCode B digit w blank : ℝ) := by
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hdr : ∀ a, (0 : ℝ) ≤ digit a ∧ (digit a : ℝ) ≤ (B : ℝ) - 1 := by
    intro a
    constructor
    · exact_mod_cast (hd a).1
    · exact_mod_cast (hd a).2
  rw [encode_finite_input hBr hdr]
  simp only [finiteCode, Rat.cast_add, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_div, Rat.cast_sub, Rat.cast_one, prefixValueQ_cast]

end ForcedComputation.Radix

end OAI
