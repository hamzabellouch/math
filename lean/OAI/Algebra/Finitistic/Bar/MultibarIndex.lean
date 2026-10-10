import OAI.Algebra.Finitistic.Bar.MultibarBlocks

namespace OAI
namespace DerivedBar.Multibar


/-- Add one D slot in block j. Every nonzero block differential starts at such a tuple. -/
def increment : (r : ℕ) → Blocks r → Fin (r+1) → Blocks r
  | 0, i, _ => Nat.succ i
  | r+1, (i, tail), j =>
      Fin.cases (i+1, tail) (fun j => (i, increment r tail j)) j

/-- Number of D entries strictly before block j, the ordinary totalization offset. -/
def blockOffset : (r : ℕ) → Blocks r → Fin (r+1) → ℕ
  | 0, _, _ => 0
  | r+1, (i, tail), j => Fin.cases 0 (fun j => i + blockOffset r tail j) j

/-- The degree drops by one under a nonzero face in any block. -/
theorem total_increment (r : ℕ) (b : Blocks r) (j : Fin (r+1)) :
    total r (increment r b j) = total r b + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · change (i+1) + total r tail = i + total r tail + 1
      omega
    · change i + total r (increment r tail j) = i + total r tail + 1
      rw [ih]
      omega

/-- The exponent changes by r-j when a face removes a D slot in block j. -/
theorem exponent_increment (r : ℕ) (b : Blocks r) (j : Fin (r+1)) :
    exponent r (increment r b j) = exponent r b + (r-j.val) := by
  induction r with
  | zero => simp [exponent]
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · change (r+1) * (i+1) + exponent r tail = (r+1) * i + exponent r tail + (r+1)
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    · change (r+1) * i + exponent r (increment r tail j) =
        (r+1) * i + exponent r tail + ((r+1) - (j.val+1))
      rw [ih]
      omega

/-- Equality of the actual scalar coefficients for each signed block face.
The left side applies the rescaling followed by the shifted multibar sign;
the right side applies the absolute bar sign followed by the target rescaling.
`ell` is the local bar-face number, and the offset `blockOffset` counts earlier D slots. -/
theorem face_sign {k : Type*} [Field k] (r : ℕ) (b : Blocks r)
    (j : Fin (r+1)) (ell : ℕ) :
    (-1 : k)^(exponent r (increment r b j)) *
        (-1 : k)^(r + blockOffset r b j + ell) =
      (-1 : k)^(j.val + blockOffset r b j + ell) * (-1 : k)^(exponent r b) := by
  rw [exponent_increment, ← pow_add, ← pow_add]
  have hj : j.val ≤ r := by omega
  have he : exponent r b + (r-j.val) + (r + blockOffset r b j + ell) =
      j.val + blockOffset r b j + ell + exponent r b + 2*(r-j.val) := by omega
  rw [he, pow_add, pow_mul]
  simp

/-- Raise the first block length. -/
def leadingBase : (r : ℕ) → Blocks r → Blocks r
  | 0, i => Nat.succ i
  | _+1, (i, tail) => (i+1, tail)

@[simp] theorem pattern_leadingBase (r : ℕ) (b : Blocks r) :
    pattern r (leadingBase r b) = false :: pattern r b := by
  cases r with
  | zero => exact List.replicate_succ
  | succ r => rcases b with ⟨i, tail⟩
              simp [leadingBase, pattern, List.replicate_succ]

/-- Parse any word into its unique consecutive D blocks. -/
def parse : (p : List Bool) → Blocks (count p)
  | [] => (0 : ℕ)
  | false :: p => leadingBase (count p) (parse p)
  | true :: p => (0, parse p)

/-- Every D/X word has a block-length description, including zero-length blocks. -/
@[simp] theorem pattern_parse (p : List Bool) : pattern (count p) (parse p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b <;> simp [parse, count, pattern, ih]

/-- Block indices of bounded total degree form a finite type. -/
theorem finite_bounded (r m : ℕ) : Finite {b : Blocks r // total r b ≤ m} := by
  induction r with
  | zero =>
    exact Finite.of_injective (fun b => (⟨b.val, Nat.lt_succ_of_le b.property⟩ : Fin (m+1)))
      (fun a b h => Subtype.ext (Fin.mk.inj h))
  | succ r ih =>
    have := ih
    let f : {b : Blocks (r+1) // total (r+1) b ≤ m} →
        Fin (m+1) × {b : Blocks r // total r b ≤ m} := fun b =>
      (⟨b.val.1, by have h := b.property; change b.val.1 + total r b.val.2 ≤ m at h; omega⟩,
       ⟨b.val.2, by have h := b.property; change b.val.1 + total r b.val.2 ≤ m at h; omega⟩)
    apply Finite.of_injective f
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.mk.inj (congrArg Prod.fst h)
    · exact congrArg Subtype.val (congrArg Prod.snd h)

/-- The fixed-r multibar uses finitely many block tensors in every total degree. -/
theorem finite_degree (r n : ℕ) : Finite {b : Blocks r // r + total r b = n} := by
  have := finite_bounded r n
  exact Finite.of_injective
    (fun b : {b : Blocks r // r + total r b = n} =>
      (⟨b.val, by have h := b.property; omega⟩ : {b : Blocks r // total r b ≤ n}))
    (fun a b h => Subtype.ext (congrArg (fun x : {b : Blocks r // total r b ≤ n} => x.val) h))
end DerivedBar.Multibar

end OAI
