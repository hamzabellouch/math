import Mathlib.Data.List.Infix
import Mathlib.Data.List.Chain
import Mathlib.Tactic

namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations

structure SignedStep where
  forward : Bool
  tuple : ℕ
  padding : ℕ
  deriving DecidableEq

namespace SignedStep

def flip (a : SignedStep) : SignedStep := ⟨!a.forward, a.tuple, a.padding⟩

@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]

def displacement (h : ℕ) (a : SignedStep) : ℤ :=
  (if a.forward then 1 else -1) * (h : ℤ) * a.padding * a.tuple

def divisor (a : SignedStep) : ℤ := (a.padding : ℤ) * a.tuple

@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]

lemma divisor_dvd_displacement (h : ℕ) (a : SignedStep) : a.divisor ∣ a.displacement h := by
  refine ⟨(if a.forward then 1 else -1) * (h : ℤ), ?_⟩
  simp only [divisor, displacement]
  ring

@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl

lemma divisor_dvd_arrival (h : ℕ) (a : SignedStep) (x : ℤ) (hx : a.divisor ∣ x) :
    a.divisor ∣ x + a.displacement h := hx.add (a.divisor_dvd_displacement h)

/-- The exclusions on the common multiplier, padding, and tuple imply the
exact absence of this prime from the integer displacement. -/
lemma prime_not_dvd_displacement (h p : ℕ) (hp : p.Prime) (a : SignedStep)
    (hh : ¬p ∣ h) (hq : ¬p ∣ a.padding) (hd : ¬p ∣ a.tuple) :
    ¬(p : ℤ) ∣ a.displacement h := by
  have hn : ¬p ∣ h * a.padding * a.tuple := hp.not_dvd_mul (hp.not_dvd_mul hh hq) hd
  have hi : ¬(p : ℤ) ∣ ((h * a.padding * a.tuple : ℕ) : ℤ) := by exact_mod_cast hn
  rcases a with ⟨b, d, q⟩
  cases b <;> simpa [displacement, Int.natCast_mul, mul_assoc] using hi

end SignedStep

/-- Total displacement, with each visit counted in order. -/
def wordDisplacement (h : ℕ) (w : List SignedStep) : ℤ :=
  (w.map (SignedStep.displacement h)).sum

@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]

/-- Reversing a word reverses its order and its signs. -/
def reverseWord (w : List SignedStep) : List SignedStep := w.reverse.map SignedStep.flip

@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

/-- Exact positivity at every successive departure site. -/
def PositiveWord (h : ℕ) (x : ℤ) : List SignedStep → Prop
  | [] => True
  | a :: w => a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w

@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl

lemma positiveWord_append (h : ℕ) (x : ℤ) (u v : List SignedStep) :
    PositiveWord h x (u ++ v) ↔
      PositiveWord h x u ∧ PositiveWord h (x + wordDisplacement h u) v := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, positiveWord_cons, ih, wordDisplacement_cons]
      simp only [add_assoc, and_assoc]

/-- Positivity at arrivals makes reversed paths positive at their old endpoint. -/
lemma PositiveWord.reverse {h : ℕ} {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w) :
    PositiveWord h (x + wordDisplacement h w) (reverseWord w) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rcases hw with ⟨ha, hw⟩
      rw [reverseWord_cons, positiveWord_append]
      constructor
      · simpa only [wordDisplacement_cons, add_assoc] using ih hw
      · have hav := a.divisor_dvd_arrival h x ha
        simpa [PositiveWord, wordDisplacement_cons, add_assoc] using hav

/-- A main vertex is the endpoint of a prefix, including both extreme endpoints. -/
def WordVertex (h : ℕ) (x : ℤ) (w : List SignedStep) (y : ℤ) : Prop :=
  ∃ u v, w = u ++ v ∧ y = x + wordDisplacement h u

lemma WordVertex.reverse {h : ℕ} {x y : ℤ} {w : List SignedStep}
    (hy : WordVertex h (x + wordDisplacement h w) (reverseWord w) y) :
    WordVertex h x w y := by
  obtain ⟨u, v, huv, hy⟩ := hy
  have hsplit : w = reverseWord v ++ reverseWord u := by
    simpa only [reverseWord_reverseWord, reverseWord_append] using congrArg reverseWord huv
  refine ⟨reverseWord v, reverseWord u, hsplit, ?_⟩
  have hsum := congrArg (wordDisplacement h) huv
  simp only [wordDisplacement_reverseWord, wordDisplacement_append] at hsum ⊢
  omega

lemma PositiveWord.infix {h : ℕ} {x : ℤ} {u w : List SignedStep}
    (hw : PositiveWord h x w) (hu : u <:+: w) :
    ∃ y, WordVertex h x w y ∧ PositiveWord h y u := by
  obtain ⟨a, b, hab⟩ := hu
  have hpositive : PositiveWord h x (a ++ (u ++ b)) := by
    rw [← hab] at hw
    simpa only [List.append_assoc] using hw
  obtain ⟨_, hub⟩ := (positiveWord_append h x a (u ++ b)).mp hpositive
  refine ⟨x + wordDisplacement h a, ⟨a, u ++ b, by simpa only [List.append_assoc] using hab.symm, rfl⟩,
    ((positiveWord_append h (x + wordDisplacement h a) u b).mp hub).1⟩

/-- A contiguous subword in either orientation. -/
def OrientedInfix (u w : List SignedStep) : Prop := u <:+: w ∨ u <:+: reverseWord w

lemma OrientedInfix.refl (w : List SignedStep) : OrientedInfix w w := Or.inl (List.infix_refl _)

lemma reverseWord_infix {u w : List SignedStep} (hu : u <:+: w) :
    reverseWord u <:+: reverseWord w := hu.reverse.map SignedStep.flip

lemma OrientedInfix.trans {u v w : List SignedStep}
    (hu : OrientedInfix u v) (hv : OrientedInfix v w) : OrientedInfix u w := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact Or.inl (hu.trans hv)
  · exact Or.inr (hu.trans hv)
  · exact Or.inr (hu.trans (reverseWord_infix hv))
  · exact Or.inl (hu.trans (by simpa using reverseWord_infix hv))

lemma OrientedInfix.length_le {u w : List SignedStep} (hu : OrientedInfix u w) :
    u.length ≤ w.length := by
  rcases hu with hu | hu
  · exact hu.length_le
  · simpa using hu.length_le

lemma PositiveWord.orientedInfix {h : ℕ} {x : ℤ} {u w : List SignedStep}
    (hw : PositiveWord h x w) (hu : OrientedInfix u w) :
    ∃ y, WordVertex h x w y ∧ PositiveWord h y u := by
  rcases hu with hu | hu
  · exact hw.infix hu
  · obtain ⟨y, hy, hu⟩ := hw.reverse.infix hu
    exact ⟨y, hy.reverse, hu⟩

/-- Minimality refers to numerical words and permits reversing every shorter
contiguous subword. -/
def MinimalWord (P : List SignedStep → Prop) (w : List SignedStep) : Prop :=
  P w ∧ ∀ u, OrientedInfix u w → u.length < w.length → ¬P u

/-- Strictly decreasing lengths give a minimal prohibited contiguous word. -/
theorem exists_minimal_orientedInfix (P : List SignedStep → Prop) (w : List SignedStep)
    (hw : P w) : ∃ u, OrientedInfix u w ∧ MinimalWord P u := by
  classical
  have hex : ∃ n : ℕ, ∃ u, OrientedInfix u w ∧ u.length = n ∧ P u :=
    ⟨w.length, w, OrientedInfix.refl w, rfl, hw⟩
  obtain ⟨u, hu, hlen, hP⟩ := Nat.find_spec hex
  refine ⟨u, hu, hP, ?_⟩
  intro v hv hlt hPv
  have hmin := Nat.find_min' hex ⟨v, hv.trans hu, rfl, hPv⟩
  omega

/-- A tuple prime occurs when it divides the whole tuple at that position. -/
def TuplePrimeAt (w : List SignedStep) (p i : ℕ) : Prop :=
  p.Prime ∧ ∃ a, w[i]? = some a ∧ p ∣ a.tuple

def TuplePrimeIntervals (w : List SignedStep) : Prop :=
  ∀ p i j k, i ≤ j → j ≤ k → k < w.length →
    TuplePrimeAt w p i → TuplePrimeAt w p k → TuplePrimeAt w p j

/-- Exact numerical prohibition, with admissible tuple/padding pairs fixed. -/
def ForwardProhibited (h s : ℕ) (supply : ℕ → ℕ → Prop) (w : List SignedStep) : Prop :=
  3 ≤ w.length ∧ w.length ≤ s ∧
  (∀ a ∈ w, supply a.tuple a.padding) ∧
  w.IsChain (fun a b => a.tuple ≠ b.tuple) ∧ TuplePrimeIntervals w ∧
  ∃ p, TuplePrimeAt w p 0 ∧ ¬TuplePrimeAt w p (w.length - 1) ∧
    ∃ a, 0 < a ∧ a + 1 < w.length ∧ (p : ℤ) ∣ wordDisplacement h (w.drop a)

def ProhibitedWitness (h s : ℕ) (supply : ℕ → ℕ → Prop) (x : ℤ)
    (w : List SignedStep) : Prop :=
  PositiveWord h x w ∧ MinimalWord (ForwardProhibited h s supply) w

def ProhibitedSite (h s : ℕ) (supply : ℕ → ℕ → Prop) (x : ℤ) : Prop :=
  ∃ w, ProhibitedWitness h s supply x w

/-- Every positive prohibited path contains a witness beginning at a main
vertex. Reversing during descent may select either endpoint of a subword. -/
theorem PositiveWord.prohibited_witness {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w)
    (hpro : ForwardProhibited h s supply w) :
    ∃ y, WordVertex h x w y ∧ ProhibitedSite h s supply y := by
  obtain ⟨u, hu, hmin⟩ := exists_minimal_orientedInfix (ForwardProhibited h s supply) w hpro
  obtain ⟨y, hy, hpositive⟩ := hw.orientedInfix hu
  exact ⟨y, hy, u, hpositive, hmin⟩

/-- Surviving main vertices exclude every positive prohibited word. -/
theorem PositiveWord.not_prohibited {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {w : List SignedStep} (hw : PositiveWord h x w)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y) :
    ¬ForwardProhibited h s supply w := by
  intro hpro
  obtain ⟨y, hy, hbad⟩ := hw.prohibited_witness hpro
  exact hsurvive y hy hbad

/-- The same deletion excludes prohibited words contained in the path in
either orientation, by composing the two stages of witness descent. -/
theorem PositiveWord.not_prohibited_orientedInfix {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {x : ℤ} {u w : List SignedStep} (hw : PositiveWord h x w)
    (hsurvive : ∀ y, WordVertex h x w y → ¬ProhibitedSite h s supply y)
    (hu : OrientedInfix u w) : ¬ForwardProhibited h s supply u := by
  intro hpro
  obtain ⟨v, hv, hmin⟩ := exists_minimal_orientedInfix (ForwardProhibited h s supply) u hpro
  obtain ⟨y, hy, hpositive⟩ := hw.orientedInfix (hv.trans hu)
  exact hsurvive y hy ⟨v, hpositive, hmin⟩

end TwoPointCorrelations

end OAI
