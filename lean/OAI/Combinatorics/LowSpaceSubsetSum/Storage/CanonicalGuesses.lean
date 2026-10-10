import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSurvival
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerExecution

namespace OAI

/-! # Direct interval encoding of the three representation guesses

The stored natural is the lower endpoint plus the accepted bounded range
draw. This avoids enumerating a general finite type to decode a guess.
-/

noncomputable section
namespace LowSpaceSubsetSum.CanonicalGuesses

abbrev lower (n : ℕ) : ℕ := (mixerSize n + 5) / 6
abbrev upper (n : ℕ) : ℕ := mixerSize n / 4

def width (n : ℕ) : ℕ := upper n + 1 - lower n

theorem endpoints (n : ℕ) : lower n ≤ upper n := by
  unfold lower upper mixerSize
  omega

instance widthNeZero (n : ℕ) : NeZero (width n) := by
  have h := endpoints n
  exact ⟨by unfold width; omega⟩

def encode (n : ℕ) (i : Fin (width n)) : ↥(RepresentationSetup.guessRange n) :=
  ⟨lower n + i.val, by
    have hi := i.isLt
    have he := endpoints n
    simp only [RepresentationSetup.guessRange, Finset.mem_Icc]
    change lower n ≤ lower n + i.val ∧ lower n + i.val ≤ upper n
    unfold width at hi
    omega⟩

def encoding (n : ℕ) : Fin (width n) ≃ ↥(RepresentationSetup.guessRange n) where
  toFun := encode n
  invFun x := ⟨x.val - lower n, by
    have hx := x.property
    simp only [RepresentationSetup.guessRange, Finset.mem_Icc] at hx
    change lower n ≤ x.val ∧ x.val ≤ upper n at hx
    unfold width
    omega⟩
  left_inv i := by apply Fin.ext; change lower n + i.val - lower n = i.val; omega
  right_inv x := by
    apply Subtype.ext
    have hx := x.property
    simp only [RepresentationSetup.guessRange, Finset.mem_Icc] at hx
    change lower n ≤ x.val ∧ x.val ≤ upper n at hx
    change lower n + (x.val - lower n) = x.val
    omega

instance guessNonempty (n : ℕ) : Nonempty ↥(RepresentationSetup.guessRange n) :=
  ⟨encode n 0⟩

def coupling (n : ℕ) : SamplerCoupling ↥(RepresentationSetup.guessRange n) :=
  (finCoupling n (width n)).map (encoding n)

theorem coupling_uniform (n : ℕ) : (coupling n).idealLaw = FiniteLaw.uniform := by
  rw [coupling, SamplerCoupling.map_idealLaw, finCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (encoding n)

theorem coupling_failure (n : ℕ) : (coupling n).failure ≤ 1 / (2 : ℝ) ^ (n ^ 3) := by
  rw [coupling, SamplerCoupling.map_failure]
  exact finCoupling_failure n (width n)

def execution (n : ℕ) : SamplerExecution.Execution (coupling n) :=
  SamplerExecution.map (SamplerExecution.fin n (width n)) (encoding n)

theorem execution_bounded (n : ℕ) : (execution n).Bounded (n ^ 3) 0 :=
  SamplerExecution.map_bounded _ _ (SamplerExecution.fin_bounded n (width n))

end LowSpaceSubsetSum.CanonicalGuesses

end

end OAI
