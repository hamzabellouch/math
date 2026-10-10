import OAI.Combinatorics.BalancedRyser.Incidence.AffineInjectionGuards
import OAI.Combinatorics.BalancedRyser.Local.AlignedTokenPointLaw

namespace OAI

namespace Balanced.Local.TokenExposure

open AlignedListProbability PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def purposefulIndex (σ : Fin 4 → Bool) (j : Fin 4) (s : Bool) : Fin 4 :=
  if s = σ j then j else j - 1

def recordedLine (P : EqualityPattern b κ) (bits : Bits b) (i : Fin b)
    (e : DirectionToken b κ ↪ Direction F) (y : Fin 4 → Point F)
    (j : Fin 4) (s : Bool) : Line F :=
  lineThrough (e (Sum.inr (P.classOf i j))) (y (purposefulIndex (bits i) j s))

theorem recordedLine_generated (P : EqualityPattern b κ) (bits : Bits b)
    (p : Point F) (i : Fin b) (e : DirectionToken b κ ↪ Direction F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {j : Fin 4 // j ∈ freePositions J} → F) (j : Fin 4) (s : Bool) :
    recordedLine P bits i e
      (generatedPositions (tupleDirections P e i) (tupleDirections_adjacent P e i)
        (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
        (lineEval (e (Sum.inl i)) p) J hJ a x) j s =
    (e (Sum.inr (P.classOf i j)),
      generatedOffsets (tupleDirections P e i) (tupleDirections_adjacent P e i)
        (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
        (lineEval (e (Sum.inl i)) p) J hJ a x j s) := by
  rw [generatedOffsets_from_positions]
  simp only [recordedLine, purposefulIndex, lineThrough, tupleDirections]
  split_ifs <;> rfl

theorem new_generator_incidence_le (P : EqualityPattern b κ)
    (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∈ K)
    (hold : ∀ j ∈ J, Sum.inr (P.classOf i j) ∈ K)
    (a : (DirectionToken b κ ↪ Direction F) → Fin 4 → Bool → F)
    (ha : ∀ e f, (∀ t ∈ K, e t = f t) → ∀ j ∈ J, a e j = a f j)
    (j : Fin 4) (hnew : Sum.inr (P.classOf i j) ∉ K) (s : Bool) (r : Point F) :
    ((InjectionExposure.auxiliaryLaw K base (pointKernel P bits p i J hJ a)).toOuterMeasure
      {z | z.2 (purposefulIndex (bits i) j s) ≠ r ∧
        OnLine r (recordedLine P bits i z.1 z.2 j s)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  exact auxiliary_guarded_joining_probability_le K base (Sum.inr (P.classOf i j)) hnew
    (pointKernel P bits p i J hJ a)
    (pointKernel_dependsOnExposed P bits p i J hJ K htarget hold a ha)
    (fun y => y (purposefulIndex (bits i) j s)) (fun _ => r)

theorem new_generator_incidence_le_two_div (P : EqualityPattern b κ)
    (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∈ K)
    (hold : ∀ j ∈ J, Sum.inr (P.classOf i j) ∈ K)
    (a : (DirectionToken b κ ↪ Direction F) → Fin 4 → Bool → F)
    (ha : ∀ e f, (∀ t ∈ K, e t = f t) → ∀ j ∈ J, a e j = a f j)
    (j : Fin 4) (hnew : Sum.inr (P.classOf i j) ∉ K) (s : Bool) (r : Point F)
    (hK : K.card ≤ 5 * b) (hb : 10 * b ≤ Fintype.card F) :
    ((InjectionExposure.auxiliaryLaw K base (pointKernel P bits p i J hJ a)).toOuterMeasure
      {z | z.2 (purposefulIndex (bits i) j s) ≠ r ∧
        OnLine r (recordedLine P bits i z.1 z.2 j s)}).toReal ≤
      2 / (Fintype.card F : ℝ) :=
  (new_generator_incidence_le P bits p i J hJ K base htarget hold a ha j hnew s r).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b Fintype.card_pos hK hb)

end
end Balanced.Local.TokenExposure

end OAI
