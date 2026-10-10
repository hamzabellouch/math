import OAI.Combinatorics.BalancedRyser.Local.AlignedProjectedExposure
import OAI.Combinatorics.BalancedRyser.Local.InjectionExposureMixture

namespace OAI

namespace Balanced.Local.TokenExposure
open AlignedListProbability PartialAlignment InjectionExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {Z : Type*} [Fintype Z]
variable [Nonempty (DirectionToken b κ ↪ Direction F)]

theorem original_projected_left_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j ∈ J)
    (K : Finset (DirectionToken b κ))
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i j) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    (((PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure
      {ez | (tupleDirections P ez.1 i j, a ez.2 j (bits i j)) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  apply original_probability_le_of_auxiliary K noise
  intro base
  exact projected_left_probability_le_two_div P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m hK hb

theorem original_projected_right_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j+1 ∈ J)
    (K : Finset (DirectionToken b κ))
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i (j+1)) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    (((PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind
      (fun e => (noise e).map (fun z => (e,z)))).toOuterMeasure
      {ez | (tupleDirections P ez.1 i (j+1), a ez.2 (j+1) (!(bits i (j+1)))) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  apply original_probability_le_of_auxiliary K noise
  intro base
  exact projected_right_probability_le_two_div P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m hK hb

end
end Balanced.Local.TokenExposure

end OAI
