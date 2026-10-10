import OAI.NumberTheory.JointDickman.Amplification.CandidateAdditionClasses
import OAI.NumberTheory.JointDickman.Amplification.RegularTiltAverage
import OAI.NumberTheory.JointDickman.Amplification.AllLargeLowExpectation
import OAI.NumberTheory.JointDickman.Amplification.AllLargeHighExpectation

namespace OAI

/-! # The actual representation count under both tilted remainder laws -/

namespace JointDickman
open Finset Classical

noncomputable def tiltedCandidatePairCount (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (i t : Fin M) (A D : Finset ℕ) : ℝ :=
  regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (fun V =>
    ((candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)).card : ℝ)))

/-- The finite grid cover can be averaged without dropping either regularity
indicator. The opposite orientation is averaged in the opposite order. -/
theorem tiltedCandidatePairCount_le_classes
    {B L T H M : ℕ} {τ C K : ℝ} (hB : 5 ≤ B) (hL : 3 ≤ L)
    (hT : (T : ℝ) ≤ Real.exp B) (i t : Fin M) (A D : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) (hK : 0 ≤ K)
    (hsmall : ∀ U V : Finset ℕ, RegularPrimeSet B L τ C U → RegularPrimeSet B L τ C V →
      ((smallCandidateAlternatives B L T H τ C i t A D U V).card : ℝ) ≤ K) :
    tiltedCandidatePairCount B L T H τ C i t A D ≤ K +
      ∑ k ∈ Icc 4 L,
        (regularTiltAverage B L τ C D (fun V =>
          tiltedAllLargeLowPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) A D V) +
        regularTiltAverage B L τ C A (fun U =>
          tiltedAllLargeHighPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) D A U)) := by
  let small := fun U V => ((smallCandidateAlternatives B L T H τ C i t A D U V).card : ℝ)
  let lo := fun k U V => ((allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V).card : ℝ)
  let hi := fun k U V => ((allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U).card : ℝ)
  have hpoint (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset)
      (V : Finset ℕ) (hV : V ∈ (auxiliaryPrimes B \ D).powerset) :
      ((candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)).card : ℝ) ≤
        small U V+∑ k ∈ Icc 4 L, (lo k U V+hi k U V) := by
    dsimp only [small,lo,hi]
    exact_mod_cast candidatePairRepresentations_card_le_addition_classes (H := H) (τ := τ) (C := C) hB hL hT i t A D U V
      hA hD ((mem_powerset.mp hU).trans sdiff_subset) ((mem_powerset.mp hV).trans sdiff_subset)
  calc
    _ ≤ regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D
        (fun V => small U V+∑ k ∈ Icc 4 L, (lo k U V+hi k U V))) := by
      apply regularTiltAverage_mono
      intro U hU _
      apply regularTiltAverage_mono
      intro V hV _
      exact hpoint U hU V hV
    _ = regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (small U)) +
        ∑ k ∈ Icc 4 L,
          (regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (lo k U)) +
          regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (hi k U))) := by
      simp_rw [regularTiltAverage_add,regularTiltAverage_sum]
      simp_rw [regularTiltAverage_add]
    _ ≤ K+∑ k ∈ Icc 4 L,
          (regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (lo k U)) +
          regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (hi k U))) := by
      apply add_le_add _ le_rfl
      apply regularTiltAverage_bound hK
      intro U _ hUr
      apply regularTiltAverage_bound hK
      intro V _ hVr
      exact hsmall U V hUr hVr
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro k _
      rw [regularTiltAverage_comm B L τ C A D (lo k)]
      rfl

end JointDickman

end OAI
