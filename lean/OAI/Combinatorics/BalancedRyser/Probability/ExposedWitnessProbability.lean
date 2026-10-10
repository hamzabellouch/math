import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposedWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshTupleConstraints

namespace OAI

namespace Balanced.ExposedWitnessProbability

open CandidateValidityWitness CandidateExposedWitness FreshWitnessProbability
open FreshTupleConstraints
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in

theorem exposedLaw_support_fixed (D : Finset (Direction F)) (a M : MergedPairs F)
    (hM : M ∈ (exposedLaw D a).support) (d : Direction F) (hd : d ∈ D) :
    M d = a d := by
  exact ((PMF.mem_support_filter_iff _).mp hM).1 d hd

theorem real_probability_mono_support {Ω : Type*} (law : PMF Ω) {E G : Set Ω}
    (h : E ∩ law.support ⊆ G) :
    (law.toOuterMeasure E).toReal ≤ (law.toOuterMeasure G).toReal := by
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact law.tsum_coe_indicator_ne_top _
  · exact law.toOuterMeasure_mono h

theorem successful_opposite_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (d : Direction F) (hdD : d ∈ D) (hd : d ≠ S.1)
    (i : Fin 4) :
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T S ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))}).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
  let E (s : Bool) : Set (MergedPairs F) := {M |
    (∀ k, OnLine (tuplePoint M T k) S) ∧
    tuplePoint M T i = forcedPoint a S d s ∧
    tuplePoint M T (i + 2) = forcedPoint a S d (!s)}
  have hij : i ≠ i + 2 := by fin_cases i <;> decide
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal := by
      apply real_probability_mono_support
      rintro M ⟨⟨hS, hw⟩, hM⟩
      obtain ⟨s, hs, ht⟩ := (successful_opposite_iff_fixed_positions hS hd
        (exposedLaw_support_fixed D a M hM d hdD) i).mp hw
      exact ⟨s, hS.2.2.2, hs, ht⟩
    _ ≤ ∑ s : Bool, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      have hE (s : Bool) : ((exposedLaw D a).toOuterMeasure (E s)).toReal =
          (Fintype.card F : ℝ)⁻¹ ^ 6 :=
        two_pinned_positions_probability D a T hT hfresh S i (i + 2) hij
          _ _ (forcedPoint_on_target a S d hd s)
          (forcedPoint_on_target a S d hd (!s))
      simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_ofNat]

theorem successful_external_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (d : Direction F) (hdD : d ∈ D) (hd : d ≠ S.1)
    (i : Fin 4) (R : MergedPairs F → Point F → Prop) :
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T S ∧
      ∃ x, OnLine x S ∧ PairWitness M d x (tuplePoint M T i) ∧ R M x}).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  let E (s : Bool) : Set (MergedPairs F) := {M |
    (∀ k, OnLine (tuplePoint M T k) S) ∧
    tuplePoint M T i = forcedPoint a S d (!s)}
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal := by
      apply real_probability_mono_support
      rintro M ⟨⟨hS, hw⟩, hM⟩
      obtain ⟨s, hs, _⟩ := (exists_external_iff_forcedPoint hd
        (exposedLaw_support_fixed D a M hM d hdD) (hS.2.2.2 i) (R M)).mp hw
      exact ⟨s, hS.2.2.2, hs⟩
    _ ≤ ∑ s : Bool, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      have hE (s : Bool) : ((exposedLaw D a).toOuterMeasure (E s)).toReal =
          (Fintype.card F : ℝ)⁻¹ ^ 5 :=
        one_pinned_position_probability D a T hT hfresh S i _
          (forcedPoint_on_target a S d hd (!s))
      simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_ofNat]

end
end Balanced.ExposedWitnessProbability

end OAI
