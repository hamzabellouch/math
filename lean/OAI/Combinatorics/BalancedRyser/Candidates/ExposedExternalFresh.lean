import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePairCounts
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateWitnessProbability
import OAI.Combinatorics.BalancedRyser.Probability.ExposedWitnessProbability

namespace OAI

namespace Balanced.ExposedExternalFresh

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open MeasureTheory CandidateValidityWitness CandidateExposedWitness
open FreshWitnessProbability FreshTupleConstraints ExposedWitnessProbability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance externalFreshMeasurableSpace : MeasurableSpace F := ⊤

omit [Field F] in

theorem probability_eq_integral_indicator (law : PMF (MergedPairs F))
    (E : MergedPairs F → Prop) :
    (law.toOuterMeasure {M | E M}).toReal =
      ∫ M, (if E M then (1 : ℝ) else 0) ∂law.toMeasure := by
  rw [PMF.integral_eq_sum, PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun M _ => by
      by_cases h : E M
      · simpa [Set.indicator_apply, h] using law.apply_ne_top M
      · simp [h])]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : E M <;> simp [h]

theorem conditional_fresh_pair_integral_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (e : Direction F) (heD : e ∉ D) (heT : e ∉ generatorSet T)
    (x : Point F) (j : Fin 4) :
    (∫ M, (if PairWitness M e x (tuplePoint M T j) then (1 : ℝ) else 0)
      ∂(exposedLaw (D ∪ generatorSet T) a).toMeasure) ≤
      2 / (Fintype.card F : ℝ)^2 := by
  have heq := ConditionalRestriction.integral_eq_of_eq_on_support
    (exposedLaw (D ∪ generatorSet T) a)
    (fun M => if PairWitness M e x (tuplePoint M T j) then (1 : ℝ) else 0)
    (fun M => if PairWitness M e x (tuplePoint a T j) then (1 : ℝ) else 0) (by
      intro M hM
      have hp := CandidatePairs.tuplePoint_eq_of_generators T M a
        (fun d hd => exposedLaw_support_fixed (D ∪ generatorSet T) a M hM d
          (Finset.mem_union_right _ hd)) j
      rw [hp])
  rw [heq, ← probability_eq_integral_indicator
    (exposedLaw (D ∪ generatorSet T) a)
    (fun M => PairWitness M e x (tuplePoint a T j))]
  exact CandidateWitnessProbability.pairWitness_probability_le
    (D ∪ generatorSet T) a e (by simpa using And.intro heD heT) x _

theorem pinned_fresh_pair_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (i : Fin 4) (p : Point F) (hp : OnLine p S)
    (e : Direction F) (heD : e ∉ D) (heT : e ∉ generatorSet T)
    (x : Point F) (j : Fin 4) :
    ((exposedLaw D a).toOuterMeasure {M |
      (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p ∧
      PairWitness M e x (tuplePoint M T j)}).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
  let f : MergedPairs F → ℝ := fun M =>
    if (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p then 1 else 0
  let z : MergedPairs F → ℝ := fun M =>
    if PairWitness M e x (tuplePoint M T j) then 1 else 0
  have ht := CandidatePairs.exposed_integral_mul_le D (generatorSet T) a f z
    (2 / (Fintype.card F : ℝ)^2) 1 1 (by positivity)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; split_ifs <;> norm_num)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; split_ifs <;> norm_num)
    (by
      intro M N hMN
      have hpoints : tuplePoint M T = tuplePoint N T := by
        funext k
        exact CandidatePairs.tuplePoint_eq_of_generators T M N
          (fun d hd => hMN d (Finset.mem_union_right _ hd)) k
      simp only [f, hpoints])
    (fun y => conditional_fresh_pair_integral_le D y T e heD heT x j)
  have hf : (∫ M, f M ∂(exposedLaw D a).toMeasure) =
      (Fintype.card F : ℝ)⁻¹ ^ 5 := by
    rw [show (∫ M, f M ∂(exposedLaw D a).toMeasure) =
      ((exposedLaw D a).toOuterMeasure {M |
        (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p}).toReal from
      (by
        convert (probability_eq_integral_indicator (exposedLaw D a)
          (fun M => (∀ k, OnLine (tuplePoint M T k) S) ∧
            tuplePoint M T i = p)).symm using 1
        apply integral_congr_ae
        filter_upwards [] with M
        dsimp [f]
        split_ifs <;> rfl)]
    exact one_pinned_position_probability D a T hT hfresh S i p hp
  have heq :
      ((exposedLaw D a).toOuterMeasure {M |
        (∀ k, OnLine (tuplePoint M T k) S) ∧ tuplePoint M T i = p ∧
        PairWitness M e x (tuplePoint M T j)}).toReal =
      ∫ M, f M * z M ∂(exposedLaw D a).toMeasure := by
    rw [probability_eq_integral_indicator]
    apply integral_congr_ae
    filter_upwards [] with M
    dsimp [f, z]
    split_ifs <;> simp_all
  rw [heq]
  change (∫ M, f M * z M ∂(exposedLaw D a).toMeasure) ≤
    _ * (∫ M, f M ∂(exposedLaw D a).toMeasure) at ht
  rw [hf] at ht
  simpa only [div_eq_mul_inv, ← inv_pow, mul_assoc, ← pow_add] using ht

theorem successful_external_fresh_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) (T : FourTuple F)
    (hT : Function.Injective T.generator) (hfresh : ∀ i, T.generator i ∉ D)
    (S : Line F) (d : Direction F) (hdD : d ∈ D) (hd : d ≠ S.1)
    (e : Direction F) (heD : e ∉ D) (heT : e ∉ generatorSet T)
    (i j : Fin 4) :
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T S ∧
      ∃ x, OnLine x S ∧ PairWitness M d x (tuplePoint M T i) ∧
        PairWitness M e x (tuplePoint M T j)}).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
  let E (s : Bool) : Set (MergedPairs F) := {M |
    (∀ k, OnLine (tuplePoint M T k) S) ∧
    tuplePoint M T i = forcedPoint a S d (!s) ∧
    PairWitness M e (forcedPoint a S d s) (tuplePoint M T j)}
  calc
    _ ≤ ((exposedLaw D a).toOuterMeasure {M | ∃ s, M ∈ E s}).toReal := by
      apply real_probability_mono_support
      rintro M ⟨⟨hS, hw⟩, hM⟩
      obtain ⟨s, hs, ht⟩ := (exists_external_iff_forcedPoint hd
        (exposedLaw_support_fixed D a M hM d hdD) (hS.2.2.2 i)
        (fun x => PairWitness M e x (tuplePoint M T j))).mp hw
      exact ⟨s, hS.2.2.2, hs, ht⟩
    _ ≤ ∑ s : Bool, ((exposedLaw D a).toOuterMeasure (E s)).toReal :=
      probability_exists_le_sum _ _
    _ ≤ ∑ _s : Bool, 2 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
      apply Finset.sum_le_sum
      intro s _
      exact pinned_fresh_pair_probability_le D a T hT hfresh S i
        (forcedPoint a S d (!s)) (forcedPoint_on_target a S d hd (!s))
        e heD heT (forcedPoint a S d s) j
    _ = _ := by simp; ring

end
end Balanced.ExposedExternalFresh

end OAI
