import OAI.Combinatorics.BalancedRyser.Probability.ConditionalOrderVariance
import OAI.Combinatorics.BalancedRyser.Profiles.MarkedExposure
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionConcentration

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace Balanced.ProfileMarkedOrders

open ConditionalOrderVariance UncoveredSampling PermutationSubsetLaw

section FiniteLaws

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

theorem expect_pair_by_target (i : α)
    (f : Equiv.Perm α × Equiv.Perm β → ℝ) :
    (𝔼 p, f p) = 𝔼 x : α,
      𝔼 p ∈ (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)) ×ˢ
        (Finset.univ : Finset (Equiv.Perm β)), f p := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  rw [expect_by_target i]
  apply Finset.expect_congr rfl
  intro x _
  exact (Finset.expect_product _ _ _).symm

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem real_uniform_event (s : Finset Ω) (hs : s.Nonempty) (E : Set Ω) :
    (PMF.uniformOfFinset s hs).toMeasure.real E =
      𝔼 p ∈ s, if p ∈ E then (1 : ℝ) else 0 := by
  classical
  rw [← integral_indicator_one (Set.to_countable E).measurableSet,
    WithoutReplacement.integral_uniformOfFinset]
  rfl

theorem memLp_finite (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (p : ℝ≥0∞) : MemLp f p μ := by
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun ω => ‖f ω‖)
  exact MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => hC ⟨ω, rfl⟩))

end FiniteLaws

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def firstMark (U V : Finset (Line F)) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) (i : U) (p : OrderPair U V) : Prop :=
  η < z i ∧ ε < |targetFraction (p.1 i).val
      (populationLines U ((I i).map p.1.toEmbedding))
      (populationLines V ((J i).map p.2.toEmbedding)) -
    planeFraction (populationLines U ((I i).map p.1.toEmbedding))
      (populationLines V ((J i).map p.2.toEmbedding))|

def firstMarkCount (U V : Finset (Line F)) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) (p : OrderPair U V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => firstMark U V I J z η ε i p)).card

theorem firstMarkCount_le (U V : Finset (Line F))
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ) (η ε : ℝ)
    (p : OrderPair U V) : firstMarkCount U V I J z η ε p ≤ U.card := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem firstMarkCount_antitone (U V : Finset (Line F))
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ)
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') (p : OrderPair U V) :
    firstMarkCount U V I J z η' ε' p ≤ firstMarkCount U V I J z η ε p := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hmark⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, hη.trans_lt hmark.1, hε.trans_lt hmark.2⟩

theorem mean_firstMarkCount_eq_sum (U V : Finset (Line F))
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ) (η ε : ℝ) :
    (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) =
      ∑ i : U, 𝔼 p : OrderPair U V,
        if firstMark U V I J z η ε i p then (1 : ℝ) else 0 := by
  classical
  simp only [firstMarkCount, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter]
  exact Finset.expect_sum_comm _ _ _

variable (U V : Finset (Line F))
  [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]

def targetMarkEvent (I : Finset U) (J : Finset V) (x : U) (ε : ℝ) :
    Set (OrderPair U V) := {p | ε < |targetFraction x.val
      (populationLines U (I.map p.1.toEmbedding))
      (populationLines V (J.map p.2.toEmbedding)) -
    planeFraction (populationLines U (I.map p.1.toEmbedding))
      (populationLines V (J.map p.2.toEmbedding))|}

theorem mean_firstMark_eq_conditioned (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) (i : U) :
    (𝔼 p : OrderPair U V,
      if firstMark U V I J z η ε i p then (1 : ℝ) else 0) =
    if η < z i then
      𝔼 x : U, (conditionedOrderLaw U V i x).toMeasure.real
        (targetMarkEvent U V (I i) (J i) x ε)
    else 0 := by
  classical
  by_cases hz : η < z i
  · simp only [ite_eq_left hz]
    rw [expect_pair_by_target i]
    apply Finset.expect_congr rfl
    intro x _
    erw [conditionedOrderLaw, real_uniform_event]
    apply Finset.expect_congr rfl
    intro p hp
    have hx : p.1 i = x := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    simp only [firstMark, hz, true_and, targetMarkEvent, Set.mem_ofPred_eq, hx]
    rfl
  · simp [firstMark, hz]

theorem mean_firstMarkCount_eq_conditioned_sum
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ) (η ε : ℝ) :
    (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) =
      ∑ i : U, if η < z i then
        𝔼 x : U, (conditionedOrderLaw U V i x).toMeasure.real
          (targetMarkEvent U V (I i) (J i) x ε)
      else 0 := by
  rw [mean_firstMarkCount_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => mean_firstMark_eq_conditioned U V I J z η ε i)

def targetStatistic (I : Finset U) (J : Finset V) (x : U)
    (p : OrderPair U V) : ℝ :=
  targetFraction x.val (populationLines U (I.map p.1.toEmbedding))
    (populationLines V (J.map p.2.toEmbedding))

def planeStatistic (I : Finset U) (J : Finset V) (p : OrderPair U V) : ℝ :=
  planeFraction (populationLines U (I.map p.1.toEmbedding))
    (populationLines V (J.map p.2.toEmbedding))

def conditionalMean (i x : U) (f : OrderPair U V → ℝ) : ℝ :=
  𝔼 p ∈ (Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
    (Finset.univ : Finset (Equiv.Perm V)), f p

omit [Field F] [Fintype F] in
theorem integral_conditioned_eq (i x : U) (f : OrderPair U V → ℝ) :
    (∫ p, f p ∂(conditionedOrderLaw U V i x).toMeasure) =
      conditionalMean U V i x f := by
  exact WithoutReplacement.integral_uniformOfFinset _ _ f

theorem detection_le_targetMark_add_error (hUV : Disjoint U V)
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I)
    (a b ε : ℝ) (hε : 0 < ε)
    (hXa : |conditionalMean U V i x (targetStatistic U V I J x) - a| ≤ ε / 2)
    (hYb : |conditionalMean U V i x (planeStatistic U V I J) - b| ≤ ε / 2) :
    (if 3 * ε < |a - b| then (1 : ℝ) else 0) ≤
      (conditionedOrderLaw U V i x).toMeasure.real (targetMarkEvent U V I J x ε) +
        32 * ((I.card : ℝ) + J.card) /
          ((Fintype.card F : ℝ)^2 * ε^2) := by
  let μ := (conditionedOrderLaw U V i x).toMeasure
  let X := targetStatistic U V I J x
  let Y := planeStatistic U V I J
  have hX : MemLp X 2 μ := memLp_finite μ X 2
  have hY : MemLp Y 2 μ := memLp_finite μ Y 2
  have hXt : |(∫ p, X p ∂μ) - a| ≤ ε / 2 := by
    simpa only [μ, X, integral_conditioned_eq] using hXa
  have hYt : |(∫ p, Y p ∂μ) - b| ≤ ε / 2 := by
    simpa only [μ, Y, integral_conditioned_eq] using hYb
  have hVX : variance X μ ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 :=
    target_conditioned_order_measure_variance_le U V hUV I J i x hi
  have hVY : variance Y μ ≤
      4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 :=
    plane_conditioned_order_measure_variance_le U V I J i x hi
  have herr : 4 * (variance X μ + variance Y μ) / ε^2 ≤
      32 * ((I.card : ℝ) + J.card) / ((Fintype.card F : ℝ)^2 * ε^2) := by
    calc
      _ ≤ 4 * (4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 +
          4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2) / ε^2 := by
        gcongr
      _ = _ := by ring
  by_cases hgap : 3 * ε < |a - b|
  · simp only [ite_eq_left hgap]
    have hd := ProfileDetectionConcentration.marked_probability_ge_of_profile_gap
      hX hY hε hgap hXt hYt
    change 1 - 4 * (variance X μ + variance Y μ) / ε^2 ≤
      (conditionedOrderLaw U V i x).toMeasure.real (targetMarkEvent U V I J x ε) at hd
    linarith
  · simp only [ite_eq_right hgap]
    exact add_nonneg measureReal_nonneg (by positivity)

theorem detection_sum_le_mean_firstMarkCount_add_error (hUV : Disjoint U V)
    (I : U → Finset U) (J : U → Finset V) (z : U → ℝ)
    (hi : ∀ i, i ∉ I i) (a b : U → U → ℝ) (η ε : ℝ) (hε : 0 < ε)
    (hXa : ∀ i x, η < z i →
      |conditionalMean U V i x (targetStatistic U V (I i) (J i) x) - a i x| ≤ ε / 2)
    (hYb : ∀ i x, η < z i →
      |conditionalMean U V i x (planeStatistic U V (I i) (J i)) - b i x| ≤ ε / 2) :
    (∑ i : U, if η < z i then
      (𝔼 x : U, if 3 * ε < |a i x - b i x| then (1 : ℝ) else 0) else 0) ≤
      (𝔼 p : OrderPair U V, (firstMarkCount U V I J z η ε p : ℝ)) +
        ∑ i : U, if η < z i then
          32 * (((I i).card : ℝ) + (J i).card) /
            ((Fintype.card F : ℝ)^2 * ε^2) else 0 := by
  rw [mean_firstMarkCount_eq_conditioned_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hz : η < z i
  · simp only [ite_eq_left hz]
    let : Nonempty U := ⟨i⟩
    have h := Finset.expect_le_expect (s := (Finset.univ : Finset U))
      (fun x _ => detection_le_targetMark_add_error U V hUV (I i) (J i) i x (hi i)
        (a i x) (b i x) ε hε (hXa i x hz) (hYb i x hz))
    simpa only [Finset.expect_add_distrib, Fintype.expect_const] using h
  · simp only [ite_eq_right hz, add_zero, le_refl]

omit [DecidableEq F] [MeasurableSpace (OrderPair U V)]
    [MeasurableSingletonClass (OrderPair U V)] in

theorem normalized_variance_error_le (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε C : ℝ) (hC : 0 ≤ C)
    (hsize : ∀ i, ((I i).card : ℝ) + (J i).card ≤ C * Fintype.card F) :
    (∑ i : U, if η < z i then
      32 * (((I i).card : ℝ) + (J i).card) /
        ((Fintype.card F : ℝ)^2 * ε^2) else 0) / Fintype.card F ≤
      32 * C * U.card / ((Fintype.card F : ℝ)^2 * ε^2) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ i : U, if η < z i then
      32 * (((I i).card : ℝ) + (J i).card) /
        ((Fintype.card F : ℝ)^2 * ε^2) else 0) ≤
      ∑ _i : U, 32 * (C * Fintype.card F) /
        ((Fintype.card F : ℝ)^2 * ε^2) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · gcongr
      exact hsize i
    · positivity
  calc
    _ ≤ (∑ _i : U, 32 * (C * Fintype.card F) /
        ((Fintype.card F : ℝ)^2 * ε^2)) / (Fintype.card F : ℝ) := by
      exact div_le_div_of_nonneg_right hsum hq.le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      field_simp

def markCount (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    (η ε : ℝ) (p : OrderPair U V) : ℕ :=
  firstMarkCount U V ID JD zD η ε p +
    firstMarkCount V U IC JC zC η ε p.swap

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in
theorem markCount_le (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    (η ε : ℝ) (p : OrderPair U V) :
    markCount U V ID JD zD IC JC zC η ε p ≤ U.card + V.card :=
  Nat.add_le_add (firstMarkCount_le U V ID JD zD η ε p)
    (firstMarkCount_le V U IC JC zC η ε p.swap)

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in
theorem markCount_antitone (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') (p : OrderPair U V) :
    markCount U V ID JD zD IC JC zC η' ε' p ≤
      markCount U V ID JD zD IC JC zC η ε p :=
  Nat.add_le_add (firstMarkCount_antitone U V ID JD zD hη hε p)
    (firstMarkCount_antitone V U IC JC zC hη hε p.swap)

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in
theorem mean_markCount_antitone (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    {η ε η' ε' : ℝ} (hη : η ≤ η') (hε : ε ≤ ε') :
    (𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η' ε' p : ℝ)) ≤
      𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η ε p : ℝ) := by
  apply Finset.expect_le_expect
  intro p _
  exact_mod_cast markCount_antitone U V ID JD zD IC JC zC hη hε p

omit [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)] in

theorem mean_markCount_eq_add (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ) (η ε : ℝ) :
    (𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η ε p : ℝ)) =
      (𝔼 p : OrderPair U V, (firstMarkCount U V ID JD zD η ε p : ℝ)) +
      (𝔼 p : OrderPair V U, (firstMarkCount V U IC JC zC η ε p : ℝ)) := by
  simp only [markCount, Nat.cast_add, Finset.expect_add_distrib]
  congr 1
  exact Fintype.expect_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

def orderLaw : PMF (OrderPair U V) := PMF.uniformOfFintype _

omit [Field F] [Fintype F] in
theorem integral_orderLaw_eq (f : OrderPair U V → ℝ) :
    (∫ p, f p ∂(orderLaw U V).toMeasure) = 𝔼 p : OrderPair U V, f p :=
  WithoutReplacement.integral_uniformOfFinset _ Finset.univ_nonempty f

theorem positive_mark_tail_of_mean_margin
    (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    (η ε ξ : ℝ) (hU : 0 < U.card) (hξ : 0 ≤ ξ)
    (hmean : (V.card : ℝ) + ξ ≤
      𝔼 p : OrderPair U V, (markCount U V ID JD zD IC JC zC η ε p : ℝ)) :
    ξ / (2 * U.card) ≤ (orderLaw U V).toMeasure.real
      {p | (V.card : ℝ) + ξ / 2 ≤
        (markCount U V ID JD zD IC JC zC η ε p : ℝ)} := by
  let X : OrderPair U V → ℝ := fun p => markCount U V ID JD zD IC JC zC η ε p
  apply MarkedExposure.measureReal_tail_lower_bound (orderLaw U V).toMeasure X
    V.card U.card ξ
  · exact memLp_one_iff_integrable.mp (memLp_finite _ X 1)
  · exact (Set.to_countable _).measurableSet
  · exact_mod_cast hU
  · exact hξ
  · apply Filter.Eventually.of_forall
    intro p
    have h := markCount_le U V ID JD zD IC JC zC η ε p
    dsimp only [X]
    exact_mod_cast h.trans_eq (Nat.add_comm _ _)
  · simpa only [integral_orderLaw_eq, X] using hmean

end Balanced.ProfileMarkedOrders

end

end OAI
