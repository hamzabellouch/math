import OAI.Combinatorics.BalancedRyser.Probability.ConditionalOrderVariance

namespace OAI

open scoped BigOperators ENNReal
namespace Balanced.ConditionalOrderLaw

theorem filter_uniform_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset Ω) (hs : s.Nonempty)
    (h : ∃ a ∈ (s : Set Ω), a ∈ (PMF.uniformOfFintype Ω).support) :
    (PMF.uniformOfFintype Ω).filter (s : Set Ω) h = PMF.uniformOfFinset s hs := by
  classical
  have hn : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs0 : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hsum : (∑' a : Ω, (s : Set Ω).indicator (PMF.uniformOfFintype Ω) a) =
      (s.card : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
    simp [tsum_fintype, Set.indicator, Finset.sum_ite_mem]
  ext a
  rw [PMF.filter_apply, hsum, PMF.uniformOfFinset_apply]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha, PMF.uniformOfFintype_apply, ite_eq_left ha]
    rw [ENNReal.mul_inv (Or.inl hs0) (Or.inl (ENNReal.natCast_ne_top _)), inv_inv]
    calc
      _ = (s.card : ℝ≥0∞)⁻¹ *
          ((Fintype.card Ω : ℝ≥0∞)⁻¹ * Fintype.card Ω) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top _), mul_one]
  · simp [ha]

open ConditionalOrderVariance MeasureTheory
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
omit [Field F] [Fintype F] in

theorem target_event_supported (U V : Finset (Line F)) (i x : U) :
    ∃ p ∈ {p : OrderPair U V | p.1 i = x},
      p ∈ (PMF.uniformOfFintype (OrderPair U V)).support := by
  exact ⟨(Equiv.swap i x, Equiv.refl V), by simp, by simp⟩
omit [Field F] [Fintype F] in

theorem conditioned_eq_filter (U V : Finset (Line F)) (i x : U) :
    conditionedOrderLaw U V i x =
      (PMF.uniformOfFintype (OrderPair U V)).filter
        {p | p.1 i = x} (target_event_supported U V i x) := by
  classical
  let s := (Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
    (Finset.univ : Finset (Equiv.Perm V))
  have hs : s.Nonempty := ⟨(Equiv.swap i x, Equiv.refl V), by simp [s]⟩
  have hset : (s : Set (OrderPair U V)) = {p | p.1 i = x} := by
    ext p
    simp [s]
  have hsupport : ∃ p ∈ (s : Set (OrderPair U V)),
      p ∈ (PMF.uniformOfFintype (OrderPair U V)).support := by
    rw [hset]
    exact target_event_supported U V i x
  change PMF.uniformOfFinset s hs = _
  have h := (filter_uniform_eq s hs hsupport).symm
  simpa only [hset] using h

omit [Field F] in

theorem target_event_probability (U V : Finset (Line F))
    [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
    (i x : U) :
    (PMF.uniformOfFintype (OrderPair U V)).toMeasure.real {p | p.1 i = x} =
      1 / (U.card : ℝ) := by
  classical
  rw [← integral_indicator_one (Set.to_countable _).measurableSet,
    PMF.uniformOfFintype, WithoutReplacement.integral_uniformOfFinset,
    ← Finset.univ_product_univ, Finset.expect_product]
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, Fintype.expect_const]
  simpa only [Fintype.card_coe] using PermutationSubsetLaw.target_probability i x

omit [Field F] in

theorem target_event_probability_pos (U V : Finset (Line F))
    [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
    (i x : U) :
    0 < (PMF.uniformOfFintype (OrderPair U V)).toMeasure.real {p | p.1 i = x} := by
  rw [target_event_probability]
  have hU : (0 : ℝ) < U.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨i.val, i.property⟩)
  positivity

omit [Field F] [Fintype F] [DecidableEq F] in

theorem uniform_pair_atom {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (a : α) (b : β) :
    PMF.uniformOfFintype (α × β) (a, b) =
      PMF.uniformOfFintype α a * PMF.uniformOfFintype β b := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (Or.inl (by exact_mod_cast Fintype.card_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _))

end Balanced.ConditionalOrderLaw

end OAI
