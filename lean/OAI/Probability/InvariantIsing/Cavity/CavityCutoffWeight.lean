import OAI.Probability.InvariantIsing.Cavity.CavityCutoffZero
import OAI.Probability.InvariantIsing.Cavity.CavityContinuousReplicaTilt

namespace OAI

/-! A normalized spatial cutoff is multiplication of the cavity weight
by its indicator. This is the form used by finite-replica Haar limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma cavity_cutoff_weight_product {X : Type*} (w : X → ℝ) (s : Set X)
    (σ : Fin 2 → X) :
    (∏ i, s.indicator w (σ i)) =
      if ∀ i, σ i ∈ s then ∏ i, w (σ i) else 0 := by
  by_cases h : ∀ i, σ i ∈ s
  · simp only [ite_eq_left h]
    exact Finset.prod_congr rfl (fun i _ => indicator_of_mem (h i) w)
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact indicator_of_notMem hi w

theorem cavity_cutoff_replica_indicator {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      cavityWeightedReplicaMean ν (s.indicator (fun x => Real.exp (H x))) F := by
  have hz : (referencePartition ν H)^2 ≠ 0 :=
    pow_ne_zero _ (MeasureTheory.integral_exp_pos he).ne'
  have hn : (∫ σ : Fin 2 → X, Real.exp (∑ i, H (σ i)) *
      (if ∀ i, σ i ∈ s then F σ else 0) ∂Measure.pi (fun _ => ν)) =
      cavityWeightNumerator ν (s.indicator (fun x => Real.exp (H x))) F := by
    unfold cavityWeightNumerator
    apply integral_congr_ae
    exact ae_of_all _ fun σ => by
      dsimp only
      rw [cavity_cutoff_weight_product, Real.exp_sum]
      split_ifs <;> simp
  have hd : (∫ σ : Fin 2 → X, Real.exp (∑ i, H (σ i)) *
      (if ∀ i, σ i ∈ s then (1 : ℝ) else 0) ∂Measure.pi (fun _ => ν)) =
      (cavityWeightNormalizer ν (s.indicator (fun x => Real.exp (H x))))^2 := by
    have hf : (fun σ : Fin 2 → X => Real.exp (∑ i, H (σ i)) *
        (if ∀ i, σ i ∈ s then (1 : ℝ) else 0)) =
        fun σ => ∏ i, s.indicator (fun x => Real.exp (H x)) (σ i) := by
      funext σ
      rw [cavity_cutoff_weight_product, Real.exp_sum]
      split_ifs <;> simp
    rw [hf]
    simpa only [cavityWeightNormalizer, Fintype.card_fin] using
      integral_fintype_prod_eq_pow (ι := Fin 2) (μ := ν) (s.indicator (fun x => Real.exp (H x)))
  simp only [cavityCutoffReplicaMean, referenceReplicaMean, hn, hd]
  rw [div_div_div_cancel_right₀ hz]
  rfl

end InvariantIsing

end

end OAI
