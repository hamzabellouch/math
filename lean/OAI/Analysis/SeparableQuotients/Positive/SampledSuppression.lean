import OAI.Analysis.SeparableQuotients.Positive.TupleSampling

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling
open MeasureTheory Set Filter
open scoped Classical BigOperators
variable {I X C K : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace C] [MeasurableSpace K]



lemma ae_finite_suppression
    {μ : Measure I} [IsProbabilityMeasure μ]
    {code : I → C} {Φ : C × K → ℝ} {R : UnitBall X → K}
    {f : I → StrongDual ℝ X}
    (hΦ : Measurable Φ)
    (heval : ∀ a x, Φ (code a, R x) = f a x)
    (hnull : ∀ x : UnitBall X, ∀ᵐ a ∂μ, f a x = 0)
    (n : ℕ) (c : Fin n → ℝ) (s : Finset (Fin n)) :
    ∀ᵐ t ∂orderedMeasure μ n,
      ‖∑ j ∈ s, c j • f (t j)‖ ≤ 2 * ‖∑ j, c j • f (t j)‖ := by
  let Y : FullTuple I n → K := fun t =>
    R (ballHalfNormer (∑ j ∈ s, c j • f (t j)))
  have hnullD : ∀ y ∈ Set.range R, ∀ᵐ a ∂μ, Φ (code a, y) = 0 := by
    rintro y ⟨x, rfl⟩
    simpa only [heval] using hnull x
  have hcross (i : Fin n) (hi : i ∉ s) :
      ∀ᵐ t ∂orderedMeasure μ n, f (t i) (halfNormer (∑ j ∈ s, c j • f (t j))) = 0 := by
    have hh := ordered_cross_vanishing hΦ hnullD i Y
      (fun t => Set.mem_range_self _) (by
        intro u v huv
        apply congrArg (fun g => R (ballHalfNormer g))
        apply Finset.sum_congr rfl
        intro j hj
        rw [huv j (fun h => hi (h ▸ hj))])
    simpa only [Y, heval, ballHalfNormer] using hh
  have hall : ∀ᵐ t ∂orderedMeasure μ n, ∀ i, i ∉ s →
      f (t i) (halfNormer (∑ j ∈ s, c j • f (t j))) = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : i ∈ s
    · exact Eventually.of_forall (fun _ h => False.elim (h hi))
    · exact (hcross i hi).mono (fun _ ht _ => ht)
  exact hall.mono (fun t ht => suppression_of_cross_vanishing (fun j => f (t j)) c s ht)


lemma real_suppression_of_rational {J V : Type*} [Fintype J]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (v : J → V) (s : Finset J)
    (hq : ∀ q : J → ℚ, ‖∑ j ∈ s, (q j : ℝ) • v j‖ ≤ 2 * ‖∑ j, (q j : ℝ) • v j‖) :
    ∀ c : J → ℝ, ‖∑ j ∈ s, c j • v j‖ ≤ 2 * ‖∑ j, c j • v j‖ := by
  have hd : DenseRange (fun q : J → ℚ => fun j => (q j : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  intro c
  refine hd.induction_on (p := fun c : J → ℝ =>
    ‖∑ j ∈ s, c j • v j‖ ≤ 2 * ‖∑ j, c j • v j‖) c ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · exact hq



lemma exists_sequence_suppression
    {μ : Measure I} [IsProbabilityMeasure μ]
    {code : I → C} {Φ : C × K → ℝ} {R : UnitBall X → K}
    {f : I → StrongDual ℝ X}
    (hΦ : Measurable Φ)
    (heval : ∀ a x, Φ (code a, R x) = f a x)
    (hnull : ∀ x : UnitBall X, ∀ᵐ a ∂μ, f a x = 0) :
    ∃ α : ℕ → I, ∀ n (c : Fin n → ℝ) (s : Finset (Fin n)),
      ‖∑ j ∈ s, c j • f (α j.val)‖ ≤ 2 * ‖∑ j, c j • f (α j.val)‖ := by
  let G : (n : ℕ) → FullTuple I n → Prop := fun n t =>
    ∀ (q : Fin n → ℚ) (s : Finset (Fin n)),
      ‖∑ j ∈ s, (q j : ℝ) • f (t j)‖ ≤ 2 * ‖∑ j, (q j : ℝ) • f (t j)‖
  have hG : ∀ n, ∀ᵐ t ∂orderedMeasure μ n, G n t := by
    intro n
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro s
    exact ae_finite_suppression hΦ heval hnull n (fun j => (q j : ℝ)) s
  obtain ⟨α, hα⟩ := exists_good_tuple_sequence μ G hG
  refine ⟨α, fun n c s => ?_⟩
  exact real_suppression_of_rational (fun j : Fin n => f (α j.val)) s
    (fun q => hα n q s) c
end SeparableQuotient.Positive.Sampling

end

end

end OAI
