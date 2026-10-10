import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianCross

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianArraySquare
open StoppedSimpleIntegral BrownianFiltration StoppedBrownianSquare StoppedBrownianCross

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

private theorem finite_sum_martingale [IsFiniteMeasure P]
    (S : ι → ℝ≥0 → Ω → ℝ) (I : Finset ι)
    (hS : ∀ i ∈ I, Martingale (S i) F P) :
    Martingale (fun t ω => ∑ i ∈ I, S i t ω) F P := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      convert martingale_zero ℝ F P using 1
      funext t ω
      simp
  | @insert i I hi ih =>
      have hm := (hS i (Finset.mem_insert_self i I)).add
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))
      convert hm using 1
      funext t ω
      simp only [Finset.sum_insert hi, Pi.add_apply]

theorem finite_sum_compensated_square_martingale [IsFiniteMeasure P]
    (S A : ι → ℝ≥0 → Ω → ℝ)
    (hdiag : ∀ i, Martingale (fun t ω => S i t ω ^ 2 - A i t ω) F P)
    (hcross : Pairwise fun i j => Martingale (fun t ω => S i t ω * S j t ω) F P)
    (I : Finset ι) :
    Martingale (fun t ω => (∑ i ∈ I, S i t ω) ^ 2 - ∑ i ∈ I, A i t ω) F P := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      convert martingale_zero ℝ F P using 1
      funext t ω
      simp
  | @insert i I hi ih =>
      have hm := finite_sum_martingale (fun j t ω => S i t ω * S j t ω) I
        (fun j hj => hcross (fun heq => hi (heq ▸ hj)))
      convert ((hdiag i).add ih).add (Martingale.smul 2 hm) using 1
      funext t ω
      simp only [Finset.sum_insert hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum]
      ring

theorem stopped_brownian_array_square_martingale [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ)
    (hB : ∀ j, IsPreBrownianReal (B j) P)
    (hAd : ∀ j, StronglyAdapted F (B j))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω j => B j t ω - B j s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun j k =>
      IndepFun (fun ω => B j t ω - B j s ω) (fun ω => B k t ω - B k s ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[F (τ i)] (H j i))
    (K : ι → ℕ → ℝ) (hbound : ∀ j i, ∀ᵐ ω ∂P, ‖H j i ω‖ ≤ K j i)
    (I : Finset ι) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ j ∈ I, ∑ i ∈ Finset.range n,
        intervalSum (B j) (H j i) (τ i) (τ (i + 1)) t ω) ^ 2 -
      ∑ j ∈ I, ∑ i ∈ Finset.range n,
        H j i ω ^ 2 * ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ))) F P := by
  have hcoord (j : ι) (s t : ℝ≥0) (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => B j t ω - B j s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpast s t hst)
    have hm : Measurable[MeasurableSpace.comap
        (fun ω j => B j t ω - B j s ω) inferInstance]
        (fun ω j => B j t ω - B j s ω) := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hm).comap_le
  have hpair (j k : ι) (s t : ℝ≥0) (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => (B j t ω - B j s ω, B k t ω - B k s ω)) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpast s t hst)
    have hm : Measurable[MeasurableSpace.comap
        (fun ω j => B j t ω - B j s ω) inferInstance]
        (fun ω j => B j t ω - B j s ω) := measurable_iff_comap_le.mpr le_rfl
    exact (((measurable_pi_apply j).comp hm).prodMk
      ((measurable_pi_apply k).comp hm)).comap_le
  exact finite_sum_compensated_square_martingale
    (fun j t ω => ∑ i ∈ Finset.range n,
      intervalSum (B j) (H j i) (τ i) (τ (i + 1)) t ω)
    (fun j t ω => ∑ i ∈ Finset.range n,
      H j i ω ^ 2 * ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ)))
    (fun j => stopped_predictable_sum_square_martingale (hB j) (hAd j) (hcoord j)
      τ hτ (H j) (hH j) (K j) (hbound j) n)
    (fun j k hjk => stopped_brownian_sum_product_martingale (hB j) (hB k)
      (hAd j) (hAd k) (hpair j k) (fun s t hst => hind s t hst hjk)
      τ hτ (H j) (H k) (hH j) (hH k) (K j) (K k) (hbound j) (hbound k) n) I

end Problem367.StoppedBrownianArraySquare

end

end OAI
