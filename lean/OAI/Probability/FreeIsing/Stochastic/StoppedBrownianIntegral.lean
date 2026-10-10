import OAI.Probability.FreeIsing.Brownian.FiltrationIntegral
import OAI.Probability.FreeIsing.Stochastic.StoppedSimpleIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem martingale_of_independent_past
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    Martingale B F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨hAd, ?_⟩
  intro s t hst
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) (F s)
  have hself := condExp_of_stronglyMeasurable (F.le s) (hAd s) (hB.integrable_eval s)
  filter_upwards [hsub, increment_condExp_zero hB hAd (hind s t hst)] with ω hs hz
  change P[(fun ω => B t ω - B s ω) | F s] ω =
    P[B t | F s] ω - P[B s | F s] ω at hs
  rw [hz, hself] at hs
  linarith

theorem stopped_predictable_sum_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (s : Finset ℕ) (t : ℝ≥0) :
    (∫ ω, (∑ i ∈ s, StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) t ω) ^ 2 ∂P) =
      ∑ i ∈ s, ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ)) *
        ∫ ω, H i ω ^ 2 ∂P := by
  classical
  let σ : ℕ → ℝ≥0 := fun i => min t (τ i)
  let G : ℕ → Ω → ℝ := fun i => if τ i ≤ t then H i else 0
  have hσ : Monotone σ := fun i j hij => min_le_min_left t (hτ hij)
  have hG (i : ℕ) : StronglyMeasurable[F (σ i)] (G i) := by
    change StronglyMeasurable[F (min t (τ i))] (if τ i ≤ t then H i else 0)
    by_cases hi : τ i ≤ t
    · rw [ite_eq_left hi, min_eq_right hi]
      exact hH i
    · rw [ite_eq_right hi]
      exact stronglyMeasurable_zero
  have hG2 (i : ℕ) : MemLp (G i) 2 P := by
    by_cases hi : τ i ≤ t
    · simpa only [G, ite_eq_left hi] using hH2 i
    · simp only [G, ite_eq_right hi]
      exact MemLp.zero
  have hterm (i : ℕ) (ω : Ω) :
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) t ω =
        G i ω * (B (σ (i + 1)) ω - B (σ i) ω) := by
    by_cases hi : τ i ≤ t
    · simp only [G, ite_eq_left hi, σ, StoppedSimpleIntegral.intervalSum]
    · have hti : t ≤ τ i := le_of_not_ge hi
      have hti' : t ≤ τ (i + 1) := hti.trans (hτ (Nat.le_succ i))
      simp only [G, ite_eq_right hi, σ, StoppedSimpleIntegral.intervalSum,
        min_eq_left hti, min_eq_left hti', sub_self, mul_zero, Pi.zero_apply]
  have henergy (i : ℕ) :
      ((σ (i + 1) : ℝ) - (σ i : ℝ)) * (∫ ω, G i ω ^ 2 ∂P) =
        ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ)) *
          (∫ ω, H i ω ^ 2 ∂P) := by
    by_cases hi : τ i ≤ t
    · simp only [G, ite_eq_left hi, σ, NNReal.coe_min]
    · have hti : t ≤ τ i := le_of_not_ge hi
      have hti' : t ≤ τ (i + 1) := hti.trans (hτ (Nat.le_succ i))
      have htiR : (t : ℝ) ≤ (τ i : ℝ) := hti
      have hti'R : (t : ℝ) ≤ (τ (i + 1) : ℝ) := hti'
      simp only [σ, min_eq_left hti, min_eq_left hti', min_eq_left htiR,
        min_eq_left hti'R, sub_self, zero_mul]
  calc
    _ = ∫ ω, (∑ i ∈ s, G i ω * (B (σ (i + 1)) ω - B (σ i) ω)) ^ 2 ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by simp only [hterm])
    _ = ∑ i ∈ s, ((σ (i + 1) : ℝ) - (σ i : ℝ)) * ∫ ω, G i ω ^ 2 ∂P :=
      predictable_sum_isometry hB hAd hind σ hσ G hG hG2 s
    _ = _ := Finset.sum_congr rfl (fun i _ => henergy i)

theorem stopped_predictable_sum_memLp_two
    (hB : IsPreBrownianReal B P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (s : Finset ℕ) (t : ℝ≥0) :
    MemLp (fun ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) t ω) 2 P := by
  apply memLp_finsetSum s
  intro i hi
  change MemLp (fun ω => H i ω *
    (B (min t (τ (i + 1))) ω - B (min t (τ i)) ω)) 2 P
  by_cases hit : τ i ≤ t
  · have hle : τ i ≤ min t (τ (i + 1)) := le_min hit (hτ (Nat.le_succ i))
    simpa only [min_eq_right hit] using
      predictable_mul_memLp_two hB (hind (τ i) (min t (τ (i + 1))) hle) (hH i) (hH2 i)
  · have hti : t ≤ τ i := le_of_not_ge hit
    have hti' : t ≤ τ (i + 1) := hti.trans (hτ (Nat.le_succ i))
    simp only [min_eq_left hti,
      min_eq_left hti', sub_self, mul_zero]
    exact MemLp.zero

theorem stopped_predictable_sum_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (K : ℕ → ℝ) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i) (s : Finset ℕ) :
    Martingale (fun t ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact StoppedSimpleIntegral.finite_intervalSum_martingale
    (martingale_of_independent_past hB hAd hind) s τ (fun i => τ (i + 1)) H
    (fun i _ => hτ (Nat.le_succ i)) (fun i _ => hH i) K (fun i _ => hbound i)

end Problem367.BrownianFiltration

end

end OAI
