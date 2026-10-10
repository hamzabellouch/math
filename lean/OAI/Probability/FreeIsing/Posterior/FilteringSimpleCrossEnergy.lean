import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Posterior.FilteringCrossEnergy

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integrable_posterior_weighted_increment [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W F P) {Q H : Ω → ℝ} {A D : ℝ}
    (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D) {s t T : ℝ≥0}
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    Integrable (fun ω => P[Q | F T] ω * H ω * (W t ω - W s ω)) P := by
  have hb : ∀ᵐ ω ∂P, |P[Q | F T] ω * H ω| ≤ D * A := by
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := F T) hQb, hHb]
      with ω hq hh
    rw [abs_mul]
    exact mul_le_mul hq hh (abs_nonneg _) ((abs_nonneg _).trans hq)
  apply integrable_bounded_mul ((hW.integrable t).sub (hW.integrable s))
    (((stronglyMeasurable_condExp.mono (F.le T)).mul
      (hH.mono (F.le s))).aestronglyMeasurable) hb

theorem integral_posterior_mul_integralSum [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {C D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ) (A : ℕ → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hHb : ∀ i, ∀ᵐ ω ∂P, |H i ω| ≤ A i)
    (n : ℕ) {T : ℝ≥0} (hT : τ n ≤ T) :
    (∫ ω, P[Q | F T] ω * BrownianGrid.integralSum (innovation B S m) τ H n ω ∂P) =
      ∑ i ∈ Finset.range n, ∫ r in (τ i : ℝ)..(τ (i + 1) : ℝ),
        ∫ ω, H i ω * (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
          P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  have hW : Martingale (innovation B S m) F P :=
    compensated_observation_martingale_of_bounded_signal hB hFG hS hX hm hpost C hSb
  have hint (i : ℕ) : Integrable (fun ω => P[Q | F T] ω * H i ω *
      (innovation B S m (τ (i + 1)) ω - innovation B S m (τ i) ω)) P :=
    integrable_posterior_weighted_increment hW hQb (hH i) (hHb i)
  calc
    _ = ∫ ω, ∑ i ∈ Finset.range n, P[Q | F T] ω * H i ω *
        (innovation B S m (τ (i + 1)) ω - innovation B S m (τ i) ω) ∂P := by
      congr 1
      funext ω
      simp only [BrownianGrid.integralSum, Finset.mul_sum, mul_assoc]
    _ = ∑ i ∈ Finset.range n, ∫ ω, P[Q | F T] ω * H i ω *
        (innovation B S m (τ (i + 1)) ω - innovation B S m (τ i) ω) ∂P :=
      integral_finsetSum _ (fun i _ => hint i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_posterior_mul_innovation_increment hB hFG
        (hτ (Nat.le_succ i)) ((hτ (Finset.mem_range.mp hi)).trans hT)
        (hQ.mono (G.mono (bot_le : (0 : ℝ≥0) ≤ τ i))) hQb hS hSb hX
        (hH i) (hHb i) hm hpost

theorem integral_posterior_mul_uniformSum [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m H : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {A C D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (hH : StronglyAdapted F H) (hHb : ∀ r, ∀ᵐ ω ∂P, |H r ω| ≤ A)
    (T : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    (∫ ω, P[Q | F T] ω * BrownianGrid.uniformSum (innovation B S m) H T n ω ∂P) =
      ∑ i ∈ Finset.range n,
        ∫ r in (BrownianGrid.uniformGrid T n i : ℝ)..(BrownianGrid.uniformGrid T n (i + 1) : ℝ),
          ∫ ω, H (BrownianGrid.uniformGrid T n i) ω *
            (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
              P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  exact integral_posterior_mul_integralSum hB hFG hQ hQb hS hSb hX hm hpost
    (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
    (fun i => H (BrownianGrid.uniformGrid T n i)) (fun _ => A)
    (fun i => hH _) (fun i => hHb _) n (by rw [BrownianGrid.uniformGrid_end T hn])

end Problem367.FilteringCrossEnergy

end

end OAI
