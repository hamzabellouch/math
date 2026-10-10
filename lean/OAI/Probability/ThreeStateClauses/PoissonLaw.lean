import Mathlib
import OAI.Probability.ThreeStateClauses.BranchGrowth
import OAI.Probability.ThreeStateClauses.ObservedMixtures
import OAI.Probability.ThreeStateClauses.PoissonMoments

namespace OAI

/-! Poisson Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive ThreeState.TreeClauses.Probability

def poissonLaw (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ≥0) : Law :=
  offspringLaw (poissonPMF t) Q hl₀ hl₁

lemma mixture_mu (ρ : PMF ℕ) (Q : ℕ → Law) :
    (mixtureLaw ρ Q).mu = ∫ n, (Q n).mu ∂ρ.toMeasure := by
  change (∫ m, xMoment m ∂(mixtureProbability ρ (fun n ↦ (Q n).probability)).toMeasure) = _
  rw [integral_mixtureProbability _ _ (compact_integrable continuous_xMoment),
    PMF.integral_eq_tsum _ _ (pmf_bounded_integrable ρ (fun n ↦ show |(Q n).mu| ≤ 1 by
      rw [abs_of_nonneg (Q n).mu_nonneg]; exact (Q n).mu_le_one))]
  rfl

lemma Law.nu_le_one (Q : Law) : Q.nu ≤ 1 := by
  apply (integral_mono (compact_integrable (continuous_xMoment.pow 2)) (integrable_const (1:ℝ)) _).trans_eq
    (by simp)
  intro m
  change xMoment m^2 ≤ 1
  nlinarith [xMoment_nonneg m, xMoment_le_one m]

lemma mixture_nu (ρ : PMF ℕ) (Q : ℕ → Law) :
    (mixtureLaw ρ Q).nu = ∫ n, (Q n).nu ∂ρ.toMeasure := by
  change (∫ m, xMoment m^2 ∂(mixtureProbability ρ (fun n ↦ (Q n).probability)).toMeasure) = _
  rw [integral_mixtureProbability _ _ (f := fun m ↦ xMoment m^2) (compact_integrable (continuous_xMoment.pow 2)),
    PMF.integral_eq_tsum _ _ (pmf_bounded_integrable ρ (fun n ↦ show |(Q n).nu| ≤ 1 by
      rw [abs_of_nonneg (Q n).nu_nonneg]; exact (Q n).nu_le_one))]
  rfl

private lemma poisson_quadratic_integral (t : ℝ≥0) (b a : ℝ) (M : ℕ → ℝ)
    (hM : Integrable M (poissonPMF t).toMeasure) :
    (∫ n : ℕ, (2*n*b+2*((n:ℝ)^2-n)*b^2)*(a*a)+(-4*n*b)*a+2*M n
      ∂(poissonPMF t).toMeasure) =
    (2*t*b+2*(t:ℝ)^2*b^2)*(a*a)+(-4*t*b)*a+2*(∫ n, M n ∂(poissonPMF t).toMeasure) := by
  have hn := poisson_integrable_first t
  have hn₂ := poisson_integrable_second t
  have he (n : ℕ) : (2*n*b+2*((n:ℝ)^2-n)*b^2)*(a*a)+(-4*n*b)*a+2*M n =
      (2*b*(a*a)-4*b*a)*(n:ℝ)+(2*b^2*(a*a))*((n:ℝ)^2-n)+2*M n := by ring
  let A : ℝ := 2*b*(a*a)-4*b*a
  let B : ℝ := 2*b^2*(a*a)
  have hA : Integrable (fun n : ℕ ↦ A*(n:ℝ)) (poissonPMF t).toMeasure := hn.const_mul A
  have hB : Integrable (fun n : ℕ ↦ B*((n:ℝ)^2-n)) (poissonPMF t).toMeasure := (hn₂.sub hn).const_mul B
  calc
    _ = ∫ n : ℕ, (A*(n:ℝ)+B*((n:ℝ)^2-n))+2*M n ∂(poissonPMF t).toMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = (∫ n : ℕ, A*(n:ℝ)+B*((n:ℝ)^2-n) ∂(poissonPMF t).toMeasure)+
        (∫ n, 2*M n ∂(poissonPMF t).toMeasure) := integral_add (hA.add hB) (hM.const_mul 2)
    _ = A*(t:ℝ)+B*(t:ℝ)^2+2*(∫ n, M n ∂(poissonPMF t).toMeasure) := by
      rw [integral_add hA hB, integral_const_mul, integral_const_mul, integral_const_mul,
        poisson_integral_first, poisson_integral_factorial_second]
    _ = _ := by dsimp only [A,B]; ring

lemma poisson_projection_quadratic (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (t : ℝ≥0) (a : ℝ) :
    0 ≤ (2*t*(lam^2*Q.mu)+2*(t:ℝ)^2*(lam^2*Q.mu)^2)*(a*a)+
      (-4*t*(lam^2*Q.mu))*a+2*(poissonLaw Q hl₀ hl₁ t).mu := by
  have hmu := pmf_bounded_integrable (poissonPMF t)
    (fun n ↦ show |(finiteLaw Q hl₀ hl₁ n).mu| ≤ 1 by
      rw [abs_of_nonneg (finiteLaw Q hl₀ hl₁ n).mu_nonneg]; exact (finiteLaw Q hl₀ hl₁ n).mu_le_one)
  have h := integral_nonneg (μ := (poissonPMF t).toMeasure)
    (f := fun n : ℕ ↦ (2*n*(lam^2*Q.mu)+2*((n:ℝ)^2-n)*(lam^2*Q.mu)^2)*(a*a)+
      (-4*n*(lam^2*Q.mu))*a+2*(finiteLaw Q hl₀ hl₁ n).mu)
    (fun n ↦ finite_projection_quadratic Q hl₀ hl₁ n a)
  rw [poisson_quadratic_integral t (lam^2*Q.mu) a _ hmu] at h
  have hm : (∫ n, (finiteLaw Q hl₀ hl₁ n).mu ∂(poissonPMF t).toMeasure) =
      (poissonLaw Q hl₀ hl₁ t).mu := (mixture_mu _ _).symm
  rwa [hm] at h

theorem poisson_projection (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ≥0) :
    (t:ℝ)*(lam^2*Q.mu)/(1+(t:ℝ)*(lam^2*Q.mu)) ≤ (poissonLaw Q hl₀ hl₁ t).mu := by
  let β := lam^2*Q.mu
  have hb : 0 ≤ β := mul_nonneg (sq_nonneg _) Q.mu_nonneg
  have ht : 0 ≤ (t:ℝ) := t.coe_nonneg
  have hd : 0 < 1+(t:ℝ)*β := by positivity
  have h := poisson_projection_quadratic Q hl₀ hl₁ t (1/(1+(t:ℝ)*β))
  change 0 ≤ (2*t*β+2*(t:ℝ)^2*β^2)*(1/(1+(t:ℝ)*β)*(1/(1+(t:ℝ)*β)))+
      (-4*t*β)*(1/(1+(t:ℝ)*β))+2*(poissonLaw Q hl₀ hl₁ t).mu at h
  have he : (2*t*β+2*(t:ℝ)^2*β^2)*(1/(1+(t:ℝ)*β)*(1/(1+(t:ℝ)*β)))+
      (-4*t*β)*(1/(1+(t:ℝ)*β)) = -2*((t:ℝ)*β/(1+(t:ℝ)*β)) := by
    field_simp; ring
  rw [he] at h
  linarith

lemma poisson_integral_mono_intensity {f : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |f n| ≤ B)
    (hf : Monotone f) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ n, f n ∂(poissonPMF s).toMeasure) ≤ ∫ n, f n ∂(poissonPMF t).toMeasure := by
  have hts : s+(t-s) = t := add_tsub_cancel_of_le hst
  have hi : Integrable f (poissonMeasure s ∗ poissonMeasure (t-s)) := by
    rw [poissonMeasure_conv_poissonMeasure, hts, ← poissonPMF_toMeasure]
    exact pmf_bounded_integrable _ hB
  rw [poissonPMF_toMeasure, poissonPMF_toMeasure, ← hts, ← poissonMeasure_conv_poissonMeasure,
    integral_conv hi]
  apply integral_mono (by rw [← poissonPMF_toMeasure]; exact pmf_bounded_integrable _ hB)
  · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun n ↦ by
      rw [Real.norm_eq_abs]
      apply (abs_integral_le_integral_abs).trans
      apply (integral_mono (by rw [← poissonPMF_toMeasure]; exact (pmf_bounded_integrable _ (fun m ↦ hB (n+m))).abs)
        (integrable_const _) (fun m ↦ hB (n+m))).trans_eq
      simp)
  · intro n
    calc
      f n = ∫ _, f n ∂poissonMeasure (t-s) := by simp
      _ ≤ _ := integral_mono (integrable_const _) (by
        rw [← poissonPMF_toMeasure]; exact pmf_bounded_integrable _ (fun m ↦ hB (n+m)))
        (fun m ↦ hf (Nat.le_add_right n m))

lemma poisson_nu_mono (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (poissonLaw Q hl₀ hl₁ s).nu ≤ (poissonLaw Q hl₀ hl₁ t).nu := by
  change (mixtureLaw _ _).nu ≤ (mixtureLaw _ _).nu
  rw [mixture_nu, mixture_nu]
  apply poisson_integral_mono_intensity (B := 1) _ (fun _ _ h ↦ finite_nu_mono Q hl₀ hl₁ h) hst
  intro n
  rw [abs_of_nonneg (finiteLaw Q hl₀ hl₁ n).nu_nonneg]
  exact (finiteLaw Q hl₀ hl₁ n).nu_le_one

end ThreeState.TreeClauses.Experiment

end

end OAI
