import OAI.Analysis.LipschitzHilbert.Estimates.StoppedMartingaleEnergy

namespace OAI

/-! Quadratic energy and jump counts along any finite increasing chain
of bounded stopping times. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}

theorem stopped_martingale_chain_identity (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) :
    (∑ i∈Finset.range J, ∫ x, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ)=
      (∫ x, (stoppedValue F (τ J) x)^2 ∂μ)-(∫ x, (stoppedValue F (τ 0) x)^2 ∂μ) := by
  simp_rw [stopped_martingale_square_difference hF hF2 _ _ (hτ _) (hτ _) (hmono _) N (hbound _)]
  exact Finset.sum_range_sub (fun i => ∫ x, (stoppedValue F (τ i) x)^2 ∂μ) J

theorem stopped_martingale_terminal_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hbound : ∀ x, τ x≤N) :
    (∫ x, (stoppedValue F τ x)^2 ∂μ)≤∫ x, F N x^2 ∂μ := by
  have hh := stopped_martingale_square_difference hF hF2 τ (fun _ => (N:WithTop ℕ))
    hτ (isStoppingTime_const ℱ N) hbound N (fun _ => le_rfl)
  change (∫ x, (F N x-stoppedValue F τ x)^2 ∂μ)=
    (∫ x, F N x^2 ∂μ)-(∫ x, (stoppedValue F τ x)^2 ∂μ) at hh
  have hnonneg : 0≤∫ x, (F N x-stoppedValue F τ x)^2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  linarith

theorem stopped_martingale_chain_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) :
    (∑ i∈Finset.range J, ∫ x, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ)≤
      ∫ x, F N x^2 ∂μ := by
  rw [stopped_martingale_chain_identity hF hF2 τ hτ hmono N J hbound]
  exact (sub_le_self _ (integral_nonneg fun x => sq_nonneg _)).trans
    (stopped_martingale_terminal_energy hF hF2 (τ J) (hτ J) N (hbound J))

def stoppedJumpCount (F : ℕ → Ω → ℝ) (τ : ℕ → Ω → WithTop ℕ) (J : ℕ)
    (lambda : ℝ) (x : Ω) : ℝ :=
  ∑ i∈Finset.range J, if lambda≤|stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x| then 1 else 0

theorem stoppedJumpCount_energy (hF : Martingale F ℱ μ)
    (hF2 : ∀ n, MemLp (F n) 2 μ) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ i, IsStoppingTime ℱ (τ i)) (hmono : ∀ i, τ i≤τ (i+1))
    (N J : ℕ) (hbound : ∀ i x, τ i x≤N) (lambda : ℝ) (hlambda : 0≤lambda) :
    lambda^2*(∫ x, stoppedJumpCount F τ J lambda x ∂μ)≤∫ x, F N x^2 ∂μ := by
  have hmeas (i : ℕ) : Measurable (stoppedValue F (τ i)) :=
    ((stronglyMeasurable_stoppedValue_of_le hF.1.isStronglyProgressive_of_discrete
      (hτ i) (hbound i)).mono (ℱ.le N)).measurable
  have hcount (i : ℕ) : Integrable (fun x =>
      if lambda≤|stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x| then (1:ℝ) else 0) μ := by
    have hs0 := measurableSet_le (measurable_const (a:=lambda)) ((hmeas (i+1)).sub (hmeas i)).norm
    have hs : MeasurableSet {x | lambda≤|stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x|} := by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using hs0
    apply ((integrable_const (1:ℝ)).indicator hs).congr
    filter_upwards [] with x
    by_cases hx : lambda≤|stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x| <;> simp [hx]
  have hcountSum : Integrable (stoppedJumpCount F τ J lambda) μ :=
    integrable_finsetSum _ (fun i _ => hcount i)
  have henergy (i : ℕ) : Integrable (fun x =>
      (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2) μ :=
    ((memLp_stoppedValue (hτ (i+1)) hF2 (hbound (i+1))).sub
      (memLp_stoppedValue (hτ i) hF2 (hbound i))).integrable_sq
  have hpoint (x : Ω) : lambda^2*stoppedJumpCount F τ J lambda x≤
      ∑ i∈Finset.range J, (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 := by
    unfold stoppedJumpCount
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : lambda≤|stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x|
    · rw [ite_eq_left hi,mul_one]
      simpa only [sq_abs] using pow_le_pow_left₀ hlambda hi 2
    · rw [ite_eq_right hi,mul_zero]
      exact sq_nonneg _
  calc
    _ = ∫ x, lambda^2*stoppedJumpCount F τ J lambda x ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ x, ∑ i∈Finset.range J,
        (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ :=
      integral_mono (hcountSum.const_mul _) (integrable_finsetSum _ (fun i _ => henergy i)) hpoint
    _ = ∑ i∈Finset.range J, ∫ x,
        (stoppedValue F (τ (i+1)) x-stoppedValue F (τ i) x)^2 ∂μ :=
      integral_finsetSum _ (fun i _ => henergy i)
    _ ≤ _ := stopped_martingale_chain_energy hF hF2 τ hτ hmono N J hbound

end LipschitzHilbert

end

end OAI
