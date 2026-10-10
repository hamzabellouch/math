import OAI.Probability.DilutedSpin.ConcentrationRate
import OAI.Probability.DilutedSpin.CountedSteps

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

/-- Total (unnormalized) pressure of the literal countable reservoir. The
entropy restores the counting-spin partition function from uniform spins. -/
noncomputable def perturbedMean (μ : Measure X) (ξ : Measure Y) (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (u v : ℝ≥0) : ℝ :=
  N*Real.log 2 + twoPoissonMean u v (countedMean (N := N) μ ξ ν theta field Q m ψ)

theorem perturbedMean_size_rate_coupling (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (u v t w : ℝ≥0) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (u+t) (v+w)-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ u v| ≤
      Real.log 2+H+2*C*u*p/(N+1)+2*D*v/(N+1)+C*t+D*w := by
  let f := countedMean (N := N+1) μ ξ ν theta field Q m ψ
  let g := countedMean (N := N) μ ξ ν theta field Q m ψ
  have hf : ∀ k l, |f k l| ≤ H*(N+1)+C*k+D*l := by
    intro k l
    simpa only [Nat.cast_add,Nat.cast_one] using countedMean_bound (N := N+1) μ ξ ν theta field Q m hm ψ hθ hh hψ k l
  have hg : ∀ k l, |g k l| ≤ H*N+C*k+D*l :=
    countedMean_bound μ ξ ν theta field Q m hm ψ hθ hh hψ
  have hc : |twoPoissonMean u v f-twoPoissonMean u v g| ≤ H+2*C*u*p/(N+1)+2*D*v/(N+1) := by
    have ht := twoPoisson_abs_sub_le u v hf hg (E := H) (F := 2*C*p/(N+1)) (G := 2*D/(N+1))
      (fun k l => (countedMean_size_coupling μ ξ ν theta field hθm hhm Q m hm ψ hC hD hθ hh hψ k l).trans_eq (by ring))
    convert ht using 1
    ring
  have hl := twoPoissonMean_rate_add_left u (v+w) t hf hC
    (countedMean_interaction_step μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ)
  have hr := twoPoissonMean_rate_add_right u v w hf hD
    (countedMean_mark_step μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (u+t) (v+w)-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ u v =
      Real.log 2 + (twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f) +
      (twoPoissonMean u (v+w) f-twoPoissonMean u v f)+
      (twoPoissonMean u v f-twoPoissonMean u v g) := by
    simp only [perturbedMean,Nat.cast_add,Nat.cast_one,f,g]
    ring
  rw [he]
  have h1 := abs_add_le (Real.log 2) (twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f)
  have h2 := abs_add_le (Real.log 2+(twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f))
    (twoPoissonMean u (v+w) f-twoPoissonMean u v f)
  have h3 := abs_add_le (Real.log 2+(twoPoissonMean (u+t) (v+w) f-twoPoissonMean u (v+w) f)+
    (twoPoissonMean u (v+w) f-twoPoissonMean u v f)) (twoPoissonMean u v f-twoPoissonMean u v g)
  rw [abs_of_nonneg hlog] at h1
  linarith

end DilutedSpinGlass.SizeCoupling

namespace DilutedSpinGlass
open scoped NNReal

noncomputable def scoreRate (N : ℕ) : ℝ≥0 := ⟨scoreScale N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩

lemma scoreScale_mono : Monotone scoreScale := by
  intro M N hMN
  exact Real.rpow_le_rpow (Nat.cast_nonneg M) (by exact_mod_cast hMN) (by norm_num)

lemma scoreScale_succ_sub_le (N : ℕ) : scoreScale (N+1)-scoreScale N ≤ 1 := by
  have ht := Real.rpow_add_le_add_rpow (show (0:ℝ) ≤ N from Nat.cast_nonneg N)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3:ℝ)/4 ≤ 1)
  norm_num only [Real.one_rpow] at ht
  dsimp [scoreScale]
  push_cast
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

/-- The uniform lower and upper increment envelope needed by deterministic
parameter selection. Dependence on the entire dictionary and on all priors has
cancelled; the original uncapped N^(3/4) scale is used. -/
theorem perturbedMean_uniform_increment (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (α : ℝ≥0) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) (scoreRate (N+1))-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ (α*N) (scoreRate N)| ≤
      Real.log 2+H+(2*p+1)*C*α+3*D := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hs : scoreRate N ≤ scoreRate (N+1) := scoreScale_mono (Nat.le_succ N)
  have ha : α*(N:ℝ≥0)+α = α*(N+1) := by ring
  have hb : scoreRate N+(scoreRate (N+1)-scoreRate N) = scoreRate (N+1) :=
    add_tsub_cancel_of_le hs
  have ht := perturbedMean_size_rate_coupling (N := N) μ ξ ν theta field hθm hhm Q m hm ψ hC hD
    hθ hh hψ (α*N) (scoreRate N) α (scoreRate (N+1)-scoreRate N)
  rw [ha,hb] at ht
  apply ht.trans
  have hden : (0:ℝ) < N+1 := by positivity
  have hex : (↑(scoreRate (N+1)-scoreRate N):ℝ) ≤ 1 := by
    rw [NNReal.coe_sub hs]
    exact scoreScale_succ_sub_le N
  have hp : 2*C*↑(α*(N:ℝ≥0))*p/(N+1) ≤ 2*C*α*p := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith [mul_nonneg hC α.coe_nonneg, mul_nonneg (mul_nonneg hC α.coe_nonneg) (Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hm' : 2*D*(scoreRate N:ℝ)/(N+1) ≤ 2*D := by
    apply (div_le_iff₀ hden).mpr
    have hs' := scoreScale_le hN
    change scoreScale N ≤ (N:ℝ) at hs'
    change 2*D*scoreScale N ≤ _
    nlinarith
  have hw := mul_le_mul_of_nonneg_left hex hD
  linarith

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
