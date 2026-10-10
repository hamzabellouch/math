import OAI.Probability.FreeIsing.Brownian.FiltrationIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianFiltration

theorem square_sub_time_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    Martingale (fun t ω => B t ω ^ 2 - (t : ℝ)) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hL2 (t) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  refine ⟨fun t => (hAd t).pow 2 |>.sub stronglyMeasurable_const, ?_⟩
  intro s t hst
  let G := F s
  let X : Ω → ℝ := B t - B s
  have hXL2 : MemLp X 2 P := (hL2 t).sub (hL2 s)
  have hXint : Integrable X P := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hXzero : P[X | G] =ᵐ[P] fun _ => 0 :=
    increment_condExp_zero (mΩ := mΩ) hB hAd (hind s t hst)
  have hprodInt : Integrable (B s * X) P := (hL2 s).integrable_mul hXL2
  have hprodZero : P[B s * X | G] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_mul_of_stronglyMeasurable_left (hAd s) hprodInt hXint
    filter_upwards [hp, hXzero] with ω hp hz
    change P[B s * X | G] ω = B s ω * P[X | G] ω at hp
    rw [hz, mul_zero] at hp
    exact hp
  have htwoZero : P[(fun ω => 2 * (B s ω * X ω)) | G] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_smul (μ := P) (2 : ℝ) (B s * X) G
    filter_upwards [hp, hprodZero] with ω hp hz
    change P[(fun ω => 2 * (B s ω * X ω)) | G] ω = 2 * P[B s * X | G] ω at hp
    rw [hz, mul_zero] at hp
    exact hp
  have hXSq := increment_sq_condExp (mΩ := mΩ) hB hAd hst (hind s t hst)
  have hBSq : P[(fun ω => (B s ω)^2) | G] = (fun ω => (B s ω)^2) :=
    condExp_of_stronglyMeasurable (F.le s)
      ((hAd s).pow 2) (hL2 s).integrable_sq
  have hfun : (fun ω => (B t ω)^2) =
      (fun ω => (X ω)^2 + 2 * (B s ω * X ω)) + (fun ω => (B s ω)^2) := by
    funext ω
    dsimp [X]
    ring
  have hsum1 := condExp_add hXL2.integrable_sq (hprodInt.const_mul 2) G
  have hsum2 := condExp_add (hXL2.integrable_sq.add (hprodInt.const_mul 2))
    (hL2 s).integrable_sq G
  have hBtSq : P[(fun ω => (B t ω)^2) | G] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) + (B s ω)^2 := by
    rw [hfun]
    filter_upwards [hsum2, hsum1, htwoZero, hXSq] with ω h2 h1 hz hsq
    change P[(fun ω => (X ω)^2) | G] ω = (t : ℝ) - (s : ℝ) at hsq
    simp only [Pi.add_def, Pi.mul_def] at h2 h1
    rw [hBSq] at h2
    rw [h1, hz, hsq] at h2
    simpa only [Pi.add_def, add_zero] using h2
  have hsub := condExp_sub (hL2 t).integrable_sq (integrable_const (t : ℝ)) G
  have hc : P[(fun _ : Ω => (t : ℝ)) | G] = (fun _ => (t : ℝ)) :=
    condExp_const (F.le s) (t : ℝ)
  filter_upwards [hsub, hBtSq] with ω hs hsq
  rw [hc] at hs
  simp only [Pi.sub_apply] at hs
  rw [hsq] at hs
  simp only [Pi.sub_def] at hs
  exact hs.trans (by ring)

end Problem367.BrownianFiltration

end

end OAI
