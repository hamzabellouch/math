import OAI.Probability.FreeIsing.Estimates.IntervalSumIntegrable
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianSquare
open StoppedSimpleIntegral BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem square_sub_time_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    Martingale (fun t ω => (B t ω)^2 - (t : ℝ)) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_of_independent_past hB hAd hind
  have hL2 (t) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  refine ⟨fun t => (hM.stronglyAdapted t).pow 2 |>.sub stronglyMeasurable_const, ?_⟩
  intro s t hst
  let G := F s
  let X : Ω → ℝ := B t - B s
  have hXL2 : MemLp X 2 P := (hL2 t).sub (hL2 s)
  have hXint : Integrable X P := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hXzero : P[X | G] =ᵐ[P] fun _ => 0 := by
    have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) G
    filter_upwards [hsub, hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
    dsimp [X, G] at *
    simp only [h2, h3, sub_self] at h1
    exact h1
  have hprodInt : Integrable (B s * X) P := (hL2 s).integrable_mul hXL2
  have hprodZero : P[B s * X | G] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_mul_of_stronglyMeasurable_left (hM.stronglyAdapted s) hprodInt hXint
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
    condExp_of_stronglyMeasurable (F |>.le s)
      ((hM.stronglyAdapted s).pow 2) (hL2 s).integrable_sq
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
    condExp_const (F |>.le s) (t : ℝ)
  filter_upwards [hsub, hBtSq] with ω hs hsq
  rw [hc] at hs
  simp only [Pi.sub_apply] at hs
  rw [hsq] at hs
  simp only [Pi.sub_def] at hs
  exact hs.trans (by ring)

theorem intervalSum_square_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    {a b : ℝ≥0} (hab : a ≤ b) {H : Ω → ℝ}
    (hH : StronglyMeasurable[F a] H) {K : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K) :
    Martingale (fun t ω => intervalSum B H a b t ω ^ 2 -
      H ω ^ 2 * ((min t b : ℝ) - (min t a : ℝ))) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_of_independent_past hB hAd hind
  have hQ := square_sub_time_martingale hB hAd hind
  have hHsq : StronglyMeasurable[F a] (fun ω => H ω ^ 2) := hH.pow 2
  have hbSq : ∀ᵐ ω ∂P, ‖H ω ^ 2‖ ≤ K ^ 2 := by
    filter_upwards [hbound] with ω hω
    rw [norm_pow]
    nlinarith [norm_nonneg (H ω)]
  have hfirst := intervalSum_martingale hQ hab hHsq hbSq
  have hL2 (t : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hprod : Integrable (fun ω => B a ω * (B b ω - B a ω)) P :=
    (hL2 a).integrable_mul ((hL2 b).sub (hL2 a))
  have hcross : Integrable (fun ω => (2 * H ω ^ 2 * B a ω) *
      (B b ω - B a ω)) P := by
    have h := (hprod.bdd_mul (hHsq.mono (F.le a)).aestronglyMeasurable hbSq).const_mul 2
    convert h using 1
    funext ω
    ring
  have hsecond := intervalSum_martingale_of_integrable_terminal hM hab
    ((stronglyMeasurable_const.mul hHsq).mul (hAd a)) hcross
  convert hfirst.sub hsecond using 1
  funext t ω
  rcases le_total t a with hta | hat
  · simp only [← NNReal.coe_min, intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
      sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Pi.sub_apply]
  · simp only [← NNReal.coe_min, intervalSum, min_eq_right hat, Pi.sub_apply, Pi.mul_apply]
    ring

omit mΩ in

theorem sum_intervalSum_eq_terminal
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (n : ℕ) {t : ℝ≥0} (hnt : τ n ≤ t) :
    (fun ω => ∑ i ∈ Finset.range n,
      intervalSum B (H i) (τ i) (τ (i + 1)) t ω) =
    (fun ω => ∑ i ∈ Finset.range n,
      intervalSum B (H i) (τ i) (τ (i + 1)) (τ n) ω) := by
  funext ω
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i + 1 ≤ n := Finset.mem_range.mp hi
  have hia : τ i ≤ τ n := hτ (Nat.le_of_succ_le hin)
  have hib : τ (i + 1) ≤ τ n := hτ hin
  simp only [intervalSum, min_eq_right hia, min_eq_right hib,
    min_eq_right (hia.trans hnt), min_eq_right (hib.trans hnt)]

theorem stopped_predictable_sum_square_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (K : ℕ → ℝ) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) ^ 2 -
      ∑ i ∈ Finset.range n, H i ω ^ 2 *
        ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ))) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_of_independent_past hB hAd hind
  have hH2 (i : ℕ) : MemLp (H i) 2 P :=
    MemLp.of_bound ((hH i).mono (F.le (τ i))).aestronglyMeasurable (K i) (hbound i)
  have hsum2 (m : ℕ) (t : ℝ≥0) :=
    stopped_predictable_sum_memLp_two hB hind τ hτ H hH hH2 (Finset.range m) t
  induction n with
  | zero =>
      convert martingale_zero ℝ F P using 1
      funext t ω
      simp
  | succ n ih =>
      let S : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range n,
        intervalSum B (H i) (τ i) (τ (i + 1)) t ω
      have hS : Martingale S F P :=
        stopped_predictable_sum_martingale hB hAd hind τ hτ H hH K hbound (Finset.range n)
      have hY2 : MemLp (fun ω => H n ω * (B (τ (n + 1)) ω - B (τ n) ω)) 2 P :=
        predictable_mul_memLp_two hB (hind (τ n) (τ (n + 1)) (hτ (Nat.le_succ n)))
          (hH n) (hH2 n)
      have hcoeff : StronglyMeasurable[F (τ n)] (fun ω => S (τ n) ω * H n ω) :=
        (hS.stronglyAdapted (τ n)).mul (hH n)
      have hint : Integrable (fun ω => (S (τ n) ω * H n ω) *
          (B (τ (n + 1)) ω - B (τ n) ω)) P := by
        have h := (hsum2 n (τ n)).integrable_mul hY2
        convert h using 1
        funext ω
        dsimp [S]
        ring
      have hcross := intervalSum_martingale_of_integrable_terminal hM (hτ (Nat.le_succ n))
        hcoeff hint
      have heq : (fun t ω => S t ω *
          intervalSum B (H n) (τ n) (τ (n + 1)) t ω) =
          intervalSum B (fun ω => S (τ n) ω * H n ω) (τ n) (τ (n + 1)) := by
        funext t ω
        rcases le_total t (τ n) with hta | hat
        · simp only [intervalSum, min_eq_left hta,
            min_eq_left (hta.trans (hτ (Nat.le_succ n))), sub_self, mul_zero]
        · have hconst : S t = S (τ n) := sum_intervalSum_eq_terminal τ hτ H n hat
          rw [hconst]
          simp only [intervalSum]
          ring
      have hcross' : Martingale (fun t ω => S t ω *
          intervalSum B (H n) (τ n) (τ (n + 1)) t ω) F P := by
        rw [heq]
        exact hcross
      have hdiag := intervalSum_square_martingale hB hAd hind (hτ (Nat.le_succ n))
        (hH n) (hbound n)
      have htotal := (ih.add hdiag).add (Martingale.smul 2 hcross')
      convert htotal using 1
      funext t ω
      simp only [Finset.sum_range_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [S]
      ring

end Problem367.StoppedBrownianSquare

end

end OAI
