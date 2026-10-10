import Mathlib

namespace OAI

universe u_1

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336AdditiveD139.InnovationCharacteristic

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

theorem phase_sub_split (x y z : ℝ) : phase (z - x) = phase (y - x) * phase (z - y) := by
  rw [← phase_add]
  congr 1
  ring

theorem continuous_phase : Continuous phase := by unfold phase; fun_prop

section Probability

variable {Ω : Type u_1} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem weighted_condExp_error {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f g : Ω → ℂ} (hf : StronglyMeasurable[m] f) (hg : Integrable g μ)
    (hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) {a : ℂ} {ε : ℝ}
    (herr : ∀ᵐ ω ∂μ, ‖μ[g | m] ω - a‖ ≤ ε) :
    ‖(∫ ω, f ω * g ω ∂μ) - a * ∫ ω, f ω ∂μ‖ ≤ ε := by
  have hfm : AEStronglyMeasurable[m₀] f μ := (hf.mono hm).aestronglyMeasurable
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hfm hfb
  have hCE : Integrable (μ[g | m]) μ := integrable_condExp
  have hprod : Integrable (fun ω => f ω * μ[g | m] ω) μ := hCE.bdd_mul hfm hfb
  have hfa : Integrable (fun ω => f ω * a) μ := hfi.mul_const a
  have hpull := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ)
    hm hf hg 1 hfb
  have heq : (∫ ω, f ω * g ω ∂μ) = ∫ ω, f ω * μ[g | m] ω ∂μ := by
    calc
      _ = ∫ ω, μ[fun ω => f ω * g ω | m] ω ∂μ := (integral_condExp hm).symm
      _ = _ := integral_congr_ae hpull
  have hnorm : ∀ᵐ ω ∂μ, ‖f ω * (μ[g | m] ω - a)‖ ≤ ε := by
    filter_upwards [hfb, herr] with ω hfω heω
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hfω (norm_nonneg _)).trans (by simpa using heω)
  have h := norm_integral_le_of_norm_le_const hnorm
  simp only [probReal_univ, mul_one] at h
  convert h using 1
  rw [heq]
  congr 1
  simp_rw [mul_sub]
  rw [integral_sub hprod hfa, integral_mul_const]
  ring

theorem discrete_characteristic_error (N : ℕ) (m : ℕ → MeasurableSpace Ω)
    (hm : Monotone m) (hle : ∀ n, m n ≤ m₀) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n, StronglyMeasurable[m n] (Z n))
    (A : Set Ω) (hA : MeasurableSet[m 0] A)
    (a : ℂ) (ha : ‖a‖ ≤ 1) (ε : ℝ) (_hε : 0 ≤ ε)
    (hstep : ∀ k < N, ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (Z (k + 1) ω - Z k ω) | m k] ω - a‖ ≤ ε) :
    ‖(∫ ω in A, phase (Z N ω - Z 0 ω) ∂μ) -
      a ^ N * ((μ A).toReal : ℂ)‖ ≤ (N : ℝ) * ε := by
  have hAm : MeasurableSet A := hle 0 A hA
  have hphase (k : ℕ) : StronglyMeasurable[m k] (fun ω => phase (Z k ω - Z 0 ω)) :=
    continuous_phase.comp_stronglyMeasurable ((hZ k).sub ((hZ 0).mono (hm (Nat.zero_le _))))
  have hint (k : ℕ) : Integrable (fun ω => phase (Z k ω - Z 0 ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (((hphase k).mono (hle k)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun ω => by simp)
  have hrec (k : ℕ) (hk : k < N) :
      ‖(∫ ω in A, phase (Z (k + 1) ω - Z 0 ω) ∂μ) -
        a * ∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ‖ ≤ ε := by
    let f : Ω → ℂ := A.indicator (fun ω => phase (Z k ω - Z 0 ω))
    let g : Ω → ℂ := fun ω => phase (Z (k + 1) ω - Z k ω)
    have hf : StronglyMeasurable[m k] f := (hphase k).indicator (hm (Nat.zero_le k) A hA)
    have hg : Integrable g μ := by
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact (continuous_phase.comp_stronglyMeasurable
          (((hZ (k + 1)).mono (hle (k + 1))).sub ((hZ k).mono (hle k)))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => by simp [g])
    have hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1 := by
      filter_upwards with ω
      by_cases hω : ω ∈ A <;> simp [f, hω]
    have h := weighted_condExp_error (hle k) hf hg hfb (hstep k hk)
    have heq : (fun ω => f ω * g ω) = A.indicator
        (fun ω => phase (Z (k + 1) ω - Z 0 ω)) := by
      ext ω
      by_cases hω : ω ∈ A
      · simp only [f, g, Set.indicator_of_mem hω]
        exact (phase_sub_split _ _ _).symm
      · simp [f, hω]
    simpa only [heq, f, integral_indicator hAm] using h
  have hind : ∀ k ≤ N,
      ‖(∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ) -
        a ^ k * ((μ A).toReal : ℂ)‖ ≤ (k : ℝ) * ε := by
    intro k hk
    induction k with
    | zero => simp [Measure.real]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hs := hrec k (Nat.lt_of_succ_le hk)
      calc
        _ = ‖((∫ ω in A, phase (Z (k + 1) ω - Z 0 ω) ∂μ) -
            a * ∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ) +
            a * ((∫ ω in A, phase (Z k ω - Z 0 ω) ∂μ) -
              a ^ k * ((μ A).toReal : ℂ))‖ := by congr 1; rw [pow_succ]; ring
        _ ≤ ε + (k : ℝ) * ε := (norm_add_le _ _).trans
          (add_le_add hs (by rw [norm_mul]; exact
            (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using ih')))
        _ = ((k + 1 : ℕ) : ℝ) * ε := by push_cast; ring
  exact hind N le_rfl

theorem time_partition_characteristic_error
    (H : ℝ → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ m₀)
    (W : ℝ → Ω → ℝ) (hW : ∀ u, 0 ≤ u → StronglyMeasurable[H u] (W u))
    (C σ2 : ℝ) (hC : 0 ≤ C) (hσ : 0 ≤ σ2)
    (hlocal : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (W v ω - W u ω) | H u] ω -
        (Real.exp (-(v - u) * σ2 / 2) : ℂ)‖ ≤ C * (v - u) * Real.sqrt (v - u))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[H s] A) (N : ℕ) (hN : 0 < N)
    (hsmall : (t - s) / N ≤ 1) :
    ‖(∫ ω in A, phase (W t ω - W s ω) ∂μ) -
      (Real.exp (-(t - s) * σ2 / 2) : ℂ) * ((μ A).toReal : ℂ)‖ ≤
      C * (t - s) * Real.sqrt ((t - s) / N) := by
  let δ : ℝ := (t - s) / N
  let τ : ℕ → ℝ := fun k => s + δ * k
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg N)
  have hτ : Monotone τ := by
    intro i j hij
    dsimp [τ]
    gcongr
  have hτ0 : τ 0 = s := by simp [τ]
  have hτN : τ N = t := by dsimp [τ, δ]; field_simp; ring
  have hτpos (k : ℕ) : 0 ≤ τ k := hs.trans (by simpa [hτ0] using hτ (Nat.zero_le k))
  have hτstep (k : ℕ) : τ (k + 1) - τ k = δ := by dsimp [τ]; push_cast; ring
  let a : ℂ := Real.exp (-δ * σ2 / 2)
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hδ hσ]
  have haN : a ^ N = (Real.exp (-(t - s) * σ2 / 2) : ℂ) := by
    dsimp [a]
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    dsimp [δ]
    field_simp
  have hε : 0 ≤ C * δ * Real.sqrt δ :=
    mul_nonneg (mul_nonneg hC hδ) (Real.sqrt_nonneg _)
  have hstep : ∀ k < N, ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (W (τ (k + 1)) ω - W (τ k) ω) | H (τ k)] ω - a‖ ≤
        C * δ * Real.sqrt δ := by
    intro k _hk
    have h := hlocal (τ k) (τ (k + 1)) (hτpos k) (hτ (Nat.le_succ k))
      (by simpa only [hτstep] using hsmall)
    simpa only [hτstep, a] using h
  have h := discrete_characteristic_error N (fun k => H (τ k)) (hH.comp hτ)
    (fun k => hle (τ k)) (fun k => W (τ k)) (fun k => hW (τ k) (hτpos k)) A
    (by rw [hτ0]; exact hA)
    a ha (C * δ * Real.sqrt δ) hε hstep
  rw [hτN, hτ0, haN] at h
  convert h using 1
  dsimp [δ]
  field_simp

theorem event_characteristic_eq
    (H : ℝ → MeasurableSpace Ω) (hH : Monotone H) (hle : ∀ u, H u ≤ m₀)
    (W : ℝ → Ω → ℝ) (hW : ∀ u, 0 ≤ u → StronglyMeasurable[H u] (W u))
    (C σ2 : ℝ) (hC : 0 ≤ C) (hσ : 0 ≤ σ2)
    (hlocal : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ 1 → ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (W v ω - W u ω) | H u] ω -
        (Real.exp (-(v - u) * σ2 / 2) : ℂ)‖ ≤ C * (v - u) * Real.sqrt (v - u))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[H s] A) :
    (∫ ω in A, phase (W t ω - W s ω) ∂μ) =
      (Real.exp (-(t - s) * σ2 / 2) : ℂ) * ((μ A).toReal : ℂ) := by
  have hdiv : Tendsto (fun N : ℕ => (t - s) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim : Tendsto (fun N : ℕ => C * (t - s) * Real.sqrt ((t - s) / N))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C * (t - s))).mul hdiv.sqrt
  have hsmall : ∀ᶠ N : ℕ in atTop, (t - s) / (N : ℝ) ≤ 1 :=
    (hdiv.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono
      (fun _ h => h.le)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(∫ ω in A, phase (W t ω - W s ω) ∂μ) -
        (Real.exp (-(t - s) * σ2 / 2) : ℂ) * ((μ A).toReal : ℂ)‖ ≤
        C * (t - s) * Real.sqrt ((t - s) / N) := by
    filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
    exact time_partition_characteristic_error H hH hle W hW C σ2 hC hσ
      hlocal hs hst A hA N (by omega) hsmall
  have hz := ge_of_tendsto hlim hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

end Probability

end Problem336AdditiveD139.InnovationCharacteristic

end

end OAI
