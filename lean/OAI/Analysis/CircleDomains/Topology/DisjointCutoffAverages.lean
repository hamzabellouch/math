import OAI.Analysis.CircleDomains.Sobolev.ScaledCutoffEnergy

namespace OAI

/-! Averaging cutoffs with disjoint transition sets divides their common
Dirichlet energy by the number of cutoffs. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem norm_sq_sum_disjoint {I E : Type*} [NormedAddCommGroup E]
    (s : Finset I) (v : I → E)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i ∈ s, v i‖^2 = ∑ i ∈ s, ‖v i‖^2 := by
  classical
  by_cases hn : ∃ i ∈ s, v i ≠ 0
  · obtain ⟨i, hi, hvi⟩ := hn
    have hz (j) (hj : j ∈ s) (hji : j ≠ i) : v j = 0 := (h j hj i hi hji).resolve_right hvi
    rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi]),
      Finset.sum_eq_single i (fun j hj hji => by simp [hz j hj hji]) (by simp [hi])]
  · have hz (i) (hi : i ∈ s) : v i = 0 := by
      by_contra hne
      exact hn ⟨i, hi, hne⟩
    rw [Finset.sum_eq_zero (fun i hi => hz i hi),
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])]
    simp

 def cutoffAverage (f : ℕ → ℂ → ℝ) (N : ℕ) : ℂ → ℝ :=
    fun z => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f i z

 theorem cutoffAverage_smooth (f : ℕ → ℂ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (N : ℕ) :
    ContDiff ℝ ∞ (cutoffAverage f N) :=
  contDiff_const.mul (ContDiff.sum (fun i _ => hf i))

 theorem cutoffAverage_fderiv (f : ℕ → ℂ → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) (N : ℕ) (z : ℂ) :
    fderiv ℝ (cutoffAverage f N) z =
      (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, fderiv ℝ (f i) z := by
  exact ((HasFDerivAt.fun_sum (fun i _ => (hf i z).hasFDerivAt)).const_mul (N : ℝ)⁻¹).fderiv

 theorem cutoffAverage_compact (f : ℕ → ℂ → ℝ) (hs : ∀ i, HasCompactSupport (f i)) (N : ℕ) :
    HasCompactSupport (cutoffAverage f N) := by
  have hh : HasCompactSupport (fun z : ℂ => ∑ i ∈ Finset.range N, f i z) := by
    simpa only [Finset.sum_fn] using
      (HasCompactSupport.finset_sum (s := Finset.range N) (f := f) (fun i _ => hs i))
  change HasCompactSupport ((fun _ : ℂ => (N : ℝ)⁻¹) *
    (fun z : ℂ => ∑ i ∈ Finset.range N, f i z))
  exact hh.mul_left

 theorem cutoffAverage_mem_unit (f : ℕ → ℂ → ℝ)
    (hf : ∀ i z, f i z ∈ Icc (0 : ℝ) 1) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    cutoffAverage f N z ∈ Icc (0 : ℝ) 1 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, f i z := Finset.sum_nonneg (fun i _ => (hf i z).1)
  have hsum1 : ∑ i ∈ Finset.range N, f i z ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hf i z).2)
      _ = _ := by simp
  change 0 ≤ (N : ℝ)⁻¹ * _ ∧ (N : ℝ)⁻¹ * _ ≤ 1
  exact ⟨mul_nonneg (inv_pos.mpr hn).le hsum0, (inv_mul_le_iff₀ hn).mpr (by simpa using hsum1)⟩

 theorem cutoffAverage_one (f : ℕ → ℂ → ℝ) {N : ℕ} (hN : 0 < N) {z : ℂ}
    (hf : ∀ i ∈ Finset.range N, f i z = 1) : cutoffAverage f N z = 1 := by
  simp only [cutoffAverage, Finset.sum_congr rfl hf, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')

 theorem cutoffAverage_energy (f : ℕ → ℂ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hs : ∀ i, HasCompactSupport (f i))
    (hdisj : ∀ z i j, i ≠ j → fderiv ℝ (f i) z = 0 ∨ fderiv ℝ (f j) z = 0)
    {C : ℝ} (hC : ∀ i, (∫ z, ‖fderiv ℝ (f i) z‖^2) = C)
    {N : ℕ} (hN : 0 < N) :
    (∫ z, ‖fderiv ℝ (cutoffAverage f N) z‖^2) = (N : ℝ)⁻¹*C := by
  have hdiff (i) : Differentiable ℝ (f i) := (hf i).differentiable (by simp)
  have he (z : ℂ) : ‖fderiv ℝ (cutoffAverage f N) z‖^2 =
      (N : ℝ)⁻¹^2 * ∑ i ∈ Finset.range N, ‖fderiv ℝ (f i) z‖^2 := by
    rw [cutoffAverage_fderiv f hdiff N, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)), mul_pow]
    rw [norm_sq_sum_disjoint (Finset.range N) _ (fun i _ j _ hij => hdisj z i j hij)]
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => smooth_cutoff_energy_integrable (hf i) (hs i))]
  simp only [hC, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

end CircleDomainRigidity

end

end OAI
