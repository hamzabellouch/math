import OAI.Probability.InvariantIsing.Haar.HaarKernelMass

namespace OAI

/-! Uniform approximation by positive polynomial Haar convolution. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem haarKernelApprox_error {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (B ε a : ℝ)
    (hB : 0 ≤ B) (hfB : ∀ V, |f V| ≤ B) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (hloc : ∀ U V, a < haarKernelBase 1 V → |f (U*V)-f U| ≤ ε)
    (n : ℕ) (U : SpecialOrthogonal N) :
    |haarPolynomialValue (haarKernelApprox μ f n) U-f U| ≤
      ε+2*B*(a^n/haarKernelMass μ n) := by
  let Z := haarKernelMass μ n
  let k (V : SpecialOrthogonal N) := (haarKernelBase 1 V)^n
  have hZ : 0 < Z := haarKernelMass_pos hN μ n
  have hk : Continuous k := (continuous_haarKernelBase 1).pow n
  have hi : Integrable (fun V => (f (U*V)-f U)*k V) μ :=
    continuous_haar_integrable μ _ (((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).mul hk)
  have he : haarPolynomialValue (haarKernelApprox μ f n) U-f U =
      Z⁻¹*(∫ V, (f (U*V)-f U)*k V ∂μ) := by
    simp only [haarKernelApprox,haarPolynomialValue,map_smul,smul_eq_mul]
    change Z⁻¹*haarPolynomialValue (haarKernelAverage μ f n) U-f U = _
    rw [haarKernelAverage_convolution μ f hf]
    have he' : (∫ V, (f (U*V)-f U)*k V ∂μ) =
        (∫ V, f (U*V)*k V ∂μ)-f U*Z := by
      simp_rw [sub_mul]
      have hi1 : Integrable (fun V => f (U*V)*k V) μ :=
        continuous_haar_integrable μ _ ((hf.comp (continuous_const.mul continuous_id)).mul hk)
      have hi2 : Integrable (fun V => f U*k V) μ :=
        (continuous_haar_integrable μ _ hk).const_mul (f U)
      rw [integral_sub hi1 hi2,integral_const_mul]
      rfl
    rw [he']
    dsimp only [k]
    field_simp
  have hb (V : SpecialOrthogonal N) :
      |(f (U*V)-f U)*k V| ≤ ε*k V+2*B*a^n := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg (haarKernelBase_nonneg 1 V) n)]
    by_cases hV : a < haarKernelBase 1 V
    · have hh := mul_le_mul_of_nonneg_right (hloc U V hV)
        (pow_nonneg (haarKernelBase_nonneg 1 V) n)
      have ht : 0 ≤ 2*B*a^n := by positivity
      exact hh.trans (le_add_of_nonneg_right ht)
    · have hbd : |f (U*V)-f U| ≤ 2*B := (abs_sub (f (U*V)) (f U)).trans (by linarith [hfB (U*V),hfB U])
      have hpow : k V ≤ a^n := pow_le_pow_left₀ (haarKernelBase_nonneg 1 V) (le_of_not_gt hV) n
      have hh := mul_le_mul hbd hpow (pow_nonneg (haarKernelBase_nonneg 1 V) n) (by positivity : 0 ≤ 2*B)
      have ht : 0 ≤ ε*k V := mul_nonneg hε (pow_nonneg (haarKernelBase_nonneg 1 V) n)
      exact hh.trans (le_add_of_nonneg_left ht)
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hZ)]
  have hI : |∫ V, (f (U*V)-f U)*k V ∂μ| ≤ ε*Z+2*B*a^n := by
    calc
      _ ≤ ∫ V, |(f (U*V)-f U)*k V| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ V, ε*k V+2*B*a^n ∂μ :=
        integral_mono hi.abs (((continuous_haar_integrable μ _ hk).const_mul ε).add (integrable_const _)) hb
      _ = ε*Z+2*B*a^n := by
        rw [integral_add ((continuous_haar_integrable μ _ hk).const_mul ε) (integrable_const _),integral_const_mul]
        simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
        rfl
  calc
    _ ≤ Z⁻¹*(ε*Z+2*B*a^n) := mul_le_mul_of_nonneg_left hI (inv_pos.mpr hZ).le
    _ = ε+2*B*(a^n/Z) := by field_simp

theorem haarKernelApprox_uniform {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U,
      |haarPolynomialValue (haarKernelApprox μ f n) U-f U| ≤ ε := by
  intro ε hε
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hfB (V : SpecialOrthogonal N) : |f V| ≤ B := by simpa only [Real.norm_eq_abs] using hB V (mem_univ V)
  have hB0 : 0 ≤ B := (abs_nonneg (f 1)).trans (hfB 1)
  let δ := ε/(2*L)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hL)
  have hδeq : L*δ = ε/2 := by dsimp [δ]; field_simp
  let a := max 0 (2*N-δ^2/2)
  have ha : 0 ≤ a := le_max_left _ _
  have haN : a < 2*N := max_lt (by positivity) (by nlinarith [sq_pos_of_pos hδ])
  have hloc (U V : SpecialOrthogonal N) (hV : a < haarKernelBase 1 V) :
      |f (U*V)-f U| ≤ ε/2 := by
    have hda : 2*N-δ^2/2 < haarKernelBase 1 V := (le_max_right _ _).trans_lt hV
    rw [haarKernelBase_dist] at hda
    have hd : frobeniusDistance 1 V < δ := by nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ((1 : Matrix (Fin N) (Fin N) ℝ) i j-(V : Matrix (Fin N) (Fin N) ℝ) i j)^2)]
    have hh := hLip (U*V) (U*1)
    rw [frobeniusDistance_mul_left,mul_one,frobeniusDistance_comm V 1] at hh
    have hh' := mul_lt_mul_of_pos_left hd hL
    rw [hδeq] at hh'
    exact hh.trans hh'.le
  have ht : Tendsto (fun n : ℕ => 2*B*(a^n/haarKernelMass μ n)) atTop (𝓝 0) := by
    simpa using (haarKernelMass_ratio_tendsto_zero hN μ a ha haN).const_mul (2*B)
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))] with n hn U
  have hh := haarKernelApprox_error hN μ f hf B (ε/2) a hB0 hfB (by positivity) ha hloc n U
  linarith

end InvariantIsing

end

end OAI
