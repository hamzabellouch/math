import OAI.NumberTheory.SiegelZeros.EntireFunctions.AvoidZeroRadii

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

theorem summable_indexed_regularized_reciprocals {ι : Type*} (ρ : ι → ℂ)
    (hρ : ∀ i, ρ i ≠ 0) {z : ℂ} (hz : ∀ i, z ≠ ρ i)
    (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2))
    (hfar : ∀ᶠ i in Filter.cofinite, 2 * ‖z‖ ≤ ‖ρ i‖) :
    Summable (fun i => (z - ρ i)⁻¹ + (ρ i)⁻¹) := by
  apply (hsquare.mul_left (2 * ‖z‖)).of_norm_bounded_eventually
  filter_upwards [hfar] with i hi
  convert norm_regularized_reciprocal_le (hρ i) (hz i) hi using 1; ring

variable {q : ℕ} [NeZero q]

theorem actual_zeroValue_ne_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) (i : W51.ZeroIndex χ) : W51.zeroValue χ i ≠ 0 := by
  intro hz
  have h := (W51.zeroValue_mem_strip χ hχ hprimitive i).1
  simp only [hz, Complex.zero_re, lt_self_iff_false] at h

theorem actual_zero_sums_summable_of_growth (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ, ‖W51.normalizedCompletion χ z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : W51.normalizedCompletion χ z ≠ 0) :
    Summable (fun i : W51.ZeroIndex χ =>
      (z - W51.zeroValue χ i)⁻¹ + (W51.zeroValue χ i)⁻¹) ∧
    Summable (fun i : W51.ZeroIndex χ => ((W51.zeroValue χ i)⁻¹).re) ∧
    Summable (fun i : W51.ZeroIndex χ => ((z - W51.zeroValue χ i)⁻¹).re) := by
  have hsquare := actual_zero_inverse_square_summable_of_growth χ hχ hprimitive hC hgrowth
  have hzne : ∀ i : W51.ZeroIndex χ, z ≠ W51.zeroValue χ i := by
    intro i hi
    apply hz
    rw [hi]
    exact W51.zeroValue_is_zero χ i
  have hreg := summable_indexed_regularized_reciprocals (W51.zeroValue χ)
    (actual_zeroValue_ne_zero χ hχ hprimitive) hzne hsquare
    (W51.zeroValue_cofinite_far χ hχ (2 * ‖z‖))
  have hinv := summable_reciprocal_re (W51.zeroValue χ)
    (fun i => ⟨(W51.zeroValue_mem_strip χ hχ hprimitive i).1.le,
      (W51.zeroValue_mem_strip χ hχ hprimitive i).2.le⟩) hsquare
  exact ⟨hreg, hinv, summable_real_zero_contributions (W51.zeroValue χ) z hreg hinv⟩

theorem actual_canonicalProduct_locallyUniform_of_growth (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ, ‖W51.normalizedCompletion χ z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {R : ℝ} (hR : 0 < R) :
    MultipliableLocallyUniformlyOn
      (fun i : W51.ZeroIndex χ => genusOneFactor (W51.zeroValue χ i)) (Metric.ball 0 R) :=
  multipliableLocallyUniformlyOn_genusOne (W51.zeroValue χ)
    (actual_zeroValue_ne_zero χ hχ hprimitive)
    (actual_zero_inverse_square_summable_of_growth χ hχ hprimitive hC hgrowth) hR
    (W51.zeroValue_cofinite_far χ hχ R)

theorem actual_canonicalProduct_logDeriv_of_growth (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ, ‖W51.normalizedCompletion χ z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : W51.normalizedCompletion χ z ≠ 0) :
    logDeriv (fun w => ∏' i : W51.ZeroIndex χ, genusOneFactor (W51.zeroValue χ i) w) z =
      ∑' i : W51.ZeroIndex χ, ((z - W51.zeroValue χ i)⁻¹ + (W51.zeroValue χ i)⁻¹) := by
  have hρ := actual_zeroValue_ne_zero χ hχ hprimitive
  have hsquare := actual_zero_inverse_square_summable_of_growth χ hχ hprimitive hC hgrowth
  have hzne : ∀ i : W51.ZeroIndex χ, z ≠ W51.zeroValue χ i := by
    intro i hi
    apply hz
    rw [hi]
    exact W51.zeroValue_is_zero χ i
  apply logDeriv_indexedGenusOneProduct (W51.zeroValue χ) hρ
    (U := Metric.ball 0 (‖z‖ + 1)) Metric.isOpen_ball
    (by simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖z‖) hzne
  · exact (actual_zero_sums_summable_of_growth χ hχ hprimitive hC hgrowth hz).1
  · exact actual_canonicalProduct_locallyUniform_of_growth χ hχ hprimitive hC hgrowth (by positivity)
  · exact genusOneProduct_ne_zero (W51.zeroValue χ) hρ hsquare hzne
      (W51.zeroValue_cofinite_far χ hχ ‖z‖)

end SiegelZerosAwei.W03

end

end SiegelZeros

end OAI
