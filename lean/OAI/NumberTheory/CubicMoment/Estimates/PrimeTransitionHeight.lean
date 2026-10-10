import OAI.NumberTheory.CubicMoment.Estimates.PrimeTransitionBilinear
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimePrimeEstimate

namespace OAI

/-! The coarse height mean at the transition keeps the prime diagonal.
It supplies the full Mellin complement without a logarithmic gap between
the outer length and the square of the inner length. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem single_prime_transition_height_variance {γ : Type*}
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) :
    ∃ (η K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u T : ℝ), B₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
      (1+Real.log (L r))^m ≤ T → T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
      dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t)
        (fun x => (dispersionCutoff 4 x:ℂ)) A‖) T ≤ K*A^(2/3:ℝ)*(L r)^(5/3:ℝ) := by
  let V := fun x => (dispersionCutoff 4 x:ℂ)
  obtain ⟨η,σ,hη,hη1,hσ,hbound⟩ := height_coprime_dispersion_saving
    (γ := γ) (ι := Unit) (c := 1/2) (R := 2) hpub hHuxley hperiod hMV hC
    (by norm_num) (by norm_num) (by norm_num) hGI hGQ V
    (dispersionCutoff_complex_compact 4) (dispersionCutoff_complex_smooth 4) 0
  obtain ⟨K,B₀,m,hK,hbound⟩ := hbound L (fun r _ => W r) hL
    (uniformLogWeights_prime_coordinates L W hL hW) (fun r _ => hlo r) (fun r _ => hhi r)
  refine ⟨η,K+6480,B₀,m,hη,hη1,by positivity,?_⟩
  intro r A u T hB₀ hrough hAlo hAhi hT hThi hu
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hmem (p : Eisenstein) (hp : p ∈ S) :
      p ∈ fullPrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) () := by
    dsimp only [S] at hp
    rwa [fullSquarefreePrimeSupport_unit] at hp
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    fullPrimeSupport_prime 2 (fun _ : Unit => W r) (fun _ => L r) () p (hmem p hp)
  have henergy : (∑ p ∈ S, ‖β p‖^2) ≤ 36*L r := by
    apply bounded_prime_dyad_energy S β hB.le
    · intro p hp
      exact ⟨(hS p hp).1,(mem_primaryElementBall.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hmem p hp)).1).1).2⟩
    · intro p hp
      dsimp only [β]
      rw [fullPrimeCoefficient_unit (hmem p hp)]
      exact hW1 r _
  have hVM (x : ℝ) : ‖V x‖ ≤ 1 := by
    dsimp [V]
    rw [Complex.norm_real,Real.norm_of_nonneg (dispersionCutoff_nonneg 4 x)]
    exact (mul_le_mul (Real.smoothTransition.le_one _)
      (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1)
  have hd (v : ℝ) : ‖smoothedDispersionVariance S β v V A‖ ≤
      ‖coprimeDispersionGram S β v V A‖+3240*A*L r := by
    rw [prime_variance_split S hS β v V (dispersionCutoff_complex_compact 4)
      (dispersionCutoff_complex_smooth 4) hA]
    have hh := prime_dispersion_diagonal_bound S hS β v V hA (by norm_num : (0:ℝ) ≤ 5)
      (by norm_num : (0:ℝ) ≤ 1) hVM
      (fun x hx => by
        have hz := dispersionCutoff_high (R := 4) (x := x) (by linarith : (4:ℝ)+1 < x)
        simp only [V,hz,Complex.ofReal_zero])
    apply (norm_add_le _ _).trans
    apply (add_le_add (hh.trans (mul_le_mul_of_nonneg_left henergy (by positivity))) le_rfl).trans_eq
    ring
  have hv : Continuous (fun t : ℝ => ‖smoothedDispersionVariance S β (u+t) V A‖) :=
    ((continuous_smoothedDispersionVariance S (fun p hp => (hS p hp).1) β V
    (dispersionCutoff_complex_compact 4) (dispersionCutoff_complex_smooth 4) hA).comp
    (continuous_const.add continuous_id)).norm
  have hc : Continuous (fun t : ℝ => ‖coprimeDispersionGram S β (u+t) V A‖) :=
    ((continuous_coprimeDispersionGram S β V A).comp
    (continuous_const.add continuous_id)).norm
  have hm := dyadicHeightMean_mono hv (hc.add continuous_const) hTp (fun t _ => hd (u+t))
  change dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T ≤
    dyadicHeightMean (fun t => ‖coprimeDispersionGram S β (u+t) V A‖+3240*A*L r) T at hm
  rw [dyadicHeightMean_add hc continuous_const,dyadicHeightMean_const _ hTp.ne'] at hm
  have hb := hbound r (fun _ => L r) A 1 u T hB₀ (by simp) (fun _ => hrough)
    hAlo hAhi one_ne_zero (by simpa only [norm_one_eq] using Real.one_le_rpow (hL r) hσ.le)
    hT hThi hu
  simp only [pow_zero,div_one] at hb
  have hscale : A*L r ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ) := by
    have hh := cube_transition_scale hA hB hAhi
    have he : (L r)^(-(1/3:ℝ))*(L r)^2 = (L r)^(5/3:ℝ) := by
      rw [← Real.rpow_natCast (L r) 2,← Real.rpow_add hB]; norm_num
    calc
      _ = (A/L r)*(L r)^2 := by field_simp
      _ ≤ (A^(2/3:ℝ)*(L r)^(-(1/3:ℝ)))*(L r)^2 :=
        mul_le_mul_of_nonneg_right hh (sq_nonneg _)
      _ = _ := by rw [mul_assoc,he]
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left hscale (show (0:ℝ) ≤ 3240 by norm_num)
  change dyadicHeightMean (fun t => ‖coprimeDispersionGram S β (u+t) V A‖) T ≤ _ at hb
  exact (add_le_add hb (by nlinarith : 2*(3240*A*L r) ≤
    6480*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)))).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
