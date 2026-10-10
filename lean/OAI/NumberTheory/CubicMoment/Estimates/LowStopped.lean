import OAI.NumberTheory.CubicMoment.Estimates.LowNormalized
import OAI.NumberTheory.CubicMoment.Estimates.ThinCellStoppedBilinear

namespace OAI

/-! Low-height localization for the actual stopped coefficients. The
outer and inner energies are derived from their divisor definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem low_localized_stopped_bilinear_log_saving
    (hpnt : PrimaryPrimePNT) {C M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M) (j r a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X₀ T Mₕ : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ b ∈ R, primary b) → (∀ a ∈ E, primary a) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → 1 ≤ w →
      (∀ b ∈ R, ∀ p ∈ primaryPrimeFactors b, w ≤ norm p) →
      (∀ b ∈ R, ‖v b‖ ≤ M) → Z < w^r →
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → A ≤ Z^3 →
      0 < X₀ → (1+Real.log Z)^Ct ≤ T → 0 ≤ Mₕ →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧
        1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ Mₕ) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ Mₕ) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) h X₀ T‖ ≤
        K*Mₕ*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨Ka,d,hKa,halpha⟩ := smallB_stopped_alpha_energy hpnt
  let Ma := 2*Ka*(4+Real.log 2)^d
  let Mb := 18*((2^r:ℕ)*M)^2
  have hMa : 0 ≤ Ma := by dsimp [Ma]; positivity
  have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
  let Mbeta : ℝ := (2^r:ℕ)*M
  have hMbeta : 0 ≤ Mbeta := by dsimp [Mbeta]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := low_localized_integral_log_saving hpnt hMV hC hHuxley
    hMa hMb hMbeta j d 0 a
  refine ⟨K,Ct,hK,?_⟩
  intro R D E U P S ψ w Z A X₀ T Mₕ v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hMₕ hP hS h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hZbig : 65536 ≤ Z := by nlinarith
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hZA : Z ≤ A := by
    calc
      Z = Z^(1:ℝ) := (Real.rpow_one Z).symm
      _ ≤ Z^(3/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      _ ≤ A := by linarith [Real.rpow_nonneg hZp.le (3/2:ℝ)]
  have hA1 : 1 ≤ A := hZ1.trans hZA
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hpupper (a : Eisenstein) (ha : a ∈ P) : norm a ≤ 2*A :=
    (div_le_iff₀ hAp).mp (hP a ha).2.2.2
  have hexp : Real.exp 1 ≤ 2*A := by
    have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    linarith
  have hea : (∑ a ∈ P, ‖stoppedAlpha E U ψ w remaining a‖^2) ≤
      Ma*A*(1+Real.log Z)^d := by
    apply (halpha E U P ψ w (2*A) remaining hE hψ hexp
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,hpupper a ha⟩)).trans
    exact outer_log_energy_conversion_cubic hA1 hZ1 hAcubic hKa.le d
  have heb : (∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2) ≤
      Mb*Z*(1+Real.log Z)^0 := by
    have hh := smallB_stopped_beta_energy R D S hR hψ w hw hrough selected v hM
      hZp.le hv r hsize (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩)
    dsimp only [Mb]
    simpa only [pow_zero,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hh
  have hbeta : ∀ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖ ≤ Mbeta := by
    intro b hb
    exact stoppedBeta_rough_bound R D hR hψ w hw hrough selected v hM hv
      (hS b hb).1 (hS b hb).2.1 ((hS b hb).2.2.2.trans_lt hsize)
  exact hbound P S (stoppedAlpha E U ψ w remaining) (stoppedBeta R D v ψ w selected)
    Z A X₀ T Mₕ hZ hA hAupper hX hT hMₕ
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩) hS hbeta hea heb
    h hi hd hi' hd' hi'' hh hs hh2 hs2

end CubicFirstMoment

end

end OAI
