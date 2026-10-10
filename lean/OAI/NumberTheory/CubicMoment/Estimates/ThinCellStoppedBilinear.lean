import OAI.NumberTheory.CubicMoment.Estimates.ThinCellLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.SmallBStoppedBilinear

namespace OAI

/-! The thin-cell estimate for literal stopped coefficients. Their energies
are proved from the divisor moment and roughness, rather than assumed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma outer_log_energy_conversion_cubic {A Z K : ℝ} (hA : 1 ≤ A) (hZ : 1 ≤ Z)
    (hAZ : A ≤ Z^3) (hK : 0 ≤ K) (d : ℕ) :
    K*(2*A)*(1+Real.log (2*A))^d ≤
      (2*K*(4+Real.log 2)^d)*A*(1+Real.log Z)^d := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hlA : Real.log A ≤ 3*Real.log Z := by
    have hh := Real.log_le_log hA0 hAZ
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlZ := Real.log_nonneg hZ
  have hl2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hl : 1+Real.log (2*A) ≤ (4+Real.log 2)*(1+Real.log Z) := by
    rw [Real.log_mul (by norm_num) hA0.ne']
    nlinarith [mul_nonneg hl2 hlZ]
  have hp := pow_le_pow_left₀
    (show 0 ≤ 1+Real.log (2*A) by
      have hh := Real.log_nonneg (show 1 ≤ 2*A by linarith)
      linarith) hl d
  calc
    _ ≤ K*(2*A)*((4+Real.log 2)*(1+Real.log Z))^d :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem thinCell_stopped_bilinear_log_saving
    (hpnt : PrimaryPrimePNT) {C M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M) (j r : ℕ) :
    ∃ (γ K : ℝ), 0 < γ ∧ 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A T u : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ b ∈ R, primary b) → (∀ a ∈ E, primary a) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → 1 ≤ w →
      (∀ b ∈ R, ∀ p ∈ primaryPrimeFactors b, w ≤ norm p) →
      (∀ b ∈ R, ‖v b‖ ≤ M) → Z < w^r →
      65536 ≤ Z → Z^(2-1/80000:ℝ) ≤ A → A ≤ Z^(2+γ) → A ≤ Z^3 → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧
        1+1/(4*Z^γ) ≤ norm a/A ∧ norm a/A ≤ 1+3/(4*Z^γ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S,
          stoppedAlpha E U ψ w remaining a*stoppedBeta R D v ψ w selected b*
            gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨Ka,d,hKa,halpha⟩ := smallB_stopped_alpha_energy hpnt
  let Ma := 2*Ka*(4+Real.log 2)^d
  let Mb := 18*((2^r:ℕ)*M)^2
  have hMa : 0 ≤ Ma := by dsimp [Ma]; positivity
  have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
  obtain ⟨γ,K,hγ,hK,hbound⟩ := thinCell_bilinear_log_saving hMV hC hHuxley hMa hMb j d 0
  refine ⟨γ,K,hγ,hK,?_⟩
  intro R D E U P S ψ w Z A T u v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hT hP hS
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hZA : Z ≤ A := by
    calc
      Z = Z^(1:ℝ) := (Real.rpow_one Z).symm
      _ ≤ Z^(2-1/80000:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      _ ≤ A := hA
  have hA1 : 1 ≤ A := hZ1.trans hZA
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hJ : 1 ≤ Z^γ := Real.one_le_rpow hZ1 hγ.le
  have hpupper (a : Eisenstein) (ha : a ∈ P) : norm a ≤ 2*A := by
    have hh : 3/(4*Z^γ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hr : norm a/A ≤ 2 := by linarith [(hP a ha).2.2.2]
    exact (div_le_iff₀ hAp).mp hr
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
  exact hbound P S (stoppedAlpha E U ψ w remaining) (stoppedBeta R D v ψ w selected)
    Z A T u hZ hA hAupper hT (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩) hS hea heb

end CubicFirstMoment

end

end OAI
