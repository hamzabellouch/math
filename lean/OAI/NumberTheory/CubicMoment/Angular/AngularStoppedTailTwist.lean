import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnergy
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope

namespace OAI

/-! Uniform common norm twists for the literal stopped coefficients.
Both coefficient energies are derived before restoring the product weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_stopped_twisted_cutoff_tail
    (hpnt : PrimaryPrimePNT) {C M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M) (n r a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X₀ T H : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ b ∈ R, primary b) → (∀ e ∈ E, primary e) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → 1 ≤ w →
      (∀ b ∈ R, ∀ p ∈ primaryPrimeFactors b, w ≤ norm p) →
      (∀ b ∈ R, ‖v b‖ ≤ M) → Z < w^r →
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → A ≤ Z^3 →
      0 < X₀ → (1+Real.log Z)^Ct ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ e ∈ P, primary e ∧ Squarefree e ∧ 1 ≤ norm e/A ∧ norm e/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) → ∀ u : ℝ,
      ‖cutoffBilinearTail P S
        (fun b => (theta ℓ b*stoppedAlpha E U ψ w remaining b)*normTwist u b)
        (fun b => (theta ℓ b*stoppedBeta R D v ψ w selected b)*normTwist u b) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Ka,d,hKa,halpha⟩ := smallB_stopped_alpha_energy hpnt
  let Ma := 2*Ka*(4+Real.log 2)^d
  let Mb := 18*((2^r:ℕ)*M)^2
  let Mbeta : ℝ := (2^r:ℕ)*M
  have hMa : 0 ≤ Ma := by dsimp [Ma]; positivity
  have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
  have hMbeta : 0 ≤ Mbeta := by dsimp [Mbeta]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := scaleFirst_energy_twisted_cutoff_tail hpnt hMV hC hHuxley
    hMa hMb hMbeta n d 0 a
  refine ⟨K,Ct,hK,?_⟩
  intro R D E U P S ψ w Z A X₀ T H v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hH hHZ hP hS u
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
  have hpupper (b : Eisenstein) (hb : b ∈ P) : norm b ≤ 2*A :=
    (div_le_iff₀ hAp).mp (hP b hb).2.2.2
  have hexp : Real.exp 1 ≤ 2*A := by
    have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    linarith
  have hea : (∑ b ∈ P, ‖stoppedAlpha E U ψ w remaining b‖^2) ≤
      Ma*A*(1+Real.log Z)^d := by
    apply (halpha E U P ψ w (2*A) remaining hE hψ hexp
      (fun b hb => ⟨(hP b hb).1,(hP b hb).2.1,hpupper b hb⟩)).trans
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
  have hαeq : (∑ b ∈ P, ‖theta ℓ b*stoppedAlpha E U ψ w remaining b‖^2) =
      ∑ b ∈ P, ‖stoppedAlpha E U ψ w remaining b‖^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [norm_theta_mul (primary_ne_zero (hP b hb).1)]
  have hβeq : (∑ b ∈ S, ‖theta ℓ b*stoppedBeta R D v ψ w selected b‖^2) =
      ∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [norm_theta_mul (primary_ne_zero (hS b hb).1)]
  exact hbound P S (fun b => theta ℓ b*stoppedAlpha E U ψ w remaining b)
    (fun b => theta ℓ b*stoppedBeta R D v ψ w selected b)
    Z A X₀ T H hZ hA hAupper hX hT hH hHZ
    (fun b hb => ⟨(hP b hb).1,(hP b hb).2.2⟩) hS
    (fun b hb => by rw [norm_theta_mul (primary_ne_zero (hS b hb).1)]; exact hbeta b hb)
    (hαeq.trans_le hea) (hβeq.trans_le heb) u

end CubicFirstMoment

end

end OAI
