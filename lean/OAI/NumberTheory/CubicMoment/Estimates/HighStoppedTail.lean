import OAI.NumberTheory.CubicMoment.Estimates.HighEnergyTail
import OAI.NumberTheory.CubicMoment.Estimates.SmallBStoppedAlphaEnergy
import OAI.NumberTheory.CubicMoment.Estimates.ThinCellStoppedBilinear

namespace OAI

/-! The upper stopped branch needs no prime roughness. Its actual divisor
coefficients have logarithmic second moments, sufficient for the power-width
height estimate. The total-product envelope remains present. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem stopped_beta_log_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (R D S : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w X M : ℝ) (v : Eisenstein → ℂ)
      (selected : Eisenstein → Eisenstein → Prop),
      (∀ r ∈ R, primary r) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      0 ≤ M → (∀ r ∈ R, ‖v r‖ ≤ M) → Real.exp 1 ≤ X →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) →
      (∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2) ≤
        (M^2*K)*X*(1+Real.log X)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_divisor_second_moment hpnt
  refine ⟨K,d,hK,?_⟩
  intro R D S ψ w X M v selected hR hψ hM hv hX hS
  have hb (b : Eisenstein) (hbs : b ∈ S) :
      ‖stoppedBeta R D v ψ w selected b‖ ≤ (2:ℝ)^(primaryPrimeFactors b).card*M := by
    apply (stoppedBeta_divisor_bound R D hR hψ w selected v hM hv b).trans
    apply mul_le_mul_of_nonneg_right _ hM
    exact_mod_cast primary_squarefree_divisor_card R hR (hS b hbs).1 (hS b hbs).2.1
  calc
    _ ≤ ∑ b ∈ S, M^2*(4:ℝ)^(primaryPrimeFactors b).card := by
      apply Finset.sum_le_sum
      intro b hbs
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (hb b hbs) 2).trans_eq
      rw [mul_pow,←pow_mul,Nat.mul_comm (primaryPrimeFactors b).card 2,pow_mul]
      norm_num
      ring
    _ = M^2*∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card := (Finset.mul_sum _ _ _).symm
    _ ≤ M^2*(K*X*(1+Real.log X)^d) :=
      mul_le_mul_of_nonneg_left (hmoment X S hX hS) (sq_nonneg M)
    _ = _ := by ring

theorem high_stopped_envelope_tail (hpnt : PrimaryPrimePNT)
    {C M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M)
    (n : ℕ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ γ K Z₀ : ℝ, 0 < γ ∧ 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X T H : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ r ∈ R, primary r) → (∀ e ∈ E, primary e) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ r ∈ R, ‖v r‖ ≤ M) →
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → A ≤ Z^3 →
      0 < X → Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ‖envelopeCutoffBilinearTail P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) W H T X‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Ka,da,hKa,halpha⟩ := smallB_stopped_alpha_energy hpnt
  obtain ⟨Kb,db,hKb,hbeta⟩ := stopped_beta_log_energy hpnt
  let Ma := 2*Ka*(4+Real.log 2)^da
  let Mb := M^2*Kb
  have hMa : 0 ≤ Ma := by dsimp [Ma]; positivity
  have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := high_energy_envelope_cutoff_tail hMV hC hHuxley
    hMa hMb n da db W hW hpos hsm
  refine ⟨γ,K,max Z₀ 65536,hγ,hK,?_⟩
  intro R D E U P S ψ w Z A X T H v selected remaining hR hE hψ hv hZ hA hAu hA3
    hX hT hH hHZ hP hS
  have hZbig : 65536 ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hZA : Z ≤ A := by
    calc
      Z = Z^(1:ℝ) := (Real.rpow_one Z).symm
      _ ≤ Z^(3/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      _ ≤ A := by linarith [Real.rpow_nonneg hZp.le (3/2:ℝ)]
  have hA1 : 1 ≤ A := hZ1.trans hZA
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hexpZ : Real.exp 1 ≤ Z := by
    have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    linarith
  have hea : (∑ a ∈ P, ‖stoppedAlpha E U ψ w remaining a‖^2) ≤
      Ma*A*(1+Real.log Z)^da := by
    apply (halpha E U P ψ w (2*A) remaining hE hψ (by linarith)
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,
        (div_le_iff₀ hAp).mp (hP a ha).2.2.2⟩)).trans
    exact outer_log_energy_conversion_cubic hA1 hZ1 hA3 hKa.le da
  have heb : (∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2) ≤
      Mb*Z*(1+Real.log Z)^db := hbeta R D S ψ w Z M v selected hR hψ hM hv hexpZ
        (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩)
  exact hbound P S _ _ Z A X T H ((le_max_left _ _).trans hZ) hA hAu hX hT hH hHZ
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩) hS hea heb

end CubicFirstMoment

end

end OAI
