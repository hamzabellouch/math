import OAI.NumberTheory.CubicMoment.Estimates.UniformHighTail
import OAI.NumberTheory.CubicMoment.Estimates.HighStoppedTail

namespace OAI

/-! Uniform power width for actual stopped coefficients, chosen before
both their arity-dependent bound and the desired logarithmic saving. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_high_stopped_envelope_tail_uniform (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ M : ℝ, 0 ≤ M →
      ∀ (n : ℕ) (W : ℝ → ℂ), HasCompactSupport W →
        tsupport W ⊆ Set.Ioi 0 → ContDiff ℝ ∞ W →
        ∃ K Z₀ : ℝ, 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X T H : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ r ∈ R, primary r) → (∀ e ∈ E, primary e) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ r ∈ R, ‖v r‖ ≤ M) →
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → A ≤ Z^3 →
      0 < X → Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ‖envelopeCutoffBilinearTail P S (fun a => theta ℓ a*stoppedAlpha E U ψ w remaining a)
        (fun b => theta ℓ b*stoppedBeta R D v ψ w selected b) W H T X‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Ka,da,hKa,halpha⟩ := smallB_stopped_alpha_energy hpnt
  obtain ⟨Kb,db,hKb,hbeta⟩ := stopped_beta_log_energy hpnt
  obtain ⟨γ,hγ,huniform⟩ := high_energy_envelope_cutoff_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro M hM n W hW hpos hsm
  let Ma := 2*Ka*(4+Real.log 2)^da
  let Mb := M^2*Kb
  have hMa : 0 ≤ Ma := by dsimp [Ma]; positivity
  have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform Ma Mb hMa hMb n da db W hW hpos hsm
  refine ⟨K,max Z₀ 65536,hK,?_⟩
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
  have hαeq : (∑ a ∈ P, ‖theta ℓ a*stoppedAlpha E U ψ w remaining a‖^2) =
      ∑ a ∈ P, ‖stoppedAlpha E U ψ w remaining a‖^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [norm_theta_mul (primary_ne_zero (hP a ha).1)]
  have hβeq : (∑ b ∈ S, ‖theta ℓ b*stoppedBeta R D v ψ w selected b‖^2) =
      ∑ b ∈ S, ‖stoppedBeta R D v ψ w selected b‖^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [norm_theta_mul (primary_ne_zero (hS b hb).1)]
  exact hbound P S _ _ Z A X T H ((le_max_left _ _).trans hZ) hA hAu hX hT hH hHZ
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩) hS
    (hαeq.trans_le hea) (hβeq.trans_le heb)

end CubicFirstMoment

end

end OAI
