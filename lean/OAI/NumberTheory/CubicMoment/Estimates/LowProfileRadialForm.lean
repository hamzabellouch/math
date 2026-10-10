import OAI.NumberTheory.CubicMoment.Estimates.LowProfileCoprimeMass
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin

namespace OAI

/-! Uniform profile control of the actual radial form on the required dyad. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem low_radial_form_height_log_saving (hpnt : PrimaryPrimePNT) (k : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (q : ℕ) (hq : q ≤ 3) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H : Finset Eisenstein) (β phase : Eisenstein → ℂ)
      (Z : ℕ) (B T M u ρ N J : ℝ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ ρ → 0 < N → 0 < J →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) 2) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) → (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      (1+ρ)^q*dyadicHeightMean (fun t =>
        ‖normCoprimeRadialForm S H
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/N) P.V ρ‖) T ≤
        (K*P.cost)*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  let D := poissonProfileLogWidth
  have hD : 0 < D := poissonProfileLogWidth_pos
  obtain ⟨K,Ct,hK,hmass⟩ := low_coprime_mellin_height_log_saving hpnt k hMV hC hHuxley
    q hq
  refine ⟨K,Ct,hK,?_⟩
  intro P S H β phase Z B T M u ρ N J hZ hB hM hT hρ hN hJ hS hrange hβ hsize hH hHJ hphase
  let U := S.biUnion primaryPrimeFactors
  have hU : ∀ p ∈ U, primaryPrime p := by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hS a ha).1 hpa).1
  have hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := by
    intro a ha p hp
    exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩
  let v := fun t (a : Eisenstein) => star (β a*mellinPhase (t+u) (norm a))
  have hvc (a : Eisenstein) : Continuous (fun t => v t a) := by
    dsimp [v,mellinPhase]
    fun_prop
  have hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S,
      |Real.log (norm h/J)-Real.log ((norm a/N)*(norm b/N))| ≤ D := by
    intro h hh a ha b hb
    exact compact_norm_log_ratio (by norm_num : (1:ℝ) ≤ 2)
      ⟨(le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1),
        (div_le_iff₀ hJ).mpr (hHJ h hh).2⟩ (hrange a ha) (hrange b hb)
  have hn (t : ℝ) := normCoprimeRadialForm_norm_le_mass D hD S H U
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) hU hSU
    (v t) (v t) phase hphase (fun h => norm h/J) (fun a => norm a/N)
    (fun h hh => (le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1))
    (fun a ha => zero_lt_one.trans_le (hrange a ha).1) hlog P.V P.compact P.smooth hρ
  have hf := normCoprimeRadialForm_continuous_coefficients S H v v hvc hvc
    phase (fun h => norm h/J) (fun a => norm a/N) P.V ρ
  have hg := continuous_integral_twistedCoprimeMellinMass S H U
    (fun a ha => (hS a ha).1) β (fun a => norm a/N)
    (𝓕 (normDenominatorLogSchwartz D hD P.V P.compact P.smooth ρ)).continuous.norm
    (normDenominatorMellinCoefficient_integrable D hD P.V P.compact P.smooth ρ).norm
  have hZ1 : 1 ≤ (Z:ℝ) := by linarith
  have hlogpos : 0 < 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hlogpos _).trans_le hT
  have hh := dyadicHeightMean_mono hf.norm (hg.comp (continuous_id.add continuous_const)) hTp
    (fun t _ => hn t)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans
    (hmass P S H U β Z B T M u ρ N hZ hB hM hT hρ hN hU hS hβ hsize hH)

end CubicFirstMoment.ProfileControl

end

end OAI
