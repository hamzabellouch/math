import OAI.NumberTheory.CubicMoment.Estimates.ProfileCoprimeMass
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin

namespace OAI

/-! Uniform profile control of the actual radial form on the required dyad. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem smallB_radial_form_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (q : ℕ) (hq : q ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H : Finset Eisenstein) (β phase : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ N J : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N → 0 < J →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) 2) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) → (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      (1+ρ)^q*dyadicHeightMean (fun t =>
        ‖normCoprimeRadialForm S H
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/N) P.V ρ‖) T ≤
        (K*P.cost)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  let M := poissonProfileLogWidth
  have hM : 0 < M := poissonProfileLogWidth_pos
  obtain ⟨K,hK,hmass⟩ := smallB_coprime_mellin_height_power hMV hC hHuxley
    q hq
  refine ⟨K,hK,?_⟩
  intro P S H β phase Z B T u ρ N J hZ hB hT hρ hN hJ hS hrange hsize hH hHJ hphase
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
      |Real.log (norm h/J)-Real.log ((norm a/N)*(norm b/N))| ≤ M := by
    intro h hh a ha b hb
    exact compact_norm_log_ratio (by norm_num : (1:ℝ) ≤ 2)
      ⟨(le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1),
        (div_le_iff₀ hJ).mpr (hHJ h hh).2⟩ (hrange a ha) (hrange b hb)
  have hn (t : ℝ) := normCoprimeRadialForm_norm_le_mass M hM S H U
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) hU hSU
    (v t) (v t) phase hphase (fun h => norm h/J) (fun a => norm a/N)
    (fun h hh => (le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1))
    (fun a ha => zero_lt_one.trans_le (hrange a ha).1) hlog P.V P.compact P.smooth hρ
  have hf := normCoprimeRadialForm_continuous_coefficients S H v v hvc hvc
    phase (fun h => norm h/J) (fun a => norm a/N) P.V ρ
  have hg := continuous_integral_twistedCoprimeMellinMass S H U
    (fun a ha => (hS a ha).1) β (fun a => norm a/N)
    (𝓕 (normDenominatorLogSchwartz M hM P.V P.compact P.smooth ρ)).continuous.norm
    (normDenominatorMellinCoefficient_integrable M hM P.V P.compact P.smooth ρ).norm
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  have hh := dyadicHeightMean_mono hf.norm (hg.comp (continuous_id.add continuous_const)) hTp
    (fun t _ => hn t)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans
    (hmass P S H U β Z B T u ρ N hZ hB hT hρ hN hU hS hsize hH)

end CubicFirstMoment.ProfileControl

end

end OAI
