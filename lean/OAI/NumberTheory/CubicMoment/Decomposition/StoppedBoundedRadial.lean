import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedMellin
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin

namespace OAI

/-! The literal bounded-coefficient Poisson annulus, with its square-root
norm denominator and unrestricted original height. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_coprime_radial_form (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve) {R : ℝ} (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S H : Finset Eisenstein)
      (β phase : Eisenstein → ℂ) (N M B u ρ L J : ℝ),
      65536 ≤ N → 0 ≤ M → 1 ≤ B → 0 ≤ ρ → 0 < L → 0 < J →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → (∀ a ∈ S, norm a/L ∈ Icc (1:ℝ) R) →
      8*B ≤ N^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) → (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      (1+ρ)^q*‖normCoprimeRadialForm S H
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun a => star (β a*mellinPhase u (norm a))) phase
        (fun h => norm h/J) (fun a => norm a/L) V ρ‖ ≤
      K*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d := by
  let m := 1+2*Real.log R
  have hm : 0 < m := by dsimp [m]; linarith [Real.log_nonneg hR]
  obtain ⟨K,d,hK,hbound⟩ := bounded_coprime_mellin_integral hpnt hHuxley m hm V hV hV' q
  refine ⟨K,d,hK,?_⟩
  intro S H β phase N M B u ρ L J hN hM hB hρ hL hJ hS hβ hrange hsize hH hHJ hphase
  let U := S.biUnion primaryPrimeFactors
  have hU : ∀ p ∈ U, primaryPrime p := by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hS a ha).1 hpa).1
  have hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := by
    intro a ha p hp
    exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩
  have hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S,
      |Real.log (norm h/J)-Real.log ((norm a/L)*(norm b/L))| ≤ m := by
    intro h hh a ha b hb
    exact compact_norm_log_ratio hR
      ⟨(le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1),
        (div_le_iff₀ hJ).mpr (hHJ h hh).2⟩ (hrange a ha) (hrange b hb)
  have hn := normCoprimeRadialForm_norm_le_mass m hm S H U
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) hU hSU
    (fun a => star (β a*mellinPhase u (norm a)))
    (fun a => star (β a*mellinPhase u (norm a))) phase hphase
    (fun h => norm h/J) (fun a => norm a/L)
    (fun h hh => (le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1))
    (fun a ha => zero_lt_one.trans_le (hrange a ha).1) hlog V hV hV' hρ
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans
    (hbound S H U β N M B u ρ L hN hM hB hρ hL hS hβ hU hsize hH)

end CubicFirstMoment

end

end OAI
