import OAI.NumberTheory.CubicMoment.Estimates.WidePoissonRecurrence
import OAI.NumberTheory.CubicMoment.Estimates.AllFrequencyOuterSieve
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin

namespace OAI

/-! The actual coprime Poisson annulus, including cube frequencies,
for the compact norm interval of a common-factor quotient. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment

 theorem coprime_poisson_outer_annulus {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ) (j : ℕ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      (1+Z*2^j/(27*N^2))^3 * ‖coprimePoissonDyad S (frequencyDyad j) u W Z‖ ≤
        C*(Z/N)*(4*2^j*(R*N))^ε*
          (2*2^j+(2*2^j*(R*N))^(2/3:ℝ)+(2*2^j)^(1/3:ℝ)*(R*N))*
            ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  have hM : 0 < 1+2*Real.log R := by linarith [Real.log_nonneg hR]
  obtain ⟨C₁,hC₁,hrec⟩ := wide_coprimePoissonDyad_norm_recurrence
    (1+2*Real.log R) hM W hW hW' 3
  obtain ⟨C₂,hC₂,houter⟩ := all_frequency_cubic_operator_bound hε
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro S u Z N j hZ hN hS
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hJ : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hs : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hlog : ∀ h ∈ frequencyDyad j, ∀ a ∈ S, ∀ b ∈ S,
      |Real.log (norm h/2^j)-Real.log ((norm a/N)*(norm b/N))| ≤ 1+2*Real.log R := by
    intro h hh a ha b hb
    apply compact_norm_log_ratio hR
    · exact ⟨(le_div_iff₀ (by positivity : (0:ℝ) < 2^j)).mpr
        (by simpa only [one_mul] using (frequencyDyad_norm hh).1),
        (div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).mpr (frequencyDyad_norm hh).2⟩
    · exact ⟨(le_div_iff₀ hNp).mpr (by simpa only [one_mul] using (hS a ha).2.2.1),
        (div_le_iff₀ hNp).mpr (hS a ha).2.2.2⟩
    · exact ⟨(le_div_iff₀ hNp).mpr (by simpa only [one_mul] using (hS b hb).2.2.1),
        (div_le_iff₀ hNp).mpr (hS b hb).2.2.2⟩
  have hr := hrec S (frequencyDyad j) hs u Z (2^j) N hZ.le (by positivity) hNp
    (fun a ha => (hS a ha).2.2.1)
    (fun h hh => (by positivity : (0:ℝ) < 2^j).trans_le (frequencyDyad_norm hh).1) hlog
  have hb := houter S (frequencyDyad j) (2*2^j) (R*N) (by nlinarith) (by nlinarith)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
    (fun h hh => ⟨(mem_frequencyDyad.mp hh).1,(frequencyDyad_norm hh).2⟩)
  apply hr.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ C₁*(Z/N))) (Finset.sum_nonneg (fun _ _ => by positivity))).trans_eq
  congr 1
  rw [show 2*(2*2^j)*(R*N) = 4*2^j*(R*N) by ring]
  ring

end CubicFirstMoment

end

end OAI
