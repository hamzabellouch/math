import OAI.NumberTheory.JointDickman.Analysis.LogPhaseUniform
import OAI.NumberTheory.JointDickman.Analysis.CharacterFourierExpansion

namespace OAI

/-! # Character twists of logarithmic exponential sums -/
namespace JointDickman
open Complex Filter Problem337
open scoped Topology

lemma imaginary_power_as_log_phase (t : ℝ) {n : ℤ} (hn : 0 < n) :
    (n:ℂ)^(-((t:ℂ)*I)) =
      differencingPhase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hnC]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp,←Complex.ofReal_log hn0.le]
  unfold differencingPhase
  congr 1
  push_cast
  field_simp

/-- A character contributes at most the finite Fourier expansion factor q.
The power saving is uniform in the character. -/
theorem character_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (t : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))‖ ≤
          (q:ℝ)*A*U^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := logarithmic_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with U hbound hU
  intro q _ χ t L R hlo hhi hL hR
  have he : (∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) =
      ∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*
        differencingPhase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hLn : (L:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0:ℝ) < n := hU.trans_le (hL.trans hLn)
    rw [imaginary_power_as_log_phase t (by exact_mod_cast hn0)]
  rw [he]
  have hh := character_log_sum_bound χ (Finset.Icc L R) (-t/(2*Real.pi))
    (A*U^(1-δ)) (by positivity) (fun a => hbound a (-t/(2*Real.pi)) L R
      (by simpa only [neg_div,abs_neg] using hlo)
      (by simpa only [neg_div,abs_neg] using hhi) hL hR)
  simpa only [mul_assoc] using hh

end JointDickman

end OAI
