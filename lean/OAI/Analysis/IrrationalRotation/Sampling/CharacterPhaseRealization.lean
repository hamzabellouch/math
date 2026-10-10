import OAI.Analysis.IrrationalRotation.Sampling.PrescribedPhaseRealization
import OAI.Analysis.IrrationalRotation.Sampling.CharacterLawConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

namespace Invariant233
namespace PrescribedPhaseRealization

open Filter
open scoped Topology

theorem exists_phase_approximation_family {θ : ℝ} (hθ : Irrational θ)
    (target : ℕ → ℝ) (htarget₀ : ∀ i, 0 < target i)
    (htarget₁ : ∀ i, target i < 1) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ → ℕ,
      (∀ j, q j 0 = q₀) ∧ (∀ j i, 0 < q j i) ∧
      (∀ j, StrictMono (q j)) ∧ (∀ j i, q j i ∣ q j (i + 1)) ∧
      (∀ i, Tendsto (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop) ∧
      ∀ i, Tendsto (fun j => Int.fract ((q j (i + 1) : ℝ) * θ)) atTop
        (𝓝 (target i)) := by
  classical
  have hex : ∀ j : ℕ, ∃ q : ℕ → ℕ,
      q 0 = q₀ ∧ (∀ i, 0 < q i) ∧
      ∀ i, q i ∣ q (i + 1) ∧ q i < q (i + 1) ∧
        (j + 1) * q i ≤ q (i + 1) ∧
        |Int.fract ((q (i + 1) : ℝ) * θ) - target i| < 1 / ((j : ℝ) + 1) := by
    intro j
    exact exists_divisible_phase_approximation hθ target
      (fun _ => 1 / ((j : ℝ) + 1)) (fun _ => j + 1)
      htarget₀ htarget₁ (fun _ => by positivity) hq₀
  choose q hzero hpos hstep using hex
  refine ⟨q, hzero, hpos, ?_, ?_, ?_, ?_⟩
  · intro j
    exact strictMono_nat_of_lt_succ (fun i => (hstep j i).2.1)
  · intro j i
    exact (hstep j i).1
  · intro i
    apply tendsto_atTop_mono (f := fun j : ℕ => (j : ℝ) + 1)
    · intro j
      apply (le_div_iff₀ (by exact_mod_cast hpos j i)).mpr
      exact_mod_cast (hstep j i).2.2.1
    · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.dist_eq] using (hstep j i).2.2.2.le

theorem exists_joint_phase_character_limit {θ : ℝ} (hθ : Irrational θ)
    (target : ℕ → ℝ) (htarget₀ : ∀ i, 0 < target i)
    (htarget₁ : ∀ i, target i < 1) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ → ℕ,
      (∀ j, q j 0 = q₀) ∧ (∀ j i, 0 < q j i) ∧
      (∀ j, StrictMono (q j)) ∧ (∀ j i, q j i ∣ q j (i + 1)) ∧
      (∀ i, Tendsto (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop) ∧
      (∀ i, Tendsto (fun j => Int.fract ((q j (i + 1) : ℝ) * θ)) atTop
        (𝓝 (target i))) ∧
      ∀ m : ℕ, Tendsto (fun j => CharacterLaws.characterPhaseLaw
          (fun i : Fin m => q j (i.val + 1))
          (fun i : Fin m => Int.fract ((q j (i.val + 1) : ℝ) * θ))) atTop
        (𝓝 (CharacterLaws.haarPhaseLaw m (fun i : Fin m => target i.val))) := by
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hphase⟩ :=
    exists_phase_approximation_family hθ target htarget₀ htarget₁ hq₀
  refine ⟨q, hzero, hpos, hstrict, hdiv, hgap, hphase, ?_⟩
  intro m
  apply CharacterLaws.tendsto_characterPhaseLaw (fun j i => q j (i + 1)) m
  · intro j i
    exact hpos j (i + 1)
  · intro j i k hik
    exact (hstrict j).monotone (Nat.add_le_add_right hik 1)
  · intro i _hi
    exact hgap (i + 1)
  · exact tendsto_pi_nhds.mpr (fun i : Fin m => hphase i.val)

end PrescribedPhaseRealization
end Invariant233

end OAI
