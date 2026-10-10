import OAI.NumberTheory.JointDickman.Analysis.MellinPrefixInterval
import OAI.NumberTheory.JointDickman.Analysis.MellinLowFrequencyEnergy

namespace OAI

/-! # Uniform low-frequency estimates for integer dyadic subintervals -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem angularMellin_uniform_dyadic_low (f : ℝ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x n, ‖f x n‖ ≤ C) (hf0 : ∀ x, f x 0 = 0)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊A*x⌋₊, f x n)/(x:ℂ)) atTop (𝓝 0))
    {a b T ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, a*x ≤ N → (N:ℝ) ≤ b*x →
      ∀ t : ℝ, |t| ≤ T → ‖angularMellinPolynomial (Ioc N (2*N)) (f x) t‖ ≤ ε := by
  let δ := ε*a/(5+3*T)
  have hd : 0 < 5+3*T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [uniform_prefix_of_marginal_means f hC hf hmean (2*b)
    (by positivity) hδ,eventually_gt_atTop (0:ℝ)] with x hpre hx
  intro N hlo hhi t ht
  have hn : (0:ℝ)<N := (mul_pos ha hx).trans_le hlo
  have hp : ∀ u ∈ Set.Icc (N:ℝ) (2*(N:ℝ)),
      ‖∑ n ∈ Icc 0 ⌊u⌋₊, f x n‖ ≤ δ*x := by
    intro u hu
    rw [←Ioc_insert_left (Nat.zero_le ⌊u⌋₊),sum_insert (by simp),hf0,zero_add]
    exact hpre u ⟨hn.le.trans hu.1,hu.2.trans (by linarith)⟩
  have hh := angularMellinPolynomial_le_of_prefix_interval (f x) hn
    (by linarith : (N:ℝ) ≤ 2*N) (by linarith : 2*(N:ℝ) ≤ 4*N)
    hT (mul_nonneg hδ.le hx.le) ht hp
  have heq : (2*N:ℝ) = ((2*N:ℕ):ℝ) := by push_cast; rfl
  rw [heq,Nat.floor_natCast,Nat.floor_natCast] at hh
  apply hh.trans
  calc
    (5+3*T)*(δ*x)/(N:ℝ) = ε*(a*x)/(N:ℝ) := by dsimp [δ]; field_simp
    _ ≤ ε := (div_le_iff₀ hn).mpr (mul_le_mul_of_nonneg_left hlo hε.le)

end JointDickman

end OAI
