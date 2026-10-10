import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeNearbySum
import OAI.NumberTheory.JointDickman.Amplification.MinorArcStrongApproximation

namespace OAI

/-! # The squarefree exponential bound off the manuscript's rational arcs -/
namespace JointDickman
open Finset

theorem squarefree_minor_arc_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B : ℕ) (X θ V : ℝ),
    0 < N → 2 ≤ B → (80:ℝ)*Real.log B ≤ B →
    (B:ℝ)/2 ≤ Real.log N → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ X → X ≤ (N:ℝ)*(B:ℝ)^2 → (N:ℝ) ≤ V*X →
    ¬ InRationalArc θ ((B:ℝ)^12) ((B:ℝ)^13/X) →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      C*(1+2*Real.pi*V)*N*(1+Real.log B)/(B:ℝ) := by
  obtain ⟨C,hC,hnear⟩ := squarefree_near_rational_sum_bound
  refine ⟨C,hC,?_⟩
  intro f hf hb hs N B X θ V hN hB hlogB hloglo hloghi hX hXN hNV hminor
  have hB0 : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hX0 : 0 < X := (pow_pos hB0 12).trans_le hX
  have hm : ¬ InRationalArc θ ((B:ℝ)^12) ((B:ℝ)^12/X) := by
    rintro ⟨r,hr,he⟩
    apply hminor
    refine ⟨r,hr,he.trans ?_⟩
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hB1 (by norm_num : 12 ≤ 13)) hX0.le
  obtain ⟨r,hrlo,hrhi,herr⟩ := minorArc_strong_rational_approximation (pow_pos hB0 12) hX hm
  have hqN : (r.den:ℝ) ≤ (N:ℝ)/(B:ℝ)^10 := by
    apply hrhi.trans
    calc
      _ ≤ ((N:ℝ)*(B:ℝ)^2)/(B:ℝ)^12 := div_le_div_of_nonneg_right hXN (pow_nonneg hB0.le 12)
      _ = _ := by field_simp
  apply hnear f hf hb hs N B r.den r.num θ V hN hB hlogB hloglo hloghi
    r.pos r.reduced hrlo.le hqN
  have hh := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg N)
  have hv : (N:ℝ)/X ≤ V := (div_le_iff₀ hX0).mpr hNV
  have hh' : (N:ℝ)*|θ-(r:ℝ)| ≤ (N:ℝ)/X := by
    simpa only [mul_one_div] using hh
  simpa only [Rat.cast_def] using hh'.trans hv

end JointDickman

end OAI
