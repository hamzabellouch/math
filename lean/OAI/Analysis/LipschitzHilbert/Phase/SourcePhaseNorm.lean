import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftSimplex

namespace OAI

/-! Coordinate bounds on the actual shift simplex, and the polynomial
budget for the linear node envelope at arbitrary imaginary phases. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem sourceShiftSimplex_phase_norm {mu : ℝ} (a eta : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) (i : ι) :
    ‖phaseTubePoint a eta i‖ ≤ mu+Real.sqrt (∑ j, (eta j)^2) := by
  have hai : a i ≤ mu := by
    calc
      a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)
      _ = mu := ha.2
  have hsq : (eta i)^2 ≤ ∑ j, (eta j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (eta j)) (Finset.mem_univ i)
  have heta : |eta i| ≤ Real.sqrt (∑ j, (eta j)^2) :=
    (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr
      (by simpa only [sq_abs] using hsq)
  calc
    ‖phaseTubePoint a eta i‖ ≤ ‖(a i:ℂ)‖+‖(eta i:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = a i+|eta i| := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha.1 i),norm_mul,
        Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    _ ≤ _ := add_le_add hai heta

theorem sourceShiftSimplex_phase_re {mu : ℝ} (a eta : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) (i : ι) :
    0 ≤ (phaseTubePoint a eta i).re := by
  simpa only [phaseTubePoint,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
    mul_zero,zero_mul,sub_zero,add_zero] using ha.1 i

/-- The explicit node-envelope coefficient grows at most linearly in
 the imaginary norm; its remaining factors are fixed powers of L. -/
theorem eventually_source_linear_phase_budget (C q : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (a Z A r H : ℝ) (K : ℕ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ r → Z ≤ 1+r →
      0 ≤ A → A ≤ L^q → (K:ℝ) ≤ L^2 → 0 ≤ H → H ≤ 3*L →
      C^8*A*(1+(a+Z*K)*(H+1))*C^3 ≤ L^(q+4)*(1+r) := by
  filter_upwards [eventually_ge_atTop (max 1 (9*C^11))] with L hLlarge
  intro a Z A r H K ha ha1 hZ hr hZr hA hAq hK hH hHL
  have hL : 1 ≤ L := (le_max_left _ _).trans hLlarge
  have hCL : 9*C^11 ≤ L := (le_max_right _ _).trans hLlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpoly : 1+(a+Z*K)*(H+1) ≤ 9*(1+r)*L^3 := by
    have hZK : Z*(K:ℝ) ≤ (1+r)*L^2 :=
      mul_le_mul hZr hK (Nat.cast_nonneg K) (by positivity)
    have hprod := mul_le_mul
      (show a+Z*K ≤ 1+(1+r)*L^2 by linarith)
      (show H+1 ≤ 4*L by linarith)
      (by linarith : 0 ≤ H+1) (by positivity : 0 ≤ 1+(1+r)*L^2)
    have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
    have hL3 : L ≤ L^3 := by nlinarith
    have hrL : 0 ≤ r*L^3 := by positivity
    nlinarith
  calc
    _ = C^11*A*(1+(a+Z*K)*(H+1)) := by ring
    _ ≤ C^11*(L^q)*(9*(1+r)*L^3) := mul_le_mul
      (mul_le_mul_of_nonneg_left hAq (by positivity)) hpoly
      (by positivity) (by positivity)
    _ = (9*C^11)*L^q*L^3*(1+r) := by ring
    _ ≤ L*L^q*L^3*(1+r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL (by positivity))
          (by positivity)) (by positivity)
    _ = L^(q+4)*(1+r) := by
      have he : L*L^q*L^3 = L^(q+4) := by
        rw [mul_assoc,← Real.rpow_natCast,← Real.rpow_add hL0]
        calc
          L*L^(q+3) = L^(1:ℝ)*L^(q+3) := by rw [Real.rpow_one]
          _ = L^(q+4) := by rw [← Real.rpow_add hL0]; congr 1; ring
      rw [he]

end LipschitzHilbert

end

end OAI
