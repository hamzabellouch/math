import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLogNormDerivatives
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLogarithmicSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianEquation

namespace OAI

/-! Cartesian symbol estimates obtained from the actual outgoing expansion. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radial_log_composition_symbol (H : ℝ → ℂ) (L σ : ℝ)
    (hH : ContDiffOn ℝ ∞ H (Ioi L))
    (hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv i H t‖ ≤ C*Real.exp (σ*t)) (k : ℕ) :
    ∃ D R : ℝ, 0 ≤ D ∧ 0 < R ∧ ∀ y : E, R ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k (fun x : E => H (Real.log ‖x‖)) y‖ ≤
        D*‖y‖^(σ-(k : ℝ)) := by
  choose C hC hbound using hb
  have he : ∀ᶠ t in atTop, ∀ i ∈ Finset.range (k+1),
      ‖iteratedDeriv i H t‖ ≤ C i*Real.exp (σ*t) :=
    (eventually_all_finset _).mpr (fun i _ => hbound i)
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  choose B hB hlog using (fun j : ℕ => radialLogNorm_derivative_bound (j+1) (by omega))
  let A := ∑ i ∈ Finset.range (k+1), C i
  let D := 1+∑ i ∈ Finset.range k, B i
  let U := max T (L+1)
  let S : Set E := {y | Real.exp U < ‖y‖}
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hC i)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hS : IsOpen S := isOpen_lt continuous_const continuous_norm
  have hSL (y : E) (hy : y ∈ S) : L < Real.log ‖y‖ := by
    have hl := Real.log_lt_log (Real.exp_pos U) hy
    rw [Real.log_exp] at hl
    exact lt_trans (lt_of_lt_of_le (by linarith : L < L+1) (le_max_right _ _)) hl
  have hSy (y : E) (hy : y ∈ S) : y ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos U).trans hy)
  have hf : ContDiffOn ℝ ∞ (fun y : E => Real.log ‖y‖) S :=
    fun y hy => (radialLogNorm_contDiffAt y (hSy y hy)).contDiffWithinAt
  have hm : MapsTo (fun y : E => Real.log ‖y‖) S (Ioi L) := hSL
  refine ⟨(k.factorial : ℝ)*A*D^k,Real.exp (U+1),by positivity,Real.exp_pos _,?_⟩
  intro y hy
  have hyS : y ∈ S :=
    lt_of_lt_of_le (Real.exp_lt_exp.mpr (by linarith : U < U+1)) hy
  have hyr : 0 < ‖y‖ := norm_pos_iff.mpr (hSy y hyS)
  have hyL : L < Real.log ‖y‖ := hSL y hyS
  have hyT : T ≤ Real.log ‖y‖ := by
    have hl := Real.log_lt_log (Real.exp_pos U) hyS
    rw [Real.log_exp] at hl
    exact (le_max_left _ _).trans hl.le
  have houter (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i H (Ioi L) (Real.log ‖y‖)‖ ≤
        A*Real.exp (σ*Real.log ‖y‖) := by
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hyL,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hmem : i ∈ Finset.range (k+1) := Finset.mem_range.mpr (by omega)
    exact (hT _ hyT i hmem).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hC j) hmem) (Real.exp_pos _).le)
  have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i (fun x : E => Real.log ‖x‖) S y‖ ≤ (D/‖y‖)^i := by
    rw [iteratedFDerivWithin_of_isOpen i hS hyS]
    have hmem : i-1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    have hBi : B (i-1) ≤ D := by
      have hh := Finset.single_le_sum (fun j _ => hB j) hmem
      dsimp [D]
      linarith
    have hpow : B (i-1) ≤ D^i := hBi.trans (le_self_pow₀ hD (by omega))
    have hh := hlog (i-1) y (hSy y hyS)
    rw [show i-1+1=i by omega] at hh
    apply hh.trans
    calc
      B (i-1)*‖y‖^(-(i : ℝ)) ≤ D^i*‖y‖^(-(i : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hyr.le _)
      _ = (D/‖y‖)^i := by rw [Real.rpow_neg hyr.le,Real.rpow_natCast,div_pow,div_eq_mul_inv]
  have hh := norm_iteratedFDerivWithin_comp_le hH hf (by simp : (k : ℕ∞ω) ≤ ∞)
    isOpen_Ioi.uniqueDiffOn hS.uniqueDiffOn hm hyS houter hinner
  rw [iteratedFDerivWithin_of_isOpen k hS hyS] at hh
  apply hh.trans_eq
  have hrpow : Real.exp (σ*Real.log ‖y‖)=‖y‖^σ := by
    rw [Real.rpow_def_of_pos hyr]
    congr 1
    ring
  rw [hrpow,div_pow,Real.rpow_sub hyr,Real.rpow_natCast]
  ring

end DefocusingNLS

end OAI
