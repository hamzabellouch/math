import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma smooth_deriv_infty {f : ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

lemma smoothTransition_flat_left {x : ℝ} (hx : x < 0) :
    deriv smoothTransition x = 0 ∧ deriv (deriv smoothTransition) x = 0 := by
  have he : smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩

lemma smoothTransition_flat_right {x : ℝ} (hx : 1 < x) :
    deriv smoothTransition x = 0 ∧ deriv (deriv smoothTransition) x = 0 := by
  have he : smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact smoothTransition.one_of_one_le hy.le
  exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩

lemma exists_transition_derivative_bound : ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ,
    |deriv smoothTransition x| ≤ M ∧ |deriv (deriv smoothTransition) x| ≤ M := by
  have hc : HasCompactSupport (deriv smoothTransition) := by
    apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
    intro x hx
    by_cases h : x < 0
    · exact (smoothTransition_flat_left h).1
    · exact (smoothTransition_flat_right (by simp only [mem_Icc, not_and_or, not_le] at hx
                                             rcases hx with hx | hx
                                             · exact False.elim (h hx)
                                             · exact hx)).1
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous
    (smooth_deriv_infty smoothTransition.contDiff).continuous
  obtain ⟨N,hN⟩ := hc.deriv.exists_bound_of_continuous
    (smooth_deriv_infty (smooth_deriv_infty smoothTransition.contDiff)).continuous
  refine ⟨max 1 (max M N), le_max_left _ _, fun x => ⟨?_,?_⟩⟩
  · exact (show |deriv smoothTransition x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans
      ((le_max_left M N).trans (le_max_right _ _))
  · exact (show |deriv (deriv smoothTransition) x| ≤ N by simpa only [Real.norm_eq_abs] using hN x).trans
      ((le_max_right M N).trans (le_max_right _ _))

def crossingOn (L z : ℝ) : ℝ := smoothTransition (4*z/L+3)
def crossingOff (L z : ℝ) : ℝ := 1 - smoothTransition (4*z/L-2)

def crossingFirst (L z : ℝ) : ℝ := crossingOff L z * exp (-3*z)
def crossingSecond (L z : ℝ) : ℝ := crossingOn L z * exp (-z)

lemma crossingOn_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingOn L) := by
  exact smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const L |>.add contDiff_const)
lemma crossingOff_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingOff L) := by
  exact contDiff_const.sub (smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).div_const L).sub contDiff_const))
lemma crossingFirst_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingFirst L) := by
  exact (crossingOff_smooth L).mul ((contDiff_const.mul contDiff_id).exp)
lemma crossingSecond_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingSecond L) := by
  exact (crossingOn_smooth L).mul (contDiff_id.neg.exp)

lemma crossingOn_bounds (L z : ℝ) : 0 ≤ crossingOn L z ∧ crossingOn L z ≤ 1 :=
  ⟨smoothTransition.nonneg _,smoothTransition.le_one _⟩
lemma crossingOff_bounds (L z : ℝ) : 0 ≤ crossingOff L z ∧ crossingOff L z ≤ 1 := by
  constructor <;> dsimp [crossingOff]
  · linarith [smoothTransition.le_one (4*z/L-2)]
  · linarith [smoothTransition.nonneg (4*z/L-2)]

lemma crossingOn_eq_zero {L z : ℝ} (hL : 0 < L) (hz : z ≤ -3*L/4) :
    crossingOn L z = 0 := by
  apply smoothTransition.zero_of_nonpos
  have : 4*z/L ≤ -3 := (div_le_iff₀ hL).mpr (by linarith)
  linarith
lemma crossingOn_eq_one {L z : ℝ} (hL : 0 < L) (hz : -L/2 ≤ z) :
    crossingOn L z = 1 := by
  apply smoothTransition.one_of_one_le
  have : -2 ≤ 4*z/L := (le_div_iff₀ hL).mpr (by linarith)
  linarith
lemma crossingOff_eq_one {L z : ℝ} (hL : 0 < L) (hz : z ≤ L/2) :
    crossingOff L z = 1 := by
  have : 4*z/L ≤ 2 := (div_le_iff₀ hL).mpr (by linarith)
  rw [crossingOff,smoothTransition.zero_of_nonpos (by linarith),sub_zero]
lemma crossingOff_eq_zero {L z : ℝ} (hL : 0 < L) (hz : 3*L/4 ≤ z) :
    crossingOff L z = 0 := by
  have : 3 ≤ 4*z/L := (le_div_iff₀ hL).mpr (by linarith)
  rw [crossingOff,smoothTransition.one_of_one_le (by linarith),sub_self]

lemma crossingOn_hasDerivAt (L z : ℝ) : HasDerivAt (crossingOn L)
    ((4/L)*deriv smoothTransition (4*z/L+3)) z := by
  have h := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (4*z/L+3)).hasDerivAt
  change HasDerivAt (fun w => smoothTransition (4*w/L+3)) ((4/L)*deriv smoothTransition (4*z/L+3)) z
  exact (h.comp z (((hasDerivAt_id z).const_mul 4).div_const L |>.add_const 3)).congr_deriv
    (g' := (4/L)*deriv smoothTransition (4*z/L+3))
    (by simp only [mul_one]; ring)
lemma crossingOff_hasDerivAt (L z : ℝ) : HasDerivAt (crossingOff L)
    (-(4/L)*deriv smoothTransition (4*z/L-2)) z := by
  have h := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (4*z/L-2)).hasDerivAt
  change HasDerivAt (fun w => 1-smoothTransition (4*w/L-2)) (-(4/L)*deriv smoothTransition (4*z/L-2)) z
  exact ((h.comp z ((((hasDerivAt_id z).const_mul 4).div_const L).sub_const 2)).const_sub 1).congr_deriv
    (g' := -(4/L)*deriv smoothTransition (4*z/L-2))
    (by simp only [mul_one]; ring)

lemma deriv_crossingOn (L : ℝ) : deriv (crossingOn L) =
    fun z => (4/L)*deriv smoothTransition (4*z/L+3) :=
  funext fun z => (crossingOn_hasDerivAt L z).deriv
lemma deriv_crossingOff (L : ℝ) : deriv (crossingOff L) =
    fun z => -(4/L)*deriv smoothTransition (4*z/L-2) :=
  funext fun z => (crossingOff_hasDerivAt L z).deriv

lemma crossingOn_second (L z : ℝ) : deriv (deriv (crossingOn L)) z =
    (4/L)^2*deriv (deriv smoothTransition) (4*z/L+3) := by
  rw [deriv_crossingOn]
  have h := ((smooth_deriv_infty smoothTransition.contDiff).differentiable (by simp) (4*z/L+3)).hasDerivAt
  have hh := (h.comp z ((((hasDerivAt_id z).const_mul 4).div_const L).add_const 3)).const_mul (4/L)
  convert hh.deriv using 1 <;> simp only [Function.comp_def, id_eq, mul_one]
  ring
lemma crossingOff_second (L z : ℝ) : deriv (deriv (crossingOff L)) z =
    -(4/L)^2*deriv (deriv smoothTransition) (4*z/L-2) := by
  rw [deriv_crossingOff]
  have h := ((smooth_deriv_infty smoothTransition.contDiff).differentiable (by simp) (4*z/L-2)).hasDerivAt
  have hh := (h.comp z ((((hasDerivAt_id z).const_mul 4).div_const L).sub_const 2)).const_mul (-(4/L))
  convert hh.deriv using 1 <;> simp only [Function.comp_def, id_eq, mul_one]
  ring

end ScalarConductivity

end

end OAI
