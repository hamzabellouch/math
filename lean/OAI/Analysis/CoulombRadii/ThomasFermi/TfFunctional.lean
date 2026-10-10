import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TFNonneg

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
noncomputable def tfFunctional (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f : TFLp μ) : ℝ :=
  c * ‖f‖^(5/3:ℝ) - L f + B f f / 2
lemma tfFunctional_continuous (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) : Continuous (tfFunctional c L B) := by
  unfold tfFunctional
  exact ((continuous_norm.rpow_const (fun _ => Or.inr (by norm_num : (0:ℝ) ≤ 5/3))).const_mul c).sub L.continuous |>.add
    ((B.continuous₂.comp (continuous_id.prodMk continuous_id)).div_const 2)
lemma tfFunctional_midpoint (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f g : TFLp μ) :
    (tfFunctional c L B f+tfFunctional c L B g)/2 - tfFunctional c L B ((1/2:ℝ) • (f+g)) =
      c*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)) + B (f-g) (f-g)/8 := by
  unfold tfFunctional
  simp only [map_add,map_smul,map_sub,_root_.add_apply,_root_.smul_apply,
    _root_.sub_apply,smul_eq_mul]
  ring
lemma tfFunctional_midpoint_nonneg {c : ℝ} (hc : 0 ≤ c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    tfFunctional c L B ((1/2:ℝ) • (f+g)) ≤ (tfFunctional c L B f+tfFunctional c L B g)/2 := by
  have H := tfFunctional_midpoint c L B f g
  have hn := add_nonneg (mul_nonneg hc (tfLp_gap_nonneg hf hg)) (div_nonneg (hB (f-g)) (by norm_num : (0:ℝ)≤8))
  linarith
lemma tfFunctional_lower {c : ℝ} (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) (f : TFLp μ) :
    c*‖f‖^(5/3:ℝ)-‖L‖*‖f‖ ≤ tfFunctional c L B f := by
  have HL : L f ≤ ‖L‖*‖f‖ := (le_abs_self _).trans (L.le_opNorm f)
  have HB := hB f
  unfold tfFunctional
  linarith
lemma tf_superlinear_bound {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, R ≤ s → s ≤ c*s^(5/3:ℝ)-K*s := by
  let a := (K+1)/c
  have ha : 0 < a := div_pos (by linarith) hc
  refine ⟨a^(3/2:ℝ),Real.rpow_pos_of_pos ha _,?_⟩
  intro s hs
  have hs0 : 0 < s := (Real.rpow_pos_of_pos ha _).trans_le hs
  have H := Real.rpow_le_rpow (Real.rpow_nonneg ha.le _) hs (by norm_num : (0:ℝ)≤2/3)
  rw [← Real.rpow_mul ha.le] at H
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,Real.rpow_one] at H
  have Hc : K+1 ≤ c*s^(2/3:ℝ) := by
    have := mul_le_mul_of_nonneg_left H hc.le
    dsimp [a] at this
    field_simp at this
    nlinarith
  have hp : s^(5/3:ℝ) = s*s^(2/3:ℝ) := by
    have H := Real.rpow_add hs0 (1:ℝ) (2/3:ℝ)
    norm_num at H ⊢
    exact H
  rw [hp]
  nlinarith
lemma tfFunctional_bddBelow {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) (S : Set (TFLp μ)) :
    BddBelow (tfFunctional c L B '' S) := by
  obtain ⟨R,hR,hRb⟩ := tf_superlinear_bound hc (norm_nonneg L)
  refine ⟨-‖L‖*R,?_⟩
  rintro a ⟨f,hf,rfl⟩
  have H := tfFunctional_lower (c := c) L B hB f
  by_cases hs : R ≤ ‖f‖
  · have HH := hRb ‖f‖ hs
    have hn : -‖L‖*R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg _)) hR.le
    linarith [norm_nonneg f]
  · have Hp := mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg f) (5/3:ℝ))
    have Hn := mul_le_mul_of_nonneg_left (le_of_not_ge hs) (norm_nonneg L)
    linarith
lemma tfFunctional_sublevel_bound {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) (a : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ f : TFLp μ, tfFunctional c L B f ≤ a → ‖f‖ ≤ R := by
  obtain ⟨R,hR,hRb⟩ := tf_superlinear_bound hc (norm_nonneg L)
  refine ⟨max R a,lt_of_lt_of_le hR (le_max_left _ _),?_⟩
  intro f hf
  by_cases hs : R ≤ ‖f‖
  · exact (hRb ‖f‖ hs |>.trans (tfFunctional_lower (c := c) L B hB f) |>.trans hf).trans (le_max_right _ _)
  · exact (le_of_not_ge hs).trans (le_max_left _ _)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
