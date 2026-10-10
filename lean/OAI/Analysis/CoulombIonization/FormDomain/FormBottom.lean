import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoerciveOperator

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def formLift (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) : H →L[ℂ] V :=
  (coerciveEquiv A hc hA).symm.toContinuousLinearMap.comp j.adjoint

lemma formLift_eq (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (y : H) :
    A (formLift j A hc hA y) = j.adjoint y :=
  (coerciveEquiv A hc hA).apply_symm_apply _

lemma formLift_inner (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (u : V) (y : H) :
    ⟪u, A (formLift j A hc hA y)⟫_ℂ = ⟪j u, y⟫_ℂ := by
  rw [formLift_eq, j.adjoint_inner_right]

lemma formResolvent_apply (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (y : H) :
    formResolvent j A hc hA y = j (formLift j A hc hA y) := rfl

lemma formLift_self (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (y : H) :
    ⟪formLift j A hc hA y, A (formLift j A hc hA y)⟫_ℂ =
      ⟪formResolvent j A hc hA y, y⟫_ℂ := formLift_inner j A hc hA _ y

lemma formResolvent_positive (j : V →L[ℂ] H) (A : V →L[ℂ] V)
    (hs : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) :
    (formResolvent j A hc hA).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨formResolvent_selfAdjoint j A hs hc hA, fun y => ?_⟩
  change 0 ≤ (⟪formResolvent j A hc hA y, y⟫_ℂ).re
  rw [← formLift_self]
  exact (mul_nonneg hc.le (sq_nonneg _)).trans (hA _)

omit [CompleteSpace V] in
lemma coercive_nonneg (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (u : V) :
    0 ≤ (⟪u, A u⟫_ℂ).re := (mul_nonneg hc.le (sq_nonneg _)).trans (hA u)

lemma hermitian_quadratic_sub (A : V →L[ℂ] V) (hs : IsSelfAdjoint A) (u v : V) :
    (⟪u - v, A (u - v)⟫_ℂ).re =
      (⟪u, A u⟫_ℂ).re - 2 * (⟪u, A v⟫_ℂ).re + (⟪v, A v⟫_ℂ).re := by
  have he : (⟪v, A u⟫_ℂ).re = (⟪u, A v⟫_ℂ).re := by
    have hh : ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs) u v
    rw [← hh]
    exact inner_re_symm (𝕜 := ℂ) v (A u)
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [Complex.sub_re]
  rw [he]
  ring

omit [CompleteSpace H] in
lemma bounded_quadratic_upper (R : H →L[ℂ] H) (y : H) :
    (⟪R y, y⟫_ℂ).re ≤ ‖R‖ * ‖y‖ ^ 2 := by
  calc
    _ ≤ ‖R y‖ * ‖y‖ := by simpa only [RCLike.re_eq_complex_re] using re_inner_le_norm (𝕜 := ℂ) (R y) y
    _ ≤ (‖R‖ * ‖y‖) * ‖y‖ := mul_le_mul_of_nonneg_right (R.le_opNorm y) (norm_nonneg _)
    _ = _ := by ring

omit [CompleteSpace H] in
lemma injective_norm_pos [Nontrivial H] (R : H →L[ℂ] H) (hinj : Function.Injective R) :
    0 < ‖R‖ := by
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  apply hx
  apply hinj
  simp [hz]

lemma form_reciprocal_resolvent_bound [Nontrivial H] (j : V →L[ℂ] H)
    (hj : Function.Injective j) (hd : DenseRange j) (A : V →L[ℂ] V)
    (hs : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (u : V) :
    ‖formResolvent j A hc hA‖⁻¹ * ‖j u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
  let R := formResolvent j A hc hA
  have hR : 0 < ‖R‖ := injective_norm_pos R (formResolvent_injective j hj hd A hc hA)
  let y : H := (‖R‖⁻¹ : ℂ) • j u
  let v := formLift j A hc hA y
  have hp := coercive_nonneg A hc hA (u - v)
  rw [hermitian_quadratic_sub A hs] at hp
  have hv : ⟪v, A v⟫_ℂ = ⟪R y, y⟫_ℂ := formLift_self j A hc hA y
  have huv : (⟪u, A v⟫_ℂ).re = ‖R‖⁻¹ * ‖j u‖ ^ 2 := by
    rw [formLift_inner]
    simp [y, norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hny : ‖y‖ ^ 2 = ‖R‖⁻¹ ^ 2 * ‖j u‖ ^ 2 := by
    simp [y, norm_smul, mul_pow]
  have hq := bounded_quadratic_upper R y
  rw [hny] at hq
  rw [hv, huv] at hp
  have hn : ‖R‖ * (‖R‖⁻¹ ^ 2 * ‖j u‖ ^ 2) = ‖R‖⁻¹ * ‖j u‖ ^ 2 := by
    field_simp
  rw [hn] at hq
  change ‖R‖⁻¹ * ‖j u‖ ^ 2 ≤ _
  linarith

lemma resolvent_norm_le_of_form_bound (j : V →L[ℂ] H) (A : V →L[ℂ] V)
    {c : ℝ} (hc : 0 < c) (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re)
    {b : ℝ} (hb : 0 < b) (hbound : ∀ u, b * ‖j u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) :
    ‖formResolvent j A hc hA‖ ≤ b⁻¹ := by
  let R := formResolvent j A hc hA
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hb.le)
  intro y
  have hv := hbound (formLift j A hc hA y)
  rw [formLift_self] at hv
  change b * ‖R y‖ ^ 2 ≤ (⟪R y, y⟫_ℂ).re at hv
  have hi : (⟪R y, y⟫_ℂ).re ≤ ‖R y‖ * ‖y‖ := re_inner_le_norm (𝕜 := ℂ) _ _
  by_cases hz : ‖R y‖ = 0
  · change ‖R y‖ ≤ _
    rw [hz]
    exact mul_nonneg (inv_nonneg.mpr hb.le) (norm_nonneg _)
  · have hn : 0 < ‖R y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hby : b * ‖R y‖ ≤ ‖y‖ := by nlinarith
    change ‖R y‖ ≤ b⁻¹ * ‖y‖
    exact (le_inv_mul_iff₀ hb).mpr hby

omit [CompleteSpace V] [CompleteSpace H] in
lemma form_lower_of_unit (j : V →L[ℂ] H) (hj : Function.Injective j)
    (A : V →L[ℂ] V) {b : ℝ}
    (hb : ∀ u, ‖j u‖ ^ 2 = 1 → b ≤ (⟪u, A u⟫_ℂ).re) (u : V) :
    b * ‖j u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
  by_cases hz : j u = 0
  · have hu : u = 0 := hj (hz.trans (map_zero j).symm)
    simp [hu]
  have hn : 0 < ‖j u‖ := norm_pos_iff.mpr hz
  let v : V := (‖j u‖⁻¹ : ℂ) • u
  have hnv : ‖j v‖ ^ 2 = 1 := by
    simp [v, norm_smul, hn.ne']
  have hv := hb v hnv
  have he : (⟪v, A v⟫_ℂ).re = (‖j u‖ ^ 2)⁻¹ * (⟪u, A u⟫_ℂ).re := by
    simp [v, Complex.mul_re, pow_two]
    ring
  rw [he] at hv
  simpa only [mul_comm] using (le_inv_mul_iff₀ (sq_pos_of_pos hn)).mp hv

omit [CompleteSpace V] [CompleteSpace H] in

lemma denseRange_exists_nonzero [Nontrivial H] (j : V →L[ℂ] H) (hd : DenseRange j) :
    ∃ u, j u ≠ 0 := by
  by_contra! h
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hh : x = 0 := hd.induction_on x (isClosed_eq continuous_id continuous_const) (fun u => h u)
  exact hx hh

theorem form_infimum_eq_reciprocal [Nontrivial H] (j : V →L[ℂ] H)
    (hj : Function.Injective j) (hd : DenseRange j) (A : V →L[ℂ] V)
    (hs : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) :
    sInf {e : ℝ | ∃ u : V, ‖j u‖ ^ 2 = 1 ∧ (⟪u, A u⟫_ℂ).re = e} =
      ‖formResolvent j A hc hA‖⁻¹ := by
  let S := {e : ℝ | ∃ u : V, ‖j u‖ ^ 2 = 1 ∧ (⟪u, A u⟫_ℂ).re = e}
  let R := formResolvent j A hc hA
  have hR : 0 < ‖R‖ := injective_norm_pos R (formResolvent_injective j hj hd A hc hA)
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := denseRange_exists_nonzero j hd
    let v : V := (‖j u‖⁻¹ : ℂ) • u
    refine ⟨(⟪v, A v⟫_ℂ).re, v, ?_, rfl⟩
    simp [v, norm_smul, hu]
  have hl : ∀ e ∈ S, ‖R‖⁻¹ ≤ e := by
    rintro e ⟨u, hn, rfl⟩
    have hh := form_reciprocal_resolvent_bound j hj hd A hs hc hA u
    simpa only [hn, mul_one] using hh
  have hbb : BddBelow S := ⟨‖R‖⁻¹, hl⟩
  apply le_antisymm
  · change sInf S ≤ ‖R‖⁻¹
    by_contra! ht
    have hm : 0 < sInf S := (inv_pos.mpr hR).trans ht
    have hu : ∀ u, ‖j u‖ ^ 2 = 1 → sInf S ≤ (⟪u, A u⟫_ℂ).re :=
      fun u hn => csInf_le hbb ⟨u, hn, rfl⟩
    have hb := resolvent_norm_le_of_form_bound j A hc hA hm (form_lower_of_unit j hj A hu)
    change ‖R‖ ≤ (sInf S)⁻¹ at hb
    have hmul := mul_lt_mul_of_pos_right ht hR
    have hmle := mul_le_mul_of_nonneg_right hb hm.le
    rw [inv_mul_cancel₀ hR.ne'] at hmul
    rw [inv_mul_cancel₀ hm.ne'] at hmle
    nlinarith
  · exact le_csInf hne hl

end CoulombAtom

end

end OAI
