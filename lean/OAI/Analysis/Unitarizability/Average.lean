import OAI.Analysis.Unitarizability.Regular
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace OAI

/-! Finite-average identities for contracting averages in Hilbert spaces. -/
noncomputable section
namespace Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite Hilbert-space variance identity, without normalization. -/
theorem sum_pairwise_sq (S : Finset I) (v : I → H) :
    ∑ i ∈ S, ∑ j ∈ S, ‖v i - v j‖ ^ 2 =
      2 * (S.card : ℝ) * (∑ i ∈ S, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ S, v i‖ ^ 2 := by
  have hs : (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) =
      ‖∑ i ∈ S, v i‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    simp only [sum_inner, inner_sum, map_sum]
    exact Finset.sum_comm
  simp_rw [@norm_sub_sq ℂ H]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  change _ - 2 * (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) + _ = _
  rw [hs]
  ring

omit [InnerProductSpace ℂ H] in
/-- A chosen pair contributes at most the total squared defect. -/
theorem pairwise_sq_le_sum (S : Finset I) (v : I → H) {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) :
    ‖v i - v j‖ ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S, ‖v a - v b‖ ^ 2 := by
  exact (Finset.single_le_sum (fun b _ => sq_nonneg ‖v i - v b‖) hj).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s := S) (fun b _ => sq_nonneg ‖v a - v b‖)) hi)

variable {G : Type*} [Group G]
/-- Defect in a finite sum of right translations of a unit vector. -/
theorem regular_sum_variance (S : Finset G) (ξ : ScalarL2 G) (hξ : ‖ξ‖ = 1) :
    ∑ g ∈ S, ∑ h ∈ S, ‖rightRegular g ξ - rightRegular h ξ‖ ^ 2 =
      2 * ((S.card : ℝ) ^ 2 - ‖∑ g ∈ S, rightRegular g ξ‖ ^ 2) := by
  rw [sum_pairwise_sq]
  simp only [rightRegular_norm_map, hξ, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- A norm-one vector witnessing any strict lower bound for an operator norm. -/
theorem exists_unit_near_opNorm (A : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (hA : c < ‖A‖) : ∃ ξ : H, ‖ξ‖ = 1 ∧ c < ‖A ξ‖ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hA) (ContinuousLinearMap.opNorm_le_of_unit_norm hc h)

/-- The norm-one-average hypothesis yields simultaneous almost invariance. -/
theorem almost_invariant_of_sum_norm (S : Finset G) (h1 : (1 : G) ∈ S)
    (hS : ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ScalarL2 G, ‖ξ‖ = 1 ∧ ∀ g ∈ S, ‖rightRegular g ξ - ξ‖ < ε := by
  have hd : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
  let c := Real.sqrt (max 0 ((S.card : ℝ)^2 - ε^2/2))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2 = max 0 ((S.card : ℝ)^2 - ε^2/2) :=
    Real.sq_sqrt (le_max_left _ _)
  have hcd : c < (S.card : ℝ) := by
    have hm : max 0 ((S.card : ℝ)^2 - ε^2/2) < (S.card : ℝ)^2 :=
      max_lt (sq_pos_of_pos hd) (by nlinarith [sq_pos_of_pos hε])
    nlinarith
  obtain ⟨ξ, hξ, hclose⟩ := exists_unit_near_opNorm
    (∑ g ∈ S, rightRegular g) hc (by rwa [hS])
  have hclose' : c < ‖∑ g ∈ S, rightRegular g ξ‖ := by
    simpa only [_root_.sum_apply] using hclose
  have hdefect : 2 * ((S.card : ℝ)^2 - ‖∑ g ∈ S, rightRegular g ξ‖^2) < ε^2 := by
    have hm := le_max_right 0 ((S.card : ℝ)^2 - ε^2/2)
    nlinarith [norm_nonneg (∑ g ∈ S, rightRegular g ξ)]
  refine ⟨ξ, hξ, fun g hg => ?_⟩
  have hp := pairwise_sq_le_sum S (fun g => rightRegular g ξ) hg h1
  rw [regular_sum_variance S ξ hξ] at hp
  have he : rightRegular (1 : G) ξ = ξ := by ext x; simp
  rw [he] at hp
  nlinarith [norm_nonneg (rightRegular g ξ - ξ)]

end Dixmier

end

end OAI
