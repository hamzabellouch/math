import OAI.Analysis.KadisonKastler.VaryingSequence
import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar

namespace OAI

/-! # The actual norm ultraproduct for the infinitesimal normalizer argument

The null sequences form a closed star ideal in the bounded product. Its
C-star quotient is the norm ultraproduct used in the infinitesimal
normalizer argument.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable (B : ℕ → Type*) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

def NormNullSequence (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B) : Prop :=
  Tendsto (fun j => ‖x j‖) (ω : Filter ℕ) (𝓝 0)

omit [∀ j, Nontrivial (B j)] in
theorem normNullSequence_add (ω : Ultrafilter ℕ) {x y : VaryingBoundedSequence B}
    (hx : NormNullSequence B ω x) (hy : NormNullSequence B ω y) :
    NormNullSequence B ω (x + y) := by
  apply squeeze_zero (fun j => norm_nonneg ((x + y) j)) (fun j => norm_add_le (x j) (y j))
  simpa only [add_zero] using hx.add hy

omit [∀ j, Nontrivial (B j)] in
theorem normNullSequence_mul_left (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B)
    {y : VaryingBoundedSequence B} (hy : NormNullSequence B ω y) :
    NormNullSequence B ω (x * y) := by
  apply squeeze_zero (fun j => norm_nonneg ((x * y) j))
    (fun j => (norm_mul_le (x j) (y j)).trans
      (mul_le_mul_of_nonneg_right (varyingSequence_norm_apply_le x j) (norm_nonneg _)))
  simpa only [mul_zero] using tendsto_const_nhds.mul hy

omit [∀ j, Nontrivial (B j)] in
theorem normNullSequence_mul_right (ω : Ultrafilter ℕ) {x : VaryingBoundedSequence B}
    (hx : NormNullSequence B ω x) (y : VaryingBoundedSequence B) :
    NormNullSequence B ω (x * y) := by
  apply squeeze_zero (fun j => norm_nonneg ((x * y) j))
    (fun j => (norm_mul_le (x j) (y j)).trans
      (mul_le_mul_of_nonneg_left (varyingSequence_norm_apply_le y j) (norm_nonneg _)))
  simpa only [zero_mul] using hx.mul tendsto_const_nhds

theorem isClosed_normNullSequence (ω : Ultrafilter ℕ) :
    IsClosed {x : VaryingBoundedSequence B | NormNullSequence B ω x} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  have hxy : ‖x - y‖ < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hyx
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε / 2) (half_pos hε)] with j hj
  have hyj : ‖y j‖ < ε / 2 := by simpa only [dist_zero_right, norm_norm] using hj
  have hc : ‖x j - y j‖ ≤ ‖x - y‖ := varyingSequence_norm_apply_le (x - y) j
  have ht : ‖x j‖ ≤ ‖x j - y j‖ + ‖y j‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x j - y j) (y j)
  simpa only [dist_zero_right, norm_norm] using
    (lt_of_le_of_lt ht (by linarith only [hc, hxy, hyj]))

def normNullClosedIdeal (ω : Ultrafilter ℕ) :
    CuntzPureness.ClosedStarIdeal (VaryingBoundedSequence B) where
  ideal := TwoSidedIdeal.mk' {x | NormNullSequence B ω x}
    (by
      change NormNullSequence B ω 0
      simpa only [NormNullSequence, lp.coeFn_zero, Pi.zero_apply, norm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0)))
    (normNullSequence_add B ω)
    (by
      intro x hx
      change NormNullSequence B ω (-x)
      change NormNullSequence B ω x at hx
      simpa only [NormNullSequence, lp.coeFn_neg, Pi.neg_apply, norm_neg] using hx)
    (by intro x y hy; exact normNullSequence_mul_left B ω x hy)
    (by intro x y hx; exact normNullSequence_mul_right B ω hx y)
  star_mem := by
    intro x hx
    change NormNullSequence B ω (star x - 0)
    change NormNullSequence B ω (x - 0) at hx
    simpa only [sub_zero, NormNullSequence, lp.coeFn_star, Pi.star_apply, norm_star] using hx
  isClosed := by
    simpa only [TwoSidedIdeal.coe_mk'] using isClosed_normNullSequence B ω

abbrev NormUltraproduct (ω : Ultrafilter ℕ) := (normNullClosedIdeal B ω).Quotient

local instance : PartialOrder (VaryingBoundedSequence B) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (VaryingBoundedSequence B) := CStarAlgebra.spectralOrderedRing _

instance normUltraproductCStarAlgebra (ω : Ultrafilter ℕ) : CStarAlgebra (NormUltraproduct B ω) :=
  inferInstanceAs (CStarAlgebra (normNullClosedIdeal B ω).Quotient)

def normUltraproductMap (ω : Ultrafilter ℕ) :
    VaryingBoundedSequence B →⋆ₐ[ℂ] NormUltraproduct B ω :=
  (normNullClosedIdeal B ω).quotientStarHom

theorem normUltraproductMap_surjective (ω : Ultrafilter ℕ) :
    Function.Surjective (normUltraproductMap B ω) :=
  (normNullClosedIdeal B ω).quotientMap_surjective

theorem normUltraproductMap_eq_zero_iff (ω : Ultrafilter ℕ) (x : VaryingBoundedSequence B) :
    normUltraproductMap B ω x = 0 ↔ NormNullSequence B ω x := by
  change (normNullClosedIdeal B ω).quotientMap x =
    (normNullClosedIdeal B ω).quotientMap 0 ↔ _
  constructor
  · intro h
    have hr := Quotient.exact h
    change NormNullSequence B ω (x - 0) at hr
    simpa only [sub_zero] using hr
  · intro h
    apply Quotient.sound
    change NormNullSequence B ω (x - 0)
    simpa only [sub_zero] using h

instance normUltraproductNontrivial (ω : Ultrafilter ℕ) : Nontrivial (NormUltraproduct B ω) := by
  have h : (1 : NormUltraproduct B ω) ≠ 0 := by
    intro heq
    have hn := (normUltraproductMap_eq_zero_iff B ω 1).mp
      (by simpa only [map_one] using heq)
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ)) (ω : Filter ℕ) (𝓝 0) := by
      change Tendsto (fun j => ‖(1 : B j)‖) (ω : Filter ℕ) (𝓝 0) at hn
      simpa only [norm_one] using hn
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
  exact ⟨⟨1, 0, h⟩⟩

/-- Taking the self-adjoint part supplies actual self-adjoint sequence
representatives for the implementer produced by Sakai's theorem. -/
theorem exists_selfAdjoint_normUltraproduct_lift (ω : Ultrafilter ℕ)
    (a : NormUltraproduct B ω) (ha : IsSelfAdjoint a) :
    ∃ x : VaryingBoundedSequence B, IsSelfAdjoint x ∧ normUltraproductMap B ω x = a := by
  obtain ⟨x, hx⟩ := normUltraproductMap_surjective B ω a
  refine ⟨(1 / 2 : ℂ) • (x + star x), ?_, ?_⟩
  · exact (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self x)
  · rw [map_smul, map_add, map_star, hx, ha.star_eq, ← two_smul ℂ a, smul_smul]
    norm_num

end

end KadisonKastler

end OAI
