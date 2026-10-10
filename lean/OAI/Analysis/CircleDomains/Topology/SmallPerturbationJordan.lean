import OAI.Analysis.CircleDomains.Topology.SmallPerturbationHomeomorph
import Mathlib.Analysis.Normed.MulAction
import OAI.Analysis.CircleDomains.Topology.PositiveJordanIsotopy

namespace OAI

/-! Small smooth ambient perturbations preserve regular Jordan curves. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma regularJordanParametrization_smallPerturbation
    {V : ℂ → ℂ} {L : ℝ≥0} (hV : LipschitzWith L V) (hL : L < 1)
    (hs : ContDiff ℝ ∞ V) {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    RegularJordanParametrization (H.trans (smallPerturbationHomeomorph V hV hL))
      (smallPerturbationHomeomorph V hV hL ∘ γ) := by
  let T := smallPerturbationHomeomorph V hV hL
  have hT : ContDiff ℝ ∞ T := smallPerturbationHomeomorph_smooth hV hL hs
  refine ⟨hT.comp hγ.smooth, ?_, ?_, ?_, ?_⟩
  · intro t
    exact congrArg T (hγ.periodic t)
  · intro s hs t ht he
    exact hγ.injective hs ht (T.injective he)
  · intro t he
    have hd := (hT.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t
      (hγ.smooth.differentiable (by simp) t).hasDerivAt
    have hi : Injective (fderiv ℝ T (γ t)) :=
      id_add_fderiv_injective hV hL (hs.differentiable (by simp) (γ t))
    have hh : fderiv ℝ T (γ t) (deriv γ t) = 0 := by
      rw [← hd.deriv]
      exact he
    exact hγ.regular t (hi (hh.trans (map_zero _).symm))
  · rw [jordanInterior_trans, ← T.image_frontier, ← hγ.boundary, image_image]
    rfl

 def scaledPerturbationHomeomorph (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (ρ : Icc (0 : ℝ) 1) : ℂ ≃ₜ ℂ :=
  smallPerturbationHomeomorph (fun z => (ρ : ℝ) • V z) ((lipschitzWith_smul (ρ : ℝ)).comp hV) (by
    have hr : ‖(ρ : ℝ)‖₊ ≤ 1 := by
      change ‖(ρ : ℝ)‖ ≤ (1 : ℝ)
      simpa only [Real.norm_eq_abs, abs_of_nonneg ρ.property.1] using ρ.property.2
    exact (mul_le_of_le_one_left (by positivity) hr).trans_lt hL)

@[simp] lemma scaledPerturbationHomeomorph_apply (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) (ρ : Icc (0 : ℝ) 1) (z : ℂ) :
    scaledPerturbationHomeomorph V hV hL ρ z = z + (ρ : ℝ) • V z := rfl

lemma scaledPerturbationHomeomorph_zero (V : ℂ → ℂ) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hL : L < 1) :
    scaledPerturbationHomeomorph V hV hL ⟨0, by norm_num⟩ = Homeomorph.refl ℂ := by
  ext z
  simp

lemma positiveJordanParametrization_smallPerturbation
    {V : ℂ → ℂ} {L : ℝ≥0} (hV : LipschitzWith L V) (hL : L < 1)
    (hs : ContDiff ℝ ∞ V) {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : PositiveJordanParametrization H γ) (ρ : Icc (0 : ℝ) 1) :
    PositiveJordanParametrization (H.trans (scaledPerturbationHomeomorph V hV hL ρ))
      (scaledPerturbationHomeomorph V hV hL ρ ∘ γ) := by
  refine positiveJordanParametrization_transport (scaledPerturbationHomeomorph V hV hL)
    ?_ ⟨0, by norm_num⟩ (scaledPerturbationHomeomorph_zero V hV hL) hγ ρ ?_
  · exact continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul (hV.continuous.comp continuous_snd))
  · exact regularJordanParametrization_smallPerturbation
      (V := fun z => (ρ : ℝ) • V z) _ _ ((contDiff_const (c := (ρ : ℝ))).smul hs) hγ.toRegular

end CircleDomainRigidity

end

end OAI
