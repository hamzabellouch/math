import Mathlib
import OAI.Analysis.WeakInfiniteness.Intertwining
import OAI.Analysis.WeakInfiniteness.SeparationScalarBounds

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma initial_mul_cfc (X : B) (f : ℝ → ℝ) (hf : Continuous f) :
    star (X*cfc f (star X*X))*(X*cfc f (star X*X))=
      cfc (fun s => s*(f s)^2) (star X*X) := by
  have hF : IsSelfAdjoint (cfc f (star X*X)) := cfc_predicate _ _
  have hcomm : Commute (cfc f (star X*X)) (star X*X) := (Commute.refl _).cfc_real f
  rw [star_mul,hF.star_eq]
  calc
    _=cfc f (star X*X)*(star X*X)*cfc f (star X*X) := by simp only [mul_assoc]
    _=(star X*X)*cfc f (star X*X)*cfc f (star X*X) := by rw [hcomm.eq]
    _=cfc (fun s : ℝ => s*f s*f s) (star X*X) := by
      rw [cfc_mul (fun s : ℝ => s*f s) f _ (continuous_id.mul hf).continuousOn hf.continuousOn,
        cfc_mul (fun s : ℝ => s) f _ continuous_id.continuousOn hf.continuousOn,
        cfc_id' ℝ (star X*X) (IsSelfAdjoint.star_mul_self X)]
    _=_ := by congr 1; ext s; ring

lemma norm_mul_cfc_initial_le (X : B) (f : ℝ → ℝ) (hf : Continuous f)
    {c : ℝ} (hc : 0 ≤ c)
    (hscalar : ∀ s ∈ spectrum ℝ (star X*X),s*(f s)^2 ≤ c^2) :
    ‖X*cfc f (star X*X)‖ ≤ c := by
  have hn : ‖cfc (fun s => s*(f s)^2) (star X*X)‖ ≤ c^2 := by
    apply norm_cfc_le (sq_nonneg c)
    intro s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs) (sq_nonneg _))]
    exact hscalar s hs
  rw [← initial_mul_cfc X f hf,CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (X*cfc f (star X*X))]

omit [PartialOrder B] [StarOrderedRing B] in
lemma sandwich_cfc_initial (X : B) (f : ℝ → ℝ) (hf : Continuous f) :
    X*cfc f (star X*X)*star X=cfc (fun s => s*f s) (X*star X) := by
  rw [← cfc_star_mul_intertwine X f hf,mul_assoc]
  have hcomm : Commute (cfc f (X*star X)) (X*star X) := (Commute.refl _).cfc_real f
  rw [hcomm.eq]
  rw [cfc_mul (fun s : ℝ => s) f _ continuous_id.continuousOn hf.continuousOn,
    cfc_id' ℝ (X*star X) (IsSelfAdjoint.mul_star_self X)]

omit [PartialOrder B] [StarOrderedRing B] in
lemma cfc_real_mul_three (a : B) (_ha : IsSelfAdjoint a)
    (f g k : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    cfc f a*cfc g a*cfc k a=cfc (fun s => f s*g s*k s) a := by
  rw [cfc_mul (fun s => f s*g s) k a (hf.mul hg).continuousOn hk.continuousOn,
    cfc_mul f g a hf.continuousOn hg.continuousOn]

omit [PartialOrder B] [StarOrderedRing B] in
lemma norm_separationR (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationR l) (star X*X)‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro s _
  rw [Real.norm_eq_abs,abs_of_nonneg (separationR_nonneg hl.le s)]
  exact separationR_le_one hl s

lemma norm_separation_polar (X : B) {l : ℝ} (hl : 0 < l) :
    ‖X*cfc (separationV l) (star X*X)‖ ≤ 1 := by
  apply norm_mul_cfc_initial_le X _ (continuous_separationV hl) (by norm_num)
  intro s hs
  simpa only [one_pow] using separation_sV_sq_le_one hl
    (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)

lemma norm_separation_low (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationL l) (X*star X)*X*cfc (separationL l) (star X*X)‖ ≤ 8*l := by
  rw [cfc_star_mul_intertwine X _ (continuous_separationL l),mul_assoc,
    ← cfc_mul _ _ _ (continuous_separationL l).continuousOn (continuous_separationL l).continuousOn]
  apply norm_mul_cfc_initial_le X _ ((continuous_separationL l).mul (continuous_separationL l)) (by positivity)
  intro s hs
  have h := separation_low_square_bound hl (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)
  change s * (separationL l s * separationL l s)^2 ≤ (8*l)^2
  nlinarith

lemma norm_separation_mixedR (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationL l) (X*star X)*X*cfc (separationR l) (star X*X)‖ ≤ 3*l := by
  rw [cfc_star_mul_intertwine X _ (continuous_separationL l),mul_assoc,
    ← cfc_mul _ _ _ (continuous_separationL l).continuousOn (continuous_separationR hl).continuousOn]
  apply norm_mul_cfc_initial_le X _ ((continuous_separationL l).mul (continuous_separationR hl)) (by positivity)
  intro s hs
  have h := separation_mixed_R_square_bound hl (spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs)
  change s * (separationL l s * separationR l s)^2 ≤ (3*l)^2
  nlinarith

lemma norm_separation_mixedV (X : B) {l : ℝ} (hl : 0 < l) :
    ‖cfc (separationV l) (star X*X)*(star X*X)*cfc (separationL l) (star X*X)‖ ≤ 3*l := by
  have he : cfc (separationV l) (star X*X)*(star X*X)*cfc (separationL l) (star X*X)=
      cfc (fun s => s*separationV l s*separationL l s) (star X*X) := by
    rw [(Commute.refl (star X*X)).cfc_real (separationV l) |>.eq]
    conv_lhs => lhs; lhs; rw [← cfc_id' ℝ (star X*X) (IsSelfAdjoint.star_mul_self X)]
    exact cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) (fun s => s) _ _ continuous_id
      (continuous_separationV hl) (continuous_separationL l)
  rw [he]
  apply norm_cfc_le (by positivity)
  intro s hs
  have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg X) hs
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg hs0 (separationV_nonneg hl s))
    (separationL_bounds l s).1)]
  have h := separation_mixed_V_square_bound hl hs0
  nlinarith [mul_nonneg (mul_nonneg hs0 (separationV_nonneg hl s)) (separationL_bounds l s).1]

end

end

end WeakPureInfiniteness
end

end OAI
