import OAI.Analysis.Mahler.HorizontalForms

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedge_smul_left (c : ℂ) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (c • a) b = c • wedge a b := by
  ext v
  change (LinearMap.mul' ℝ ℂ) ((c • a).domCoprod b v) =
    c * (LinearMap.mul' ℝ ℂ) (a.domCoprod b v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply,
      smul_eq_mul]
    simp only [Units.smul_def, TensorProduct.smul_tmul']
    simp only [LinearMap.mul'_apply]
    ring

lemma wedge_smul_right (c : ℂ) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge a (c • b) = c • wedge a b := by
  ext v
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod (c • b) v) =
    c * (LinearMap.mul' ℝ ℂ) (a.domCoprod b v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply,
      smul_eq_mul]
    simp only [Units.smul_def, TensorProduct.smul_tmul']
    simp only [LinearMap.mul'_apply]
    ring

lemma wedgePower_smul (c : ℂ) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (c • a) k = c ^ k • wedgePower a k := by
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = c ^ 0 * 1
    simp
  | succ k ih =>
    change wedge (c • a) (wedgePower (c • a) k) = c ^ (k + 1) • wedge a (wedgePower a k)
    simp only [ih, wedge_smul_left, wedge_smul_right, smul_smul]
    rw [pow_succ]

lemma wedge_compLinearMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).compLinearMap L = wedge (a.compLinearMap L) (b.compLinearMap L) := by
  ext v
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod b (fun i => L (v i))) =
    (LinearMap.mul' ℝ ℂ) ((a.compLinearMap L).domCoprod (b.compLinearMap L) v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply]

lemma wedgePower_compLinearMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    (wedgePower a k).compLinearMap L = wedgePower (a.compLinearMap L) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (wedge a (wedgePower a k)).compLinearMap L = _
    rw [wedge_compLinearMap, ih]
    rfl

end Mahler

end OAI
