import OAI.Probability.SignedSweeps.SubsetInclusion
import OAI.Probability.SignedSweeps.SwitchAverages

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (A : Type*) [DecidableEq A]

def realSiteRepresentation : Representation ℝ (Equiv.Perm A) (A → ℝ) where
  toFun g := {
    toFun p x := p (g⁻¹ x)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext p x; rfl
  map_mul' := by intros; ext p x; rfl

def subsetRepresentation : Representation ℝ (Equiv.Perm A) (Finset A → ℝ) where
  toFun (g : Equiv.Perm A) := {
    toFun M T := M (T.image (g⁻¹ : Equiv.Perm A))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext M T; simp
  map_mul' := by intros; ext M T; simp [Finset.image_image, Function.comp_def]

lemma fairAction_site (a b : A) (p : A → ℝ) :
    fairAction (realSiteRepresentation A) (Equiv.swap a b) p = fairSwapWeights a b p := by
  ext x
  simp only [fairAction_apply, realSiteRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, Equiv.swap_inv,
    smul_eq_mul, fairSwapWeights]
  ring

lemma fairAction_subset (a b : A) (M : Finset A → ℝ) :
    fairAction (subsetRepresentation A) (Equiv.swap a b) M = fairSwapInclusion a b M := by
  ext T
  simp only [fairAction_apply, subsetRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, Equiv.swap_inv,
    smul_eq_mul, fairSwapInclusion]
  ring

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [DecidableEq A]

lemma switch_product_inclusion_bound (L : List (A × A)) (M : Finset A → ℝ) (p : A → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) :
    (∀ x, 0 ≤ (L.map (fun e => fairAction (realSiteRepresentation A) (Equiv.swap e.1 e.2))).prod p x) ∧
      (∀ T, (L.map (fun e => fairAction (subsetRepresentation A) (Equiv.swap e.1 e.2))).prod M T ≤
        ∏ x ∈ T, (L.map (fun e => fairAction (realSiteRepresentation A) (Equiv.swap e.1 e.2))).prod p x) := by
  induction L with
  | nil => simpa using And.intro hp hM
  | cons e L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      fairAction_site, fairAction_subset]
    exact ⟨fairSwapWeights_nonneg e.1 e.2 ih.1,
      fairSwapInclusion_bound e.1 e.2 _ _ ih.1 ih.2⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma coordinate_inclusion_bound {d : ℕ} (i : Fin d) (M : Finset (Fin (2 ^ d)) → ℝ)
    (p : Fin (2 ^ d) → ℝ) (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) :
    (∀ x, 0 ≤ realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
      (coordinateSubgroup d i).subtype) p x) ∧
      (∀ T, realGroupAverage ((subsetRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype) M T ≤
        ∏ x ∈ T, realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
          (coordinateSubgroup d i).subtype) p x) := by
  rw [coordinate_real_average_as_switches, coordinate_real_average_as_switches]
  simpa only [List.map_ofFn, Function.comp_def] using
    switch_product_inclusion_bound (List.ofFn (fun x : Fin (2 ^ d) => (x, flipPermutation d i x))) M p hp hM

def realSiteSweep (d : ℕ) : (Fin (2 ^ d) → ℝ) →ₗ[ℝ] (Fin (2 ^ d) → ℝ) :=
  ((List.ofFn (fun i : Fin d => realGroupAverage
    ((realSiteRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).reverse).prod

def subsetSweep (d : ℕ) : (Finset (Fin (2 ^ d)) → ℝ) →ₗ[ℝ] (Finset (Fin (2 ^ d)) → ℝ) :=
  ((List.ofFn (fun i : Fin d => realGroupAverage
    ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).reverse).prod

lemma subsetSweep_inclusion_bound {d : ℕ} (M : Finset (Fin (2 ^ d)) → ℝ)
    (p : Fin (2 ^ d) → ℝ) (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) :
    (∀ x, 0 ≤ realSiteSweep d p x) ∧
      (∀ T, subsetSweep d M T ≤ ∏ x ∈ T, realSiteSweep d p x) := by
  have hh (L : List (Fin d)) :
      (∀ x, 0 ≤ ((L.map fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype)).prod p) x) ∧
      (∀ T, ((L.map fun i => realGroupAverage ((subsetRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype)).prod M) T ≤
          ∏ x ∈ T, ((L.map fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
            (coordinateSubgroup d i).subtype)).prod p) x) := by
    induction L with
    | nil => simpa using And.intro hp hM
    | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact coordinate_inclusion_bound i _ _ ih.1 ih.2
  simpa [realSiteSweep, subsetSweep, List.ofFn_eq_map] using hh (List.finRange d).reverse

lemma realSiteAverage_complexify {n : ℕ} (H : Subgroup (SymmetricGroup n)) (p : Fin n → ℝ) (x : Fin n) :
    ((realGroupAverage ((realSiteRepresentation (Fin n)).comp H.subtype) p x : ℝ) : ℂ) =
      groupAverage ((oneCardRepresentation n).comp H.subtype) (fun y => (p y : ℂ)) x := by
  classical
  simp only [realGroupAverage, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
    realSiteRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, oneCardRepresentation_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast]

lemma realSiteSweep_complexify {d : ℕ} (p : Fin (2 ^ d) → ℝ) (x : Fin (2 ^ d)) :
    ((realSiteSweep d p x : ℝ) : ℂ) = oneCardSweep d (fun y => (p y : ℂ)) x := by
  have hh (L : List (Fin d)) (p : Fin (2 ^ d) → ℝ) (x : Fin (2 ^ d)) :
      (((L.map (fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype))).prod p x : ℝ) : ℂ) =
      (L.map (fun i => groupAverage ((oneCardRepresentation (2 ^ d)).comp
        (coordinateSubgroup d i).subtype))).prod (fun y => (p y : ℂ)) x := by
    induction L generalizing p x with
    | nil => rfl
    | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [realSiteAverage_complexify]
      rw [show (fun y => (((L.map (fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype))).prod p y : ℝ) : ℂ)) =
        (L.map (fun i => groupAverage ((oneCardRepresentation (2 ^ d)).comp
        (coordinateSubgroup d i).subtype))).prod (fun y => (p y : ℂ)) from funext (fun y => ih p y)]
  simpa [realSiteSweep, oneCardSweep, List.ofFn_eq_map] using hh (List.finRange d).reverse p x

lemma realSiteSweep_uniform {d : ℕ} (p : Fin (2 ^ d) → ℝ) (x : Fin (2 ^ d)) :
    realSiteSweep d p x = (∑ y, p y) / (2 ^ d : ℕ) := by
  apply Complex.ofReal_injective
  rw [realSiteSweep_complexify, oneCardSweep_uniform]
  simp only [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [DecidableEq A]

lemma subset_indicator_product (S T : Finset A) :
    (if T ⊆ S then (1 : ℝ) else 0) = ∏ x ∈ T, if x ∈ S then (1 : ℝ) else 0 := by
  by_cases h : T ⊆ S
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro x hx
    exact ite_eq_left (h hx)
  · rw [ite_eq_right h]
    obtain ⟨x, hx, hxn⟩ := Finset.not_subset.mp h
    symm
    exact Finset.prod_eq_zero hx (ite_eq_right hxn)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma subsetSweep_upper_inclusion (d : ℕ) (S T : Finset (Fin (2 ^ d))) :
    subsetSweep d (fun U => if U ⊆ S then 1 else 0) T ≤
      ((S.card : ℝ) / (2 ^ d : ℕ)) ^ T.card := by
  have hp (x : Fin (2 ^ d)) : (0 : ℝ) ≤ if x ∈ S then 1 else 0 := by split_ifs <;> norm_num
  have h := (subsetSweep_inclusion_bound (fun U => if U ⊆ S then 1 else 0)
    (fun x => if x ∈ S then 1 else 0) hp (fun U => (subset_indicator_product S U).le)).2 T
  simp only [realSiteSweep_uniform] at h
  simpa [div_pow] using h

end SignedSweeps
end

end OAI
