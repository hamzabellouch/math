import OAI.Analysis.TracialSplitting.StateExtension

namespace OAI

universe uA uB uE uF uH uK uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

namespace UnitalTomsWinter

variable {H : Type uH} {K : Type uK} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev SpatialHilbert (H : Type uH) (K : Type uK) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (H ⊗[ℂ] K)

def spatialTensorOp (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H K :=
  (TensorProduct.mapL S T).completion

@[simp] lemma spatialTensorOp_coe (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    spatialTensorOp S T x = (TensorProduct.mapL S T x : SpatialHilbert H K) := by
  exact (TensorProduct.mapL S T).completion_apply_coe x

lemma spatialTensorOp_ext {S T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K}
    (h : ∀ x : H, ∀ y : K, S (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simpa [coe_add] using congrArg₂ (· + ·) hx hy

@[simp] lemma spatialTensorOp_zero_left (T : K →L[ℂ] K) : spatialTensorOp (0 : H →L[ℂ] H) T = 0 := by
  apply spatialTensorOp_ext; intro x y; simp

@[simp] lemma spatialTensorOp_zero_right (S : H →L[ℂ] H) : spatialTensorOp S (0 : K →L[ℂ] K) = 0 := by
  apply spatialTensorOp_ext; intro x y; simp

lemma spatialTensorOp_add_left (S₁ S₂ : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (S₁+S₂) T = spatialTensorOp S₁ T + spatialTensorOp S₂ T := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.add_tmul, coe_add]

lemma spatialTensorOp_add_right (S : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp S (T₁+T₂) = spatialTensorOp S T₁ + spatialTensorOp S T₂ := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.tmul_add, coe_add]

lemma spatialTensorOp_smul_left (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (c • S) T = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, smul_apply]
  rw [← TensorProduct.smul_tmul', coe_smul]

lemma spatialTensorOp_smul_right (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp S (c • T) = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp

lemma spatialTensorOp_mul (S₁ S₂ : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp (S₁*S₂) (T₁*T₂) = spatialTensorOp S₁ T₁ * spatialTensorOp S₂ T₂ := by
  apply spatialTensorOp_ext; intro x y; simp

private lemma completion_opNorm_le {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z => simpa using f.le_opNorm z

lemma spatialTensorOp_norm_le (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖spatialTensorOp S T‖ ≤ ‖S‖ * ‖T‖ :=
  (completion_opNorm_le (TensorProduct.mapL S T)).trans (TensorProduct.norm_mapL_le S T)

variable [CompleteSpace H] [CompleteSpace K]

lemma spatialTensorOp_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (star S) (star T) = star (spatialTensorOp S T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
    | tmul x₁ x₂ =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
      | tmul y₁ y₂ => simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

end UnitalTomsWinter

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorOp_one : spatialTensorOp (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply spatialTensorOp_ext
  intro x y
  simp

def spatialLeftHom : A →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun a := spatialTensorOp (α a) 1
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_left]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_left,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,← spatialTensorOp_star,star_one]

def spatialRightHom : B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun b := spatialTensorOp 1 (β b)
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_right]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_right,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' b := by rw [map_star,← spatialTensorOp_star,star_one]

lemma spatialLeftRight_commute (a : A) (b : B) :
    Commute (spatialLeftHom (K := K) α a) (spatialRightHom (H := H) β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) =
    spatialTensorOp 1 (β b) * spatialTensorOp (α a) 1
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul]
  simp

lemma spatialRightHom_injective [Nontrivial H] (hβ : Function.Injective β) :
    Function.Injective (spatialRightHom (H := H) β) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  apply (map_eq_zero_iff β hβ).mp
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x,hx⟩ := exists_ne (0 : H)
  have hz := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    ‖T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)‖) hb
  simp only [zero_apply,norm_zero] at hz
  have hn : ‖x‖ * ‖β b y‖=0 := by simpa [spatialRightHom] using hz
  exact norm_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left (norm_ne_zero_iff.mpr hx))

def spatialStarTensorHom :
    A ⊗[ℂ] B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  commutingStarTensorHom (N := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialLeftHom (K := K) α) (spatialRightHom (H := H) β) (spatialLeftRight_commute α β)

lemma spatialStarTensorHom_tmul (a : A) (b : B) :
    spatialStarTensorHom α β (a ⊗ₜ[ℂ] b)=spatialTensorOp (α a) (β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) = _
  rw [← spatialTensorOp_mul,mul_one,one_mul]

end Pureness

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma spatial_relation_coefficients_zero
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {ι : Type uι} (b : ι → B) (hb : LinearIndependent ℂ b)
    (s : Finset ι) (a : ι → A)
    (hz : spatialStarTensorHom α β (∑ i ∈ s, a i ⊗ₜ[ℂ] b i) = 0) :
    ∀ i ∈ s, a i = 0 := by
  classical
  have hc (x x' : H) : ∑ i ∈ s, ⟪x', α (a i) x⟫_ℂ • b i = 0 := by
    apply (map_eq_zero_iff β hβ).mp
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro y'
    have he := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
      ⟪((x' ⊗ₜ[ℂ] y' : H ⊗[ℂ] K) : SpatialHilbert H K), T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)⟫_ℂ) hz
    simpa only [map_sum, map_smul, spatialStarTensorHom_tmul,
      sum_apply, smul_apply,
      zero_apply, inner_zero_right, inner_sum, inner_smul_right,
      spatialTensorOp_coe, TensorProduct.mapL_tmul, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul] using he
  intro i hi
  apply (map_eq_zero_iff α hα).mp
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro x'
  rw [zero_apply, inner_zero_right]
  exact (linearIndependent_iff'.mp hb) s _ (hc x x') i hi

theorem spatialStarTensorHom_injective_of_faithful
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (spatialStarTensorHom α β) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ B
  obtain ⟨a, rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have ha := spatial_relation_coefficients_zero α β hα hβ b b.linearIndependent a.support a hz
  change ∑ i ∈ a.support, a i ⊗ₜ[ℂ] b i = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [ha i hi, TensorProduct.zero_tmul]

end Pureness

end

end

end

end

end

end

end

end

end

end OAI
