import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.Absorption

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
section
open scoped CStarAlgebra ComplexOrder

open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]


@[simp] lemma map_coe (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    map T S (x : Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
  simp [map]

@[ext] lemma ext {T S : Hilbert H K →L[ℂ] Hilbert H K}
    (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous S.continuous
  | ih x => exact h x

lemma map_add_left (T U : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (T + U) S = map T S + map U S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_left, ← Completion.coe_add]

lemma map_add_right (T : H →L[ℂ] H) (S U : K →L[ℂ] K) :
    map T (S + U) = map T S + map T U := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_right, ← Completion.coe_add]

lemma map_smul_left (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (z • T) S = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_left, ← Completion.coe_smul]

lemma map_smul_right (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map T (z • S) = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_right, ← Completion.coe_smul]

lemma map_mul (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
    map (T * U) (S * V) = map T S * map U V := by
  apply ext
  intro x
  simp only [mul_apply_eq_comp, map_coe, TensorProduct.mapL_mul]

@[simp] lemma map_one : map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply ext
  intro x
  simp [show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
    show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]

variable [CompleteSpace H] [CompleteSpace K]

lemma map_inner_algebraic (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (x y : H ⊗[ℂ] K) :
    ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
      ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
    | tmul c d =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma map_inner (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : Hilbert H K) :
    ⟪map (star T) (star S) x, y⟫_ℂ = ⟪x, map T S y⟫_ℂ := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y => simpa using map_inner_algebraic T S x y

lemma map_star (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (star T) (star S) = star (map T S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [map_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]


lemma left_right_commute (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    Commute (left (K := K) T) (right (H := H) S) := by
  change map T 1 * map 1 S = map 1 S * map T 1
  rw [← map_mul, ← map_mul]
  simp

end KirchbergRordam.Spatial

end
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]


attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK
variable {A B}
lemma RepresentationPair.commute (ρ : RepresentationPair A B) (a : A) (b : B) :
    Commute (ρ.left a) (ρ.right b) :=
  Spatial.left_right_commute _ _


end KirchbergRordam.MinTensor
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
local instance : Ring (A ⊗[ℂ] B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)

lemma bounded : BddAbove (Set.range (fun ρ : Option (RepresentationPair A B) =>
    (spatialIndex ρ).toSeminorm)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨C,hC⟩ := MaxTensor.bounded_at x
  exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
lemma seminorm_apply (x : A ⊗[ℂ] B) :
    seminorm x=⨆ ρ : Option (RepresentationPair A B), (spatialIndex ρ).toSeminorm x :=
  Seminorm.iSup_apply bounded
lemma le_seminorm (ρ : Option (RepresentationPair A B)) (x : A ⊗[ℂ] B) :
    (spatialIndex ρ).toSeminorm x ≤ seminorm x := by
  rw [seminorm_apply]
  apply le_ciSup _ ρ
  obtain ⟨C,hC⟩ := MaxTensor.bounded_at x
  exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
lemma seminorm_le {x : A ⊗[ℂ] B} {C : ℝ}
    (h : ∀ ρ : Option (RepresentationPair A B), (spatialIndex ρ).toSeminorm x ≤ C) :
    seminorm x ≤ C := by
  rw [seminorm_apply]
  exact ciSup_le h
lemma seminorm_mul_le (x y : A ⊗[ℂ] B) :
    @LE.le ℝ Real.instLE
      (seminorm (@Mul.mul (A ⊗[ℂ] B)
        (_root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)).toMul x y))
      (@Mul.mul ℝ Real.instMul (seminorm x) (seminorm y)) := by
  apply seminorm_le
  intro ρ
  exact ((spatialIndex ρ).mul_le x y).trans (mul_le_mul (le_seminorm ρ x)
    (le_seminorm ρ y) (apply_nonneg _ _) (apply_nonneg _ _))
lemma seminorm_star (x : A ⊗[ℂ] B) : seminorm (star x)=seminorm x := by
  rw [seminorm_apply,seminorm_apply]
  congr 1
  funext ρ
  exact (spatialIndex ρ).star_eq x
lemma seminorm_cstar (x : A ⊗[ℂ] B) :
    seminorm (star x*x)=seminorm x * seminorm x := by
  apply le_antisymm
  · calc
      seminorm (star x * x) ≤ seminorm (star x) * seminorm x := seminorm_mul_le (star x) x
      _ = seminorm x * seminorm x := by rw [seminorm_star]
  · have h : seminorm x ≤ Real.sqrt (seminorm (star x*x)) := by
      apply seminorm_le
      intro ρ
      apply (Real.le_sqrt (apply_nonneg _ _) (apply_nonneg _ _)).mpr
      simpa only [← (spatialIndex ρ).cstar_eq x,pow_two] using le_seminorm ρ (star x*x)
    have := mul_self_le_mul_self (apply_nonneg seminorm x) h
    rwa [Real.mul_self_sqrt (apply_nonneg seminorm _)] at this
lemma seminorm_tmul_le (a : A) (b : B) : seminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ :=
  seminorm_le fun ρ => (spatialIndex ρ).tmul_le a b
lemma seminorm_le_maximal : (seminorm : Seminorm ℂ (A ⊗[ℂ] B)) ≤ MaxTensor.seminorm :=
  fun x => seminorm_le fun ρ => MaxTensor.le_seminorm (spatialIndex ρ) x


theorem exists_spatial_crossSeminorm (A B : Type u) [CStarAlgebra A] [CStarAlgebra B] :
    ∃ p : MaxTensor.CrossSeminorm A B, p.toSeminorm=seminorm ∧
      p.toSeminorm ≤ MaxTensor.seminorm := by
  exact ⟨{toSeminorm := seminorm
          mul_le := seminorm_mul_le
          star_eq := seminorm_star
          cstar_eq := seminorm_cstar
          tmul_le := seminorm_tmul_le},rfl,seminorm_le_maximal⟩
end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

variable {A B}
instance : StarModule ℂ (Raw A B) := TensorProduct.instStarModule

def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)


instance : NormedAlgebra ℂ (Raw A B) where
  norm_smul_le z x := (map_smul_eq_mul seminorm z x).le
instance : NormedStarGroup (Raw A B) where
  norm_star_le x := (seminorm_star x).le
@[simp] lemma norm_raw (x : Raw A B) : ‖x‖ = seminorm x := rfl


instance : CStarRing (Algebra A B) where
  norm_mul_self_le x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simp only [StarCompletion.star_coe, ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe, norm_raw]
      exact (seminorm_cstar x).ge
instance : CStarAlgebra (Algebra A B) where

def of : Raw A B →⋆ₐ[ℂ] Algebra A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' x := (StarCompletion.star_coe _ x).symm
@[simp] lemma norm_of (x : Raw A B) : ‖of x‖ = seminorm x :=
  UniformSpace.Completion.norm_coe x
lemma denseRange_of : DenseRange (of (A := A) (B := B)) :=
  UniformSpace.Completion.denseRange_coe

def includeLeft : A →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeLeft
  map_star' a := by simp })

def includeRight : B →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeRight
  map_star' b := by simp })
lemma legs_commute (a : A) (b : B) :
    Commute (includeLeft (B := B) a) (includeRight (A := A) b) := by
  change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) =
    of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) * of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


def spatialRaw (ρ : RepresentationPair A B) :
    Raw A B →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  (MaxTensor.liftRaw (A := A) (B := B)
    (C := (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K))
    ρ.left ρ.right ρ.commute).comp rawEquiv.symm.toStarAlgHom
lemma norm_spatialRaw_le (ρ : RepresentationPair A B) (x : Raw A B) :
    ‖spatialRaw ρ x‖ ≤ ‖x‖ :=
  le_seminorm (some ρ) x
lemma lipschitz_spatialRaw (ρ : RepresentationPair A B) : LipschitzWith 1 (spatialRaw ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
  exact norm_spatialRaw_le ρ (x-y)
lemma continuous_spatialRaw (ρ : RepresentationPair A B) : Continuous (spatialRaw ρ) :=
  (lipschitz_spatialRaw ρ).continuous
private def extendHom {C : Type*} [NormedRing C] [NormedAlgebra ℂ C]
    [StarRing C] [NormedStarGroup C] [CompleteSpace C]
    (f : Raw A B →⋆ₐ[ℂ] C) (hf : Continuous f) : Algebra A B →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom f.toRingHom hf
  commutes' z := by
    change UniformSpace.Completion.extensionHom f.toRingHom hf
      (algebraMap ℂ (Raw A B) z) = _
    rw [UniformSpace.Completion.extensionHom_coe]
    exact f.commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom f.toRingHom hf
        (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom f.toRingHom hf (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star f x
private lemma extendHom_of {C : Type*} [NormedRing C] [NormedAlgebra ℂ C]
    [StarRing C] [NormedStarGroup C] [CompleteSpace C]
    (f : Raw A B →⋆ₐ[ℂ] C) (hf : Continuous f) (x : Raw A B) :
    extendHom f hf (of x) = f x :=
  UniformSpace.Completion.extensionHom_coe _ hf x
def spatialLift (ρ : RepresentationPair A B) :
    Algebra A B →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  extendHom (A := A) (B := B)
    (C := Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K)
    (spatialRaw ρ) (continuous_spatialRaw ρ)


def fromMaximal : MaxTensor.Algebra A B →⋆ₐ[ℂ] Algebra A B :=
  MaxTensor.lift includeLeft includeRight legs_commute
@[simp] lemma fromMaximal_of (x : A ⊗[ℂ] B) :
    fromMaximal (MaxTensor.of (MaxTensor.rawEquiv x)) =
      of (rawEquiv (A := A) (B := B) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    change MaxTensor.lift includeLeft includeRight legs_commute
      (MaxTensor.of (a ⊗ₜ[ℂ] b)) = _
    rw [MaxTensor.lift_of_tmul]
    change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) = of (rawEquiv (a ⊗ₜ[ℂ] b))
    rw [← map_mul, ← map_mul]
    congr 2
    simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
lemma fromMaximal_denseRange : DenseRange (fromMaximal (A := A) (B := B)) :=
  denseRange_of.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨MaxTensor.of (MaxTensor.rawEquiv (rawEquiv.symm x)), by simp⟩)
end KirchbergRordam.MinTensor
namespace KirchbergRordam
namespace Spatial
open scoped TensorProduct
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Nontrivial H] [Nontrivial K]
instance : Nontrivial (Hilbert H K) :=
  (UniformSpace.Completion.coe_injective (H ⊗[ℂ] K)).nontrivial
end Spatial
namespace MinTensor
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]


instance : Nontrivial (Algebra A B) := by
  obtain ⟨π⟩ := exists_irreducible_representation A
  obtain ⟨σ⟩ := exists_irreducible_representation B
  let ρ : RepresentationPair A B := {
    H := π.space
    K := σ.space
    normH := inferInstance
    innerH := inferInstance
    completeH := inferInstance
    normK := inferInstance
    innerK := inferInstance
    completeK := inferInstance
    leftRep := π.representation
    rightRep := σ.representation }
  exact (spatialLift ρ).toRingHom.domain_nontrivial
end MinTensor
end KirchbergRordam
namespace KirchbergRordam.States
open scoped ComplexOrder


theorem exists_norming_state (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A] (a : A) :
    ∃ φ : A →ₚ[ℂ] ℂ, φ 1 = 1 ∧ ‖φ (star a * a)‖ = ‖a‖ ^ 2 := by
  let b := star a * a
  have hb : 0 ≤ b := star_mul_self_nonneg a
  let : IsStarNormal b := (IsSelfAdjoint.of_nonneg hb).isStarNormal
  let S := StarAlgebra.elemental ℂ b
  have hs : (‖b‖ : ℂ) ∈ spectrum ℂ b := by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg b hb)
  obtain ⟨χ,hχ⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum b).surjective
    ⟨(‖b‖ : ℂ),hs⟩
  let g : S →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom χ
  let : StarHomClass (S →ₐ[ℂ] ℂ) S ℂ := AlgHomClass.instStarHomClass
  have hg : ‖g.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, AlgHom.coe_toContinuousLinearMap] using NonUnitalStarAlgHom.norm_apply_le g x
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq S.toSubalgebra.toSubmodule
    g.toContinuousLinearMap
  have hψ1 : ψ 1 = 1 := by
    exact (hψ (1 : S)).trans (map_one g)
  have hψb : ψ b = (‖b‖ : ℂ) := by
    have hh := congrArg Subtype.val hχ
    exact (hψ ⟨b,StarAlgebra.elemental.self_mem ℂ b⟩).trans hh
  let φ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ψ.toLinearMap
    (eval_nonneg ψ (hψnorm.trans_le hg) hψ1)
  refine ⟨φ,hψ1,?_⟩
  change ‖ψ b‖ = ‖a‖ ^ 2
  rw [hψb,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  simp only [b,CStarRing.norm_star_mul_self,pow_two]
end KirchbergRordam.States
end

end OAI
