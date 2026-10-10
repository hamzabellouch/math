import OAI.Analysis.NuclearUltrapower.Model
import OAI.Analysis.NuclearUltrapower.HilbertTensor

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section NormTransfer
local instance spatialTensorBoundedSMul (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul

variable {B : Type u} {C : Type v} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

@[simp] theorem spatialEval_tmul (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (b : B) (c : C) :
    spatialEval H K ρ σ (b ⊗ₜ[ℂ] c) = TensorProduct.mapL (ρ b) (σ c) := rfl

@[simp] theorem commutingEval_tmul (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (b : B) (c : C) :
    commutingEval H ρ σ (b ⊗ₜ[ℂ] c) = ρ b * σ c := rfl

/-- Uniform finite projective bound on all spatial and commuting evaluations.
In particular the real suprema defining the tensor norms are genuine bounds. -/
theorem evals_bounded (x : B ⊗[ℂ] C) :
    ∃ M : ℝ, (∀ (H K : ComplexHilbert.{w})
      (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      ‖spatialEval H K ρ σ x‖ ≤ M) ∧
      (∀ (H : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ‖commutingEval H ρ σ x‖ ≤ M) := by
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    refine ⟨‖b‖ * ‖c‖, ?_, ?_⟩
    · intro H K ρ σ
      exact (TensorProduct.norm_mapL_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ b)
          (NonUnitalStarAlgHom.norm_apply_le σ c) (norm_nonneg _) (norm_nonneg _))
    · intro H ρ σ
      exact (norm_mul_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ b)
          (NonUnitalStarAlgHom.norm_apply_le σ c) (norm_nonneg _) (norm_nonneg _))
  | add x y hx hy =>
    obtain ⟨M, hM, hM'⟩ := hx
    obtain ⟨N, hN, hN'⟩ := hy
    refine ⟨M + N, ?_, ?_⟩
    · intro H K ρ σ
      rw [map_add]
      exact (norm_add_le (spatialEval H K ρ σ x) (spatialEval H K ρ σ y)).trans
        (add_le_add (hM H K ρ σ) (hN H K ρ σ))
    · intro H ρ σ
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hM' H ρ σ) (hN' H ρ σ))

theorem norm_spatialEval_le (x : B ⊗[ℂ] C) (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ σ x‖ ≤ minTensorNorm.{u,v,w} x := by
  obtain ⟨M, hM, _⟩ := evals_bounded.{u,v,w} x
  unfold minTensorNorm
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro _ ⟨H, K, ρ, σ, rfl⟩
    exact hM H K ρ σ
  · exact ⟨H, K, ρ, σ, rfl⟩

theorem norm_commutingEval_le (x : B ⊗[ℂ] C) (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hcomm : ∀ b c, Commute (ρ b) (σ c)) :
    ‖commutingEval H ρ σ x‖ ≤ maxTensorNorm.{u,v,w} x := by
  obtain ⟨M, _, hM⟩ := evals_bounded.{u,v,w} x
  unfold maxTensorNorm
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro _ ⟨H, ρ, σ, _, rfl⟩
    exact hM H ρ σ
  · exact ⟨H, ρ, σ, hcomm, rfl⟩

/-- Nuclearity precisely transfers a bound in every spatial realization to
every commuting realization. This is the sole tensor-norm step in the source
nuclear-finiteness proof, with no identification with coordinate quotients. -/
theorem nuclear_transfer_norm (hB : IsNuclear.{u,v} B) (x : B ⊗[ℂ] C) (M : ℝ)
    (hM : ∀ (H K : ComplexHilbert.{max u v})
      (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
        ‖spatialEval H K ρ σ x‖ ≤ M)
    (H : ComplexHilbert.{max u v}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hcomm : ∀ b c, Commute (ρ b) (σ c)) :
    ‖commutingEval H ρ σ x‖ ≤ M := by
  apply (norm_commutingEval_le x H ρ σ hcomm).trans
  rw [← hB C x]
  apply csSup_le
  · exact ⟨‖spatialEval H H ρ σ x‖, H, H, ρ, σ, rfl⟩
  · rintro _ ⟨H, K, ρ, σ, rfl⟩
    exact hM H K ρ σ

end NormTransfer
end NuclearUltrapower

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower

section Support
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The nondegenerate support of a possibly nonunital representation. -/
def representationSupport (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (φ 1 - 1).ker

@[simp] theorem mem_representationSupport (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    x ∈ representationSupport φ ↔ φ 1 x = x := by
  simp [representationSupport, sub_eq_zero]

instance supportComplete (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    CompleteSpace (representationSupport φ) :=
  (φ 1 - 1).isClosed_ker.completeSpace_coe

/-- Projection to the support, without invoking separability or nonzero spaces. -/
def supportProjection (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    H →L[ℂ] representationSupport φ :=
  (φ 1).codRestrict _ (fun x => by
    rw [mem_representationSupport]
    change (φ 1 * φ 1) x = φ 1 x
    rw [← map_mul, one_mul])

@[simp] theorem supportProjection_coe (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    (supportProjection φ x : H) = φ 1 x := rfl

@[simp] theorem supportProjection_subtype (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (x : representationSupport φ) : supportProjection φ x = x := by
  ext
  exact (mem_representationSupport φ x).mp x.property

/-- A possibly degenerate representation becomes unital on its actual support. -/
def supportRepresentation (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (representationSupport φ →L[ℂ] representationSupport φ) where
  toFun a := (φ a).restrict (fun x _ => by
    rw [mem_representationSupport]
    change (φ 1 * φ a) x = φ a x
    rw [← map_mul, one_mul])
  map_zero' := by ext x; simp
  map_one' := by
    ext x
    exact (mem_representationSupport φ x).mp x.property
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one,
    (mem_representationSupport φ x).mp x.property]
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    change inner ℂ (φ (star a) (x : H)) (y : H) = inner ℂ (x : H) (φ a (y : H))
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

@[simp] theorem supportRepresentation_coe (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (a : A) (x : representationSupport φ) : (supportRepresentation φ a x : H) = φ a x := rfl

/-- The original representation is its unital support plus a zero representation. -/
theorem representation_support_factor (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    φ a = (representationSupport φ).subtypeL.comp ((supportRepresentation φ a).comp
      (supportProjection φ)) := by
  ext x
  change φ a x = (φ a * φ 1) x
  rw [← map_mul, mul_one]

/-- Orthogonal projection has norm at most one, including the zero support. -/
theorem supportProjection_norm_le (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ‖supportProjection φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖φ 1 x‖ ≤ 1 * ‖x‖
  have h1 : ‖(1 : A)‖ ≤ 1 := by
    nontriviality A
    simp
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right ((NonUnitalStarAlgHom.norm_apply_le φ (1 : A)).trans h1) (norm_nonneg x))

end Support
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct

section SpatialSupport
local instance tensorSupportBoundedSMul (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul
variable {B : Type u} {C : Type v} [CStarAlgebra B] [CStarAlgebra C]

abbrev supportHilbert (H : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ComplexHilbert.{w} where
  carrier := representationSupport ρ

/-- Degenerate spatial representations factor through their two unital supports. -/
theorem spatialEval_support_factor (x : B ⊗[ℂ] C) (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    spatialEval H K ρ σ x =
      (TensorProduct.mapL (representationSupport ρ).subtypeL (representationSupport σ).subtypeL).comp
        ((spatialEval (supportHilbert H ρ) (supportHilbert K σ)
          (supportRepresentation ρ).toNonUnitalStarAlgHom
          (supportRepresentation σ).toNonUnitalStarAlgHom x).comp
            (TensorProduct.mapL (supportProjection ρ) (supportProjection σ))) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
  | tmul b c =>
      change TensorProduct.mapL (ρ b) (σ c) =
        (TensorProduct.mapL (representationSupport ρ).subtypeL (representationSupport σ).subtypeL).comp
          ((TensorProduct.mapL (supportRepresentation ρ b) (supportRepresentation σ c)).comp
            (TensorProduct.mapL (supportProjection ρ) (supportProjection σ)))
      rw [← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]
      rw [← representation_support_factor, ← representation_support_factor]

/-- No unitality was hidden in the minimal tensor norm quantifier. -/
theorem spatialEval_norm_le_support (x : B ⊗[ℂ] C) (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ σ x‖ ≤
      ‖spatialEval (supportHilbert H ρ) (supportHilbert K σ)
        (supportRepresentation ρ).toNonUnitalStarAlgHom
        (supportRepresentation σ).toNonUnitalStarAlgHom x‖ := by
  have hI : ‖TensorProduct.mapL (representationSupport ρ).subtypeL
      (representationSupport σ).subtypeL‖ ≤ 1 := by
    apply (TensorProduct.norm_mapL_le _ _).trans
    have hρ := (representationSupport ρ).subtypeₗᵢ.norm_toContinuousLinearMap_le
    have hσ := (representationSupport σ).subtypeₗᵢ.norm_toContinuousLinearMap_le
    simpa only [Submodule.subtypeₗᵢ_toContinuousLinearMap, one_mul] using
      mul_le_mul hρ hσ (norm_nonneg _) zero_le_one
  have hP : ‖TensorProduct.mapL (supportProjection ρ) (supportProjection σ)‖ ≤ 1 := by
    apply (TensorProduct.norm_mapL_le _ _).trans
    simpa only [one_mul] using mul_le_mul (supportProjection_norm_le ρ)
      (supportProjection_norm_le σ) (norm_nonneg (supportProjection σ)) zero_le_one
  rw [spatialEval_support_factor]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul hI (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one).trans
  simpa only [one_mul, mul_one] using
    mul_le_mul_of_nonneg_left hP (norm_nonneg
      (spatialEval (supportHilbert H ρ) (supportHilbert K σ)
        (supportRepresentation ρ).toNonUnitalStarAlgHom
        (supportRepresentation σ).toNonUnitalStarAlgHom x))

/-- It suffices to bound all unital spatial realizations, not to assume away the others. -/
theorem spatial_bound_of_unital (x : B ⊗[ℂ] C) (M : ℝ)
    (h : ∀ (H K : ComplexHilbert.{w}) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
      (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      ‖spatialEval H K ρ.toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom x‖ ≤ M)
    (H K : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : ‖spatialEval H K ρ σ x‖ ≤ M := by
  apply le_trans (spatialEval_norm_le_support x H K ρ σ)
  exact h (supportHilbert H ρ) (supportHilbert K σ)
    (supportRepresentation ρ) (supportRepresentation σ)

end SpatialSupport
end NuclearUltrapower

end
end
end
end
end
end
end
end

section

noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section Bounds
local instance (H K : ComplexHilbert.{0}) : IsBoundedSMul ℂ (H ⊗[ℂ] K) :=
  NormedSpace.toIsBoundedSMul
variable {A C : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

private def scalarHilbert : ComplexHilbert.{0} := ⟨ℂ⟩

theorem minTensorNorm_nonneg (x : A ⊗[ℂ] C) : 0 ≤ minTensorNorm.{0,0,0} x :=
  (norm_nonneg (spatialEval scalarHilbert scalarHilbert
    (0 : A →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ)) (0 : C →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ)) x)).trans
    (norm_spatialEval_le x scalarHilbert scalarHilbert 0 0)

def tensorLeftRep {H K : ComplexHilbert.{0}}
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : A →⋆ₙₐ[ℂ] (TensorHilbert H K →L[ℂ] TensorHilbert H K) :=
  (tensorLeftHom (E := H) (F := K)).toNonUnitalStarAlgHom.comp R

def tensorRightRep {H K : ComplexHilbert.{0}}
    (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : C →⋆ₙₐ[ℂ] (TensorHilbert H K →L[ℂ] TensorHilbert H K) :=
  (tensorRightHom (E := H) (F := K)).toNonUnitalStarAlgHom.comp S

@[simp] theorem tensorLeftRep_apply {H K : ComplexHilbert.{0}}
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    tensorLeftRep (K := K) R a = tensorLeftHom (R a) := rfl
@[simp] theorem tensorRightRep_apply {H K : ComplexHilbert.{0}}
    (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (c : C) :
    tensorRightRep (H := H) S c = tensorRightHom (S c) := rfl

theorem tensor_reps_commute (H K : ComplexHilbert.{0})
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (a : A) (c : C) :
    Commute (tensorLeftRep (K := K) R a) (tensorRightRep (H := H) S c) :=
  tensorLeftRight_commute _ _

/-- Spatial evaluation is the commuting evaluation on the Hilbert completion;
completion does not change its operator norm. -/
theorem completed_spatial_eq (H K : ComplexHilbert.{0})
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (x : A ⊗[ℂ] C) :
    (spatialEval H K R S x).completion =
      commutingEval ⟨TensorHilbert H K⟩ (tensorLeftRep R) (tensorRightRep S) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    rw [spatialEval_tmul,commutingEval_tmul,tensorLeftRep_apply,tensorRightRep_apply,
      tensorLeftRight_mul]
    rfl
  | add x y hx hy => simp only [map_add,completed_add,hx,hy]

/-- The easy inequality holds for every C*-algebra, including nonunital ones. -/
theorem minTensorNorm_le_maxTensorNorm (x : A ⊗[ℂ] C) :
    minTensorNorm.{0,0,0} x ≤ maxTensorNorm.{0,0,0} x := by
  apply csSup_le
  · exact ⟨_,scalarHilbert,scalarHilbert,0,0,rfl⟩
  · rintro _ ⟨H,K,R,S,rfl⟩
    rw [← completed_norm,completed_spatial_eq]
    exact norm_commutingEval_le x ⟨TensorHilbert H K⟩ (tensorLeftRep R) (tensorRightRep S)
      (tensor_reps_commute H K R S)

theorem maxTensorNorm_le_of_commuting (x : A ⊗[ℂ] C) (M : ℝ)
    (h : ∀ (H : ComplexHilbert.{0}) (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (S : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), (∀ a c, Commute (R a) (S c)) →
        ‖commutingEval H R S x‖ ≤ M) : maxTensorNorm.{0,0,0} x ≤ M := by
  apply csSup_le
  · refine ⟨_,scalarHilbert,0,0,?_,rfl⟩
    intro a c
    exact Commute.zero_left 0
  · rintro _ ⟨H,R,S,hRS,rfl⟩
    exact h H R S hRS
end Bounds
end NuclearUltrapower
end
end

end OAI
