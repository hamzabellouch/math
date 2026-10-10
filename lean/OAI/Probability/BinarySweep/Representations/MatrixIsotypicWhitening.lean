import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.Whitening
import OAI.Probability.BinarySweep.MatrixBounds.MatrixProjection

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Irrep
open Representation Density

variable {G V I : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [Fintype I] [DecidableEq I]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G (EuclideanSpace ℂ I))

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem matrix_whitening_positive [ρ.IsIrreducible] (B C : Matrix I I ℂ)
    (hC : C.IsHermitian)
    (hCc : ∀ g w, C.toEuclideanLin (σ g w) = σ g (C.toEuclideanLin w))
    (hBC : B*C = 1)
    (hT : ∀ g w, (B.conjTranspose*B).toEuclideanLin (σ g w) =
      σ g ((B.conjTranspose*B).toEuclideanLin w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (ht : (B.conjTranspose*B).trace.re = 1) :
    (C.conjTranspose*C - (Module.finrank ℂ V : ℂ) •
      projectionMatrix (isotypicSpan ρ σ)).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  have hsym : C.toEuclideanLin.IsSymmetric := by
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
    change C.toEuclideanLin.adjoint = C.toEuclideanLin
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hC.eq]
  have h := whitening_positive ρ σ B.toEuclideanLin C.toEuclideanLin hsym hCc
    (by simpa only [Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,Matrix.toLpLin_one,← Module.End.one_eq_id] using
      congrArg Matrix.toEuclideanLin hBC)
    (by simpa only [Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using hT)
    hσ (by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,Module.End.mul_eq_comp,← Matrix.toLpLin_mul_same,
        trace_toEuclideanLinear]
      exact ht)
  simpa only [map_sub,map_smul,projectionMatrix_linear,Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using h

end BinaryCoordinateSweeps.Irrep

end

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W U : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G U)

lemma map_isotypic_le (f : IntertwiningMap σ τ) :
    (isotypicSpan ρ σ).map f.toLinearMap ≤ isotypicSpan ρ τ := by
  rintro _ ⟨w,hw,rfl⟩
  apply Submodule.iSup_induction (fun g : IntertwiningMap ρ σ => LinearMap.range g.toLinearMap)
    (motive:=fun w => f w ∈ isotypicSpan ρ τ) hw
  · intro g w hw
    obtain ⟨v,rfl⟩ := hw
    exact (le_iSup (fun g : IntertwiningMap ρ τ => LinearMap.range g.toLinearMap) (f.comp g)) ⟨v,rfl⟩
  · simp
  · intro x y hx hy; simpa only [map_add] using (isotypicSpan ρ τ).add_mem hx hy

lemma map_isotypic_equiv (e : σ.Equiv τ) :
    (isotypicSpan ρ σ).map e.toLinearEquiv.toLinearMap = isotypicSpan ρ τ := by
  apply le_antisymm (map_isotypic_le ρ σ τ e.toIntertwiningMap)
  intro u hu
  refine ⟨e.symm u,?_,e.toLinearEquiv.apply_symm_apply u⟩
  apply map_isotypic_le ρ τ σ e.symm.toIntertwiningMap
  exact ⟨u,hu,rfl⟩

end BinaryCoordinateSweeps.Irrep

open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Irrep
open Representation Density

variable {G V I : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [Fintype I] [DecidableEq I]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G (EuclideanSpace ℂ I))

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypicProjection_commutes (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (hc : ∀ g v, M.toEuclideanLin (σ g v) = σ g (M.toEuclideanLin v)) :
    M * projectionMatrix (isotypicSpan ρ σ) = projectionMatrix (isotypicSpan ρ σ) * M := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,projectionMatrix_linear]
  apply LinearMap.ext
  intro v
  change M.toEuclideanLin ((isotypicSpan ρ σ).starProjection v) =
    (isotypicSpan ρ σ).starProjection (M.toEuclideanLin v)
  apply symmetric_projection_commutes
  · apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
    change M.toEuclideanLin.adjoint = M.toEuclideanLin
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hM.eq]
  · exact commuting_isotypic_invariant ρ σ M.toEuclideanLin hc

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical MonoidAlgebra

namespace BinaryCoordinateSweeps.Irrep
open Representation

universe uG uW uV uI
variable {G : Type uG} [Group G] [Fintype G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ G W)

def algebraSubmoduleInclusion (m : Submodule ℂ[G] σ.asModule) :
    IntertwiningMap (Representation.ofModule (k:=ℂ) (G:=G) m) σ where
  toFun v := σ.asModuleEquiv (m.subtype (RestrictScalars.addEquiv ℂ ℂ[G] m v))
  map_add' x y := by simp
  map_smul' c v := by
    simp only [RestrictScalars.addEquiv_map_smul,algebraMap_smul,RingHom.id_apply]
    change σ.asModuleEquiv (c • (m.subtype (RestrictScalars.addEquiv ℂ ℂ[G] m v))) = _
    exact map_smul σ.asModuleEquiv c _
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change σ.asModuleEquiv (m.subtype ((RestrictScalars.addEquiv ℂ ℂ[G] m)
      (Representation.ofModule m g v))) = σ g
      (σ.asModuleEquiv (m.subtype (RestrictScalars.addEquiv ℂ ℂ[G] m v)))
    rw [← Representation.asAlgebraHom_of,Representation.ofModule_asAlgebraHom_apply_apply]
    simp only [AddEquiv.apply_symm_apply,map_smul,Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]

omit [Fintype G] in
lemma algebraSubmoduleInclusion_injective (m : Submodule ℂ[G] σ.asModule) :
    Function.Injective (algebraSubmoduleInclusion σ m) := by
  intro x y h
  apply (RestrictScalars.addEquiv ℂ ℂ[G] m).injective
  apply Subtype.val_injective
  exact σ.asModuleEquiv.injective h

variable [FiniteDimensional ℂ W]
  {I : Type uI} {V : I → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (ρ : ∀ i, Representation ℂ G (V i))

omit [∀ i, FiniteDimensional ℂ (V i)] in
theorem iSup_isotypic_eq_top
    (complete : ∀ (U : Type uW) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
      (τ : Representation ℂ G U), τ.IsIrreducible → ∃ i, Nonempty (τ.Equiv (ρ i))) :
    (⨆ i, isotypicSpan (ρ i) σ) = ⊤ := by
  let T : Subrepresentation σ := {
    toSubmodule := ⨆ i, isotypicSpan (ρ i) σ
    apply_mem_toSubmodule := by
      intro g v hv
      apply Submodule.iSup_induction (fun i => isotypicSpan (ρ i) σ)
        (motive:=fun v => σ g v ∈ ⨆ i, isotypicSpan (ρ i) σ) hv
      · intro i v hv
        apply (le_iSup (fun i => isotypicSpan (ρ i) σ) i)
        rw [← isotypicSpan_map (ρ i) σ g]
        exact ⟨v,hv,rfl⟩
      · simp
      · intro x y hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy }
  have htop : T.asSubmodule = ⊤ := by
    apply top_unique
    rw [← IsSemisimpleModule.sSup_simples_eq_top ℂ[G] σ.asModule]
    apply sSup_le
    intro m hm
    let group : AddCommGroup (RestrictScalars ℂ ℂ[G] m) :=
      Module.addCommMonoidToAddCommGroup ℂ
    let _ := group
    let _ : @Module ℂ (RestrictScalars ℂ ℂ[G] m) _ group.toAddCommMonoid :=
      RestrictScalars.module ℂ ℂ[G] m
    let τ := Representation.ofModule (k:=ℂ) (G:=G) m
    let f := algebraSubmoduleInclusion σ m
    have : FiniteDimensional ℂ (RestrictScalars ℂ ℂ[G] m) :=
      FiniteDimensional.of_injective f.toLinearMap (algebraSubmoduleInclusion_injective σ m)
    have : IsSimpleModule ℂ[G] m := hm
    have hτ : τ.IsIrreducible :=
      (Representation.isSimpleModule_iff_irreducible_ofModule m).mp hm
    obtain ⟨i,⟨e⟩⟩ := complete _ τ hτ
    intro x hx
    let v : RestrictScalars ℂ ℂ[G] m := (RestrictScalars.addEquiv ℂ ℂ[G] m).symm ⟨x,hx⟩
    change σ.asModuleEquiv x ∈ ⨆ i, isotypicSpan (ρ i) σ
    apply (le_iSup (fun i => isotypicSpan (ρ i) σ) i)
    apply (le_iSup (fun f : IntertwiningMap (ρ i) σ => LinearMap.range f.toLinearMap)
      (f.comp e.symm.toIntertwiningMap))
    refine ⟨e.toLinearEquiv.toFun v,?_⟩
    change f (e.toLinearEquiv.symm.toFun (e.toLinearEquiv.toFun v)) = σ.asModuleEquiv x
    exact congrArg f.toLinearMap.toFun (e.toLinearEquiv.symm_apply_apply v)
  have hT : T = ⊤ := Subrepresentation.subrepresentationSubmoduleOrderIso.injective
    (htop.trans (Subrepresentation.subrepresentationSubmoduleOrderIso.map_top).symm)
  exact congrArg Subrepresentation.toSubmodule hT

end BinaryCoordinateSweeps.Irrep

end

end OAI
