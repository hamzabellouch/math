import OAI.Analysis.NuclearUltrapower.HilbertSchmidt
import OAI.Analysis.NuclearUltrapower.TensorNorms
import OAI.Analysis.NuclearUltrapower.Laplacian

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
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section ComplementPolynomial
variable {Γ A : Type*} [CStarAlgebra A]

/-- Polynomial form of the complemented Laplacian, retaining arbitrary unitary tuples. -/
theorem laplacian_complement_expand (S : Finset Γ) (u : Γ → unitary A) :
    (4 * (S.card : ℝ)) • (1 : A) - laplacian S (fun s => (u s : A)) =
      (2 * (S.card : ℝ)) • (1 : A) + ∑ s ∈ S, ((u s : A) + star (u s : A)) := by
  have hs (s : Γ) : star ((u s : A) - 1) * ((u s : A) - 1) =
      (2 : ℝ) • (1 : A) - ((u s : A) + star (u s : A)) := by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one,
      Unitary.coe_star_mul_self]
    module
  simp only [laplacian, hs, Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  module
private theorem laplacian_complement_expand_complex (indices : Finset Γ)
    (unitaries : Γ → unitary A) :
    (4 * (indices.card : ℂ)) • (1 : A) - laplacian indices (fun index => (unitaries index : A)) =
      (2 * (indices.card : ℂ)) • (1 : A) +
        ∑ index ∈ indices, ((unitaries index : A) + star (unitaries index : A)) := by
  have expansion := laplacian_complement_expand indices unitaries
  have real_smul (scalar : ℝ) (value : A) : (scalar : ℂ) • value = scalar • value :=
    IsScalarTower.algebraMap_smul ℂ scalar value
  rw [← real_smul (4 * indices.card) 1, ← real_smul (2 * indices.card) 1] at expansion
  push_cast at expansion
  exact expansion

def laplacianComplement (S : Finset Γ) (u : Γ → unitary A) : A :=
  (4 * (S.card : ℝ)) • (1 : A) - laplacian S (fun s => (u s : A))
end ComplementPolynomial

section TensorComplement
variable {Γ B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

/-- The algebraic tensor polynomial whose norm expresses the required lower bound. -/
def tensorComplement (S : Finset Γ) (u : Γ → unitary B) (q : Γ → unitary C) : B ⊗[ℂ] C :=
  (2 * (S.card : ℂ)) • ((1 : B) ⊗ₜ[ℂ] (1 : C)) +
    ∑ s ∈ S, (((u s : B) ⊗ₜ[ℂ] (q s : C)) + (star (u s : B) ⊗ₜ[ℂ] star (q s : C)))

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The tensor of two unitaries as a unitary of the completed tensor Hilbert space. -/
def pairedTensorUnitary (u : unitary (E →L[ℂ] E)) (v : unitary (F →L[ℂ] F)) :
    unitary (TensorHilbert E F →L[ℂ] TensorHilbert E F) :=
  ⟨completedTensorMap (u : E →L[ℂ] E) (v : F →L[ℂ] F), by
    rw [Unitary.mem_iff]
    constructor <;> rw [← completedTensorMap_star, ← completedTensorMap_mul]
    · simp only [Unitary.coe_star_mul_self, completedTensorMap_one]
    · simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, completedTensorMap_one]⟩

@[simp] theorem pairedTensorUnitary_coe (u : unitary (E →L[ℂ] E)) (v : unitary (F →L[ℂ] F)) :
    (pairedTensorUnitary u v : TensorHilbert E F →L[ℂ] TensorHilbert E F) =
      completedTensorMap (u : E →L[ℂ] E) (v : F →L[ℂ] F) := rfl

@[simp] theorem pairedTensorUnitary_action (u : unitary (E →L[ℂ] E)) (v : unitary (F →L[ℂ] F)) :
    (pairedTensorUnitary u v : TensorHilbert E F →L[ℂ] TensorHilbert E F) =
      tensorUnitaryAction (Unitary.linearIsometryEquiv u) (Unitary.linearIsometryEquiv v) := by
  rw [pairedTensorUnitary_coe]; rfl

def spatialUnitaryTuple (H K : ComplexHilbert)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (u : Γ → unitary B) (q : Γ → unitary C) :
    Γ → unitary (TensorHilbert H K →L[ℂ] TensorHilbert H K) := by
  let a : Γ → unitary (H →L[ℂ] H) := fun s => Unitary.map (StarMonoidHom.ofClass ρ) (u s)
  let b : Γ → unitary (K →L[ℂ] K) := fun s => Unitary.map (StarMonoidHom.ofClass σ) (q s)
  exact fun s => pairedTensorUnitary (a s) (b s)

/-- Spatial evaluation followed by completion is the complemented unitary Laplacian. -/
theorem spatial_complement (S : Finset Γ) (u : Γ → unitary B) (q : Γ → unitary C)
    (H K : ComplexHilbert) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (spatialEval H K ρ.toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom (tensorComplement S u q)).completion =
      (4 * (S.card : ℂ)) • (1 : TensorHilbert H K →L[ℂ] TensorHilbert H K) -
        laplacian S (fun s => completedTensorMap (ρ (u s)) (σ (q s))) := by
  classical
  let U : Γ → unitary (TensorHilbert H K →L[ℂ] TensorHilbert H K) :=
    spatialUnitaryTuple (B := B) (C := C) H K ρ σ u q
  have he := laplacian_complement_expand_complex
    (A := TensorHilbert H K →L[ℂ] TensorHilbert H K) S U
  change (4 * (S.card : ℂ)) • (1 : TensorHilbert H K →L[ℂ] TensorHilbert H K) -
      laplacian S (fun s => completedTensorMap (ρ (u s)) (σ (q s))) = _ at he
  rw [he]
  simp only [tensorComplement, map_add, map_smul, map_sum, spatialEval_tmul,
    StarAlgHom.coe_toNonUnitalStarAlgHom, map_one, map_star, completed_add, completed_smul]
  rw [tensorMap_one, completed_one]
  have hsum (f : Γ → (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K)) :
      (∑ s ∈ S, f s).completion = ∑ s ∈ S, (f s).completion := by
    clear he
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp only [Finset.sum_insert ha, completed_add, ih]
  rw [hsum]
  simp only [completed_add, U, spatialUnitaryTuple, pairedTensorUnitary_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change completedTensorMap (ρ (u s)) (σ (q s)) +
      completedTensorMap (star (ρ (u s))) (star (σ (q s))) = _
  rw [completedTensorMap_star]
  rfl
end TensorComplement

section SpatialGap
variable {Γ : Type u} [Group Γ] {B C : Type v} [CStarAlgebra B] [CStarAlgebra C]

def tupleRepresentation (q : Γ →* unitary C) (K : ComplexHilbert.{v})
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : Γ →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    ((Unitary.map (StarMonoidHom.ofClass σ)).toMonoidHom.comp q)

@[simp] theorem tupleRepresentation_apply (q : Γ →* unitary C) (K : ComplexHilbert.{v})
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (g : Γ) :
    tupleRepresentation q K σ g =
      Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass σ) (q g)) := rfl

theorem unitary_complement_norm_of_energy {J T : Type*} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] (S : Finset J)
    (U : J → unitary (T →L[ℂ] T)) (b : ℝ) (hb : b ≤ 4 * (S.card : ℝ))
    (he : ∀ x : T, b * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖(U s : T →L[ℂ] T) x - x‖ ^ 2) :
    ‖(4 * (S.card : ℂ)) • (1 : T →L[ℂ] T) -
        laplacian S (fun s => (U s : T →L[ℂ] T))‖ ≤ 4 * (S.card : ℝ) - b := by
  have hg := (laplacian_lower_iff S (fun s => (U s : T →L[ℂ] T)) b).mpr he
  have hr (r : ℝ) (a : T →L[ℂ] T) : (r : ℂ) • a = r • a :=
    IsScalarTower.algebraMap_smul ℂ r a
  have hcast : (4 * (S.card : ℂ)) = ((4 * (S.card : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, hr]
  exact laplacian_complement_norm S U hb hg

/-- The spatial estimate is abstracted from the quotient to keep inference local. -/
theorem spatial_complement_bound_unital (q : Γ →* unitary C)
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hwm : ∀ (K : ComplexHilbert.{v}) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      HasNoFiniteDimensionalSubrep (tupleRepresentation q K σ))
    (u : Γ → unitary B)
    (H K : ComplexHilbert.{v}) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ.toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom (tensorComplement S u q)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  let σg := tupleRepresentation q K σ
  have hσg := hwm K σ
  let Ut : Γ → unitary (TensorHilbert H K →L[ℂ] TensorHilbert H K) := fun g =>
    pairedTensorUnitary (Unitary.map (StarMonoidHom.ofClass ρ) (u g))
      (Unitary.map (StarMonoidHom.ofClass σ) (q g))
  have hb : κ ^ 2 / (4 * (S.card : ℝ)) ≤ 4 * (S.card : ℝ) := by
    have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    apply (div_le_iff₀ (by positivity : 0 < 4 * (S.card : ℝ))).mpr
    nlinarith
  have he (ξ : TensorHilbert H K) : κ ^ 2 / (4 * (S.card : ℝ)) * ‖ξ‖ ^ 2 ≤
      ∑ s ∈ S, ‖(Ut s : TensorHilbert H K →L[ℂ] TensorHilbert H K) ξ - ξ‖ ^ 2 := by
    have hx := weak_mixing_bound S κ hS hκ0 hgap σg hσg
      (fun g => Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass ρ) (u g))) ξ
    simpa only [Ut, pairedTensorUnitary_action, σg, tupleRepresentation_apply] using hx
  rw [← completed_norm, spatial_complement]
  exact unitary_complement_norm_of_energy S Ut _ hb he
theorem spatial_complement_bound (q : Γ →* unitary C)
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hwm : ∀ (K : ComplexHilbert.{v}) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      HasNoFiniteDimensionalSubrep (tupleRepresentation q K σ))
    (u : Γ → unitary B)
    (H K : ComplexHilbert.{v}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ σ (tensorComplement S u q)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  exact spatial_bound_of_unital _ _
    (fun H K ρ σ => spatial_complement_bound_unital q S κ hS hκ0 hκ hgap hwm u H K ρ σ) H K ρ σ
end SpatialGap
end NuclearUltrapower

end
end
end
end
end
end
end
end

end OAI
