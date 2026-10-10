import OAI.Analysis.NuclearUltrapower.RepresentationUltraproduct
import OAI.Analysis.NuclearUltrapower.SpatialGap
import OAI.Analysis.NuclearUltrapower.FiniteInduction
import OAI.Analysis.NuclearUltrapower.HilbertUltraproduct

namespace OAI

section
noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal TensorProduct
namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

omit [∀ i, CompleteSpace (E i)] in
@[simp] theorem map_one : map (E := E) (F := E) ω (1 : lp (fun i => E i →L[ℂ] E i) ∞) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [map_coe]
    congr 1

/-- The Hilbert-ultraproduct operator action is unital, including zero spaces. -/
def unitalOperatorRep : lp (fun i => E i →L[ℂ] E i) ∞ →⋆ₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  toFun := map ω
  map_zero' := map_zero ω
  map_one' := map_one ω
  map_add' := map_add ω
  map_mul' := map_mul ω
  commutes' c := by
    change operatorRep (E := E) ω (algebraMap ℂ _ c) = algebraMap ℂ _ c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      _root_.map_smul (operatorRep (E := E) ω)]
    change c • map ω (1 : lp (fun i => E i →L[ℂ] E i) ∞) = c • 1
    rw [map_one]
  map_star' := map_star ω
end HilbertUltraproduct

namespace VariableUltra
section CoordinateHom
variable {ι : Type u} {A : ι → Type v} {C : ι → Type w}
  [∀ i, CStarAlgebra (A i)] [∀ i, CStarAlgebra (C i)]
  [∀ i, Nontrivial (A i)] [∀ i, Nontrivial (C i)]

/-- Contractive coordinate homomorphisms preserve boundedness, with no dimension bound. -/
def sequenceHom (f : ∀ i, A i →⋆ₐ[ℂ] C i) : Seq A →⋆ₐ[ℂ] Seq C where
  toFun x := ⟨fun i => f i (x i), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le (f i) _).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x i)⟩⟩
  map_zero' := by ext i; exact map_zero (f i)
  map_one' := by ext i; exact map_one (f i)
  map_add' x y := by ext i; exact map_add (f i) _ _
  map_mul' x y := by ext i; exact map_mul (f i) _ _
  commutes' c := by ext i; exact (f i).commutes c
  map_star' x := by ext i; exact map_star (f i) _

@[simp] theorem sequenceHom_apply (f : ∀ i, A i →⋆ₐ[ℂ] C i) (x : Seq A) (i : ι) :
    sequenceHom f x i = f i (x i) := rfl
end CoordinateHom

section QuotientHilbert
variable {ι : Type u} {A : ι → Type v} {E : ι → Type w}
  [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ι) (f : ∀ i, A i →⋆ₐ[ℂ] (E i →L[ℂ] E i))

theorem coordinateRep_respects {x y : Seq A} (h : Rel A ω x y) :
    HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f x) =
      HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f y) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  apply (HilbertUltraproduct.map_eq_zero_iff ω _).mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => NonUnitalStarAlgHom.norm_apply_le (f i) (x i - y i))
  exact h

/-- Every uniformly varying coordinate representation descends to the quotient. -/
def quotientHilbertRep : Algebra A ω →⋆ₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  __ := (con A ω).liftₐ
    ((HilbertUltraproduct.unitalOperatorRep (E := E) ω).comp (sequenceHom f)).toAlgHom
    (fun _ _ h => coordinateRep_respects ω f h)
  map_star' x := by
    induction x using Quotient.inductionOn with | h x =>
      exact map_star ((HilbertUltraproduct.unitalOperatorRep (E := E) ω).comp (sequenceHom f)) x

@[simp] theorem quotientHilbertRep_mk (x : Seq A) :
    quotientHilbertRep ω f (mk A ω x) = HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f x) := rfl
/-- Coordinatewise commutation survives the quotient and its Hilbert action. -/
theorem quotientHilbertRep_commute_left
    (x : Seq (fun i => E i →L[ℂ] E i)) (q : Algebra A ω)
    (h : ∀ i a, Commute (x i) (f i a)) :
    Commute (HilbertUltraproduct.unitalOperatorRep (E := E) ω x)
      (quotientHilbertRep ω f q) := by
  induction q using Quotient.inductionOn with | h q =>
    change Commute (HilbertUltraproduct.unitalOperatorRep (E := E) ω x)
      (HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f q))
    have hc : Commute x (sequenceHom f q) := by
      apply Subtype.ext
      funext i
      exact h i (q i)
    exact hc.map (HilbertUltraproduct.unitalOperatorRep (E := E) ω)
end QuotientHilbert
end VariableUltra

instance tensorHilbertNontrivial {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Nontrivial F] :
    Nontrivial (TensorHilbert E F) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨⟨(x ⊗ₜ[ℂ] y : E ⊗[ℂ] F), 0, ?_⟩⟩
  intro he
  have hn := congrArg norm he
  have hp : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  simp only [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, norm_zero] at hn
  linarith

section TensorCoordinateMaps
variable {ι : Type u} {E : Type v} {F : ι → Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (F i)] [∀ i, Nontrivial (F i)]
  {B : Type*} [CStarAlgebra B] (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ω : Ultrafilter ι)

/-- First tensor factor, represented uniformly at every coordinate. -/
def tensorLeftSequence : B →⋆ₐ[ℂ] VariableUltra.Seq (fun i => TensorHilbert E (F i) →L[ℂ] TensorHilbert E (F i)) where
  toFun b := ⟨fun _ => tensorLeftHom (ρ b), memℓp_infty ⟨‖b‖, by
    rintro _ ⟨i, rfl⟩
    change ‖completedTensorMap (ρ b) (1 : F i →L[ℂ] F i)‖ ≤ ‖b‖
    calc
      _ ≤ ‖ρ b‖ * ‖(1 : F i →L[ℂ] F i)‖ := completedTensorMap_norm_le _ _
      _ = ‖ρ b‖ := by rw [norm_one, mul_one]
      _ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le ρ b⟩⟩
  map_zero' := by apply Subtype.ext; funext i; exact map_zero ((tensorLeftHom (F := F i)).comp ρ)
  map_one' := by apply Subtype.ext; funext i; exact map_one ((tensorLeftHom (F := F i)).comp ρ)
  map_add' b c := by apply Subtype.ext; funext i; exact map_add ((tensorLeftHom (F := F i)).comp ρ) b c
  map_mul' b c := by apply Subtype.ext; funext i; exact map_mul ((tensorLeftHom (F := F i)).comp ρ) b c
  commutes' c := by apply Subtype.ext; funext i; exact ((tensorLeftHom (F := F i)).comp ρ).commutes c
  map_star' b := by apply Subtype.ext; funext i; exact map_star ((tensorLeftHom (F := F i)).comp ρ) b

@[simp] theorem tensorLeftSequence_apply (b : B) (i : ι) :
    tensorLeftSequence (F := F) ρ b i = tensorLeftHom (ρ b) := rfl

def tensorAlpha : B →⋆ₐ[ℂ]
    (HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω →L[ℂ]
      HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω) :=
  (HilbertUltraproduct.unitalOperatorRep ω).comp (tensorLeftSequence ρ)

@[simp] theorem tensorAlpha_apply (b : B) :
    tensorAlpha (F := F) ρ ω b = HilbertUltraproduct.unitalOperatorRep ω
      (tensorLeftSequence (F := F) ρ b) := rfl

def tensorBeta : VariableUltra.Algebra (fun i => F i →L[ℂ] F i) ω →⋆ₐ[ℂ]
    (HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω →L[ℂ]
      HilbertUltraproduct (fun i => TensorHilbert E (F i)) ω) :=
  VariableUltra.quotientHilbertRep ω (fun _ => tensorRightHom)

/-- The two factor representations commute after taking the Hilbert ultraproduct. -/
theorem tensorAlphaBeta_commute (b : B)
    (q : VariableUltra.Algebra (fun i => F i →L[ℂ] F i) ω) :
    Commute (tensorAlpha (F := F) ρ ω b) (tensorBeta (E := E) ω q) := by
  exact VariableUltra.quotientHilbertRep_commute_left ω
    (fun i => tensorRightHom (E := E) (F := F i)) (tensorLeftSequence ρ b) q
    (fun i a => tensorLeftRight_commute (ρ b) a)

end TensorCoordinateMaps
end NuclearUltrapower
end
end

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section ComplementEvaluation
variable {Γ B C D A : Type*} [CStarAlgebra B] [CStarAlgebra C] [CStarAlgebra D]
  [CStarAlgebra A]

def complementPoly (S : Finset Γ) (z w : Γ → A) : A :=
  (2 * (S.card : ℂ)) • 1 + ∑ g ∈ S, (z g * w g + star (z g) * star (w g))

@[simp] theorem map_complementPoly (f : A →⋆ₐ[ℂ] D) (S : Finset Γ) (z w : Γ → A) :
    f (complementPoly S z w) = complementPoly S (fun g => f (z g)) (fun g => f (w g)) := by
  simp only [complementPoly, map_add, map_smul, map_sum, map_one, map_mul, map_star]

theorem complementEval_poly (H : ComplexHilbert) (α : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (β : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : Finset Γ) (u : Γ → unitary B)
    (v : Γ → unitary C) :
    commutingEval H α.toNonUnitalStarAlgHom β.toNonUnitalStarAlgHom (tensorComplement S u v) =
      complementPoly S (fun g => α (u g)) (fun g => β (v g)) := by
  simp only [tensorComplement, complementPoly, map_add, map_smul, map_sum,
    commutingEval_tmul, StarAlgHom.coe_toNonUnitalStarAlgHom, map_one, one_mul, map_star]
end ComplementEvaluation
section NuclearFiniteness
variable {Γ : Type u} [Group Γ] {B : Type v} [CStarAlgebra B]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

/-- The actual quotient group tuple from the varying finite-dimensional family. -/
def finiteQuotientTuple : Γ →* unitary (VariableUltra.operatorQuotient (fun i => π i) ω) :=
  ((Unitary.map (VariableUltra.starAlgToStarMonoid (VariableUltra.mk _ ω))).toMonoidHom).comp
    (VariableUltra.representationSequence π)

@[simp] theorem tupleRepresentation_finite (K : ComplexHilbert.{v})
    (σ : VariableUltra.operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    tupleRepresentation (finiteQuotientTuple π ω) K σ =
      VariableUltra.quotientRepresentation π ω σ := rfl

/-- Coordinate second factors, before passing to either quotient. -/
def rightRepSequence (g : Γ) : VariableUltra.Seq
    (fun i => TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) :=
  VariableUltra.sequenceHom (fun i => tensorRightHom (E := E) (F := π i))
    (VariableUltra.representationSequence π g)

/-- The complemented Laplacian as one uniformly bounded operator sequence. -/
def coordinateComplement (S : Finset Γ) (u : Γ → unitary B) : VariableUltra.Seq
    (fun i => TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) :=
  complementPoly S (fun g => tensorLeftSequence (F := fun i => π i) ρ (u g))
    (rightRepSequence (E := E) π)

@[simp] theorem tensorBeta_finiteQuotient (g : Γ) :
    tensorBeta (E := E) (F := fun i => π i) ω (finiteQuotientTuple π ω g) =
      HilbertUltraproduct.unitalOperatorRep (E := fun i => TensorHilbert E (π i)) ω
        (rightRepSequence (E := E) π g) := by
  rfl

/-- Named bundled coordinates keep all tensor/Hilbert instances shared. -/
def finiteTensorHilbert : ComplexHilbert.{v} :=
  ⟨HilbertUltraproduct (fun i => TensorHilbert E (π i)) ω⟩

def finiteTensorAlpha : B →⋆ₐ[ℂ] (finiteTensorHilbert (E := E) π ω →L[ℂ]
    finiteTensorHilbert (E := E) π ω) := tensorAlpha (F := fun i => π i) ρ ω

def finiteTensorBeta : VariableUltra.operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ]
    (finiteTensorHilbert (E := E) π ω →L[ℂ] finiteTensorHilbert (E := E) π ω) :=
  tensorBeta (E := E) (F := fun i => π i) ω

def finiteTensorAction : VariableUltra.Seq
    (fun i => TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) →⋆ₐ[ℂ]
    (finiteTensorHilbert (E := E) π ω →L[ℂ] finiteTensorHilbert (E := E) π ω) :=
  HilbertUltraproduct.unitalOperatorRep ω

@[simp] theorem finiteTensorAlpha_val (b : B) :
    finiteTensorAlpha ρ π ω b = finiteTensorAction (E := E) π ω
      (tensorLeftSequence (F := fun i => π i) ρ b) := rfl

@[simp] theorem finiteTensorBeta_val (g : Γ) :
    finiteTensorBeta (E := E) π ω (finiteQuotientTuple π ω g) =
      finiteTensorAction (E := E) π ω (rightRepSequence (E := E) π g) := rfl

theorem map_coordinateComplement (S : Finset Γ) (u : Γ → unitary B) :
    finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u) =
      complementPoly S (fun g => finiteTensorAlpha ρ π ω (u g))
        (fun g => finiteTensorBeta (E := E) π ω (finiteQuotientTuple π ω g)) := by
  exact map_complementPoly (finiteTensorAction (E := E) π ω) S
    (fun g => tensorLeftSequence (F := fun i => π i) ρ (u g)) (rightRepSequence (E := E) π)

/-- Commuting evaluation is the image of the actual bounded coordinate sequence. -/
theorem commuting_coordinateComplement (S : Finset Γ) (u : Γ → unitary B) :
    commutingEval (finiteTensorHilbert (E := E) π ω)
      (finiteTensorAlpha ρ π ω).toNonUnitalStarAlgHom
      (finiteTensorBeta (E := E) π ω).toNonUnitalStarAlgHom
      (tensorComplement S u (finiteQuotientTuple π ω)) =
        finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u) := by
  rw [map_coordinateComplement]
  exact complementEval_poly (finiteTensorHilbert (E := E) π ω)
    (finiteTensorAlpha ρ π ω) (finiteTensorBeta (E := E) π ω) S u (finiteQuotientTuple π ω)

theorem nuclear_coordinate_bound
    (hB : IsNuclear.{v,v} B) (S : Finset Γ) (κ : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (u : Γ → unitary B) :
    ‖finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  let q := finiteQuotientTuple π ω
  have hwm (K : ComplexHilbert.{v})
      (σ : VariableUltra.operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
      HasNoFiniteDimensionalSubrep (tupleRepresentation q K σ) := by
    exact VariableUltra.quotientRepresentation_weakly_mixing π ω hω hirr hne S κ hκ0 hκ hgap σ
  let H := finiteTensorHilbert (E := E) π ω
  have hb := nuclear_transfer_norm hB (tensorComplement S u q)
    (4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)))
    (fun H K a b => spatial_complement_bound q S κ hS hκ0 hκ hgap hwm u H K a b)
    H (finiteTensorAlpha ρ π ω).toNonUnitalStarAlgHom
      (finiteTensorBeta (E := E) π ω).toNonUnitalStarAlgHom
    (fun b c => tensorAlphaBeta_commute ρ ω b c)
  rw [commuting_coordinateComplement] at hb
  exact hb

/-- Quantitative finiteness obstruction: an inequivalent irreducible sequence
cannot have a uniformly small spectral minimum for a fixed nuclear tuple. -/
theorem nuclear_no_inequivalent_matches
    (hB : IsNuclear.{v,v} B) (S : Finset Γ) (κ a : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ ^ 2 / (4 * (S.card : ℝ)))
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (u : Γ → unitary B)
    (hsmall : ∀ i, 4 * (S.card : ℝ) - a < ‖coordinateComplement ρ π S u i‖) : False := by
  have hb := nuclear_coordinate_bound ρ π ω hB S κ hS hκ0 hκ hgap hω hirr hne u
  have hl := HilbertUltraproduct.map_norm_tendsto ω (coordinateComplement ρ π S u)
  have he : 4 * (S.card : ℝ) - a ≤
      ‖finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u)‖ :=
    ge_of_tendsto hl (Filter.Eventually.of_forall fun i => (hsmall i).le)
  linarith
end NuclearFiniteness
end NuclearUltrapower
end
end

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (ω : Ultrafilter ι)

/-- A unitary family is uniformly bounded, independently of Hilbert dimension. -/
def boundedUnitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : lp (fun i => E i →L[ℂ] E i) ∞ :=
  ⟨fun i => (U i : E i →L[ℂ] E i), memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, LinearIsometryEquiv.coe_coe''] using ((U i).norm_map x).le⟩⟩

@[simp] theorem boundedUnitary_apply (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) (i : ι) :
    boundedUnitary U i = (U i : E i →L[ℂ] E i) := rfl

/-- Coordinate unitaries preserve the ultralimit seminorm. -/
def preUnitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    UltraPreHilbert E ω ≃ₗᵢ[ℂ] UltraPreHilbert E ω where
  toLinearMap := UltraPreHilbert.mapLinear ω (boundedUnitary U)
  invFun := UltraPreHilbert.mapLinear ω (boundedUnitary (fun i => (U i).symm))
  left_inv x := by
    apply Subtype.ext; funext i
    exact (U i).symm_apply_apply _
  right_inv x := by
    apply Subtype.ext; funext i
    exact (U i).apply_symm_apply _
  norm_map' x := by
    have h := UltraPreHilbert.norm_tendsto ω
      (UltraPreHilbert.mapLinear ω (boundedUnitary U) x)
    simp only [UltraPreHilbert.family_map, boundedUnitary_apply,
      LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.norm_map] at h
    exact tendsto_nhds_unique h (UltraPreHilbert.norm_tendsto ω x)

/-- Coordinate unitaries act unitarily on the completed Hilbert ultraproduct. -/
def unitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    HilbertUltraproduct E ω ≃ₗᵢ[ℂ] HilbertUltraproduct E ω :=
  (preUnitary ω U).toLinearEquiv.extendOfIsometry
    UniformSpace.Completion.toComplₗᵢ.toLinearMap UniformSpace.Completion.toComplₗᵢ.toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun x => by simp)

@[simp] theorem unitary_coe (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : UltraPreHilbert E ω) :
    unitary ω U (x : HilbertUltraproduct E ω) =
      (preUnitary ω U x : HilbertUltraproduct E ω) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- Compatibility with the faithful operator realization. -/
theorem unitary_toContinuousLinearMap (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    (unitary ω U : HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) =
      map ω (boundedUnitary U) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => rw [LinearIsometryEquiv.coe_coe'', unitary_coe, map_coe]; rfl

@[simp] theorem unitary_one :
    unitary ω (fun i => (1 : E i ≃ₗᵢ[ℂ] E i)) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [unitary_coe]
    change (preUnitary ω (fun i => (1 : E i ≃ₗᵢ[ℂ] E i)) x : HilbertUltraproduct E ω) = x
    rfl

@[simp] theorem unitary_mul (U V : ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    unitary ω (fun i => U i * V i) = unitary ω U * unitary ω V := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    change unitary ω (fun i => U i * V i) (x : HilbertUltraproduct E ω) =
      unitary ω U (unitary ω V x)
    rw [unitary_coe, unitary_coe, unitary_coe]
    rfl

/-- Operator-norm null changes in a family of unitaries do not change its
Hilbert-ultraproduct action. -/
theorem unitary_eq_of_tendsto (U V : ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (h : Tendsto (fun i => ‖(U i : E i →L[ℂ] E i) - (V i : E i →L[ℂ] E i)‖)
      (ω : Filter ι) (𝓝 0)) : unitary ω U = unitary ω V := by
  have hz := (map_eq_zero_iff ω (boundedUnitary U - boundedUnitary V)).mpr h
  have hadd := map_add ω (boundedUnitary U - boundedUnitary V) (boundedUnitary V)
  rw [sub_add_cancel, hz, zero_add] at hadd
  ext x
  have he := congrArg (fun T : HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω => T x) hadd
  simpa only [← unitary_toContinuousLinearMap, LinearIsometryEquiv.coe_coe''] using he

/-- Pointwise asymptotic multiplicativity suffices. There is no hidden
intersection over all group relations, nor any dimension bound. -/
def approximateRepresentation {Γ : Type w} [Group Γ]
    (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g * h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0)) :
    Γ →* (HilbertUltraproduct E ω ≃ₗᵢ[ℂ] HilbertUltraproduct E ω) where
  toFun g := unitary ω (U g)
  map_one' := (unitary_eq_of_tendsto ω _ _ h1).trans (unitary_one ω)
  map_mul' g h := by
    change unitary ω (U (g * h)) = unitary ω (U g) * unitary ω (U h)
    have he := unitary_eq_of_tendsto ω (U (g * h))
      (fun i => U g i * U h i) (hmul g h)
    exact he.trans (unitary_mul ω (U g) (U h))

end HilbertUltraproduct
end NuclearUltrapower

noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace NuclearUltrapower
variable {Γ : Type u} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic form of the matching Laplacian. -/
def tupleEnergy (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) : ℝ :=
  ∑ s ∈ S, ‖U s x - x‖ ^ 2

theorem tupleEnergy_nonneg (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) :
    0 ≤ tupleEnergy S U x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tupleEnergy_bound (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) :
    tupleEnergy S U x ≤ 4 * (S.card : ℝ) * ‖x‖ ^ 2 := by
  calc
    _ ≤ ∑ s ∈ S, 4 * ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      have h := norm_sub_le (U s x) x
      rw [(U s).norm_map] at h
      nlinarith [norm_nonneg (U s x - x), norm_nonneg x]
    _ = _ := by simp; ring

theorem tupleEnergy_smul (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (c : ℂ) (x : E) :
    tupleEnergy S U (c • x) = ‖c‖ ^ 2 * tupleEnergy S U x := by
  simp only [tupleEnergy, map_smul, ← smul_sub, norm_smul, mul_pow, Finset.mul_sum]

theorem tupleEnergy_continuous (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    Continuous (tupleEnergy S U) := by
  unfold tupleEnergy
  fun_prop

variable [Nontrivial E]

/-- Bottom Rayleigh energy, equal to the bottom of the matching spectrum in a
faithful representation. This definition retains arbitrary Hilbert dimension. -/
def bottomEnergy (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) : ℝ :=
  sInf {r | ∃ x : E, ‖x‖ = 1 ∧ r = tupleEnergy S U x}

theorem energyValues_nonempty (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    {r | ∃ x : E, ‖x‖ = 1 ∧ r = tupleEnergy S U x}.Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  exact ⟨_, x, hx, rfl⟩

omit [Nontrivial E] in
theorem energyValues_bddBelow (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    BddBelow {r | ∃ x : E, ‖x‖ = 1 ∧ r = tupleEnergy S U x} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  exact tupleEnergy_nonneg S U x

theorem bottomEnergy_nonneg (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    0 ≤ bottomEnergy S U :=
  le_csInf (energyValues_nonempty S U) (by rintro _ ⟨x, _, rfl⟩; exact tupleEnergy_nonneg S U x)

omit [Nontrivial E] in
theorem bottomEnergy_le (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) (hx : ‖x‖ = 1) :
    bottomEnergy S U ≤ tupleEnergy S U x :=
  csInf_le (energyValues_bddBelow S U) ⟨x, hx, rfl⟩

theorem bottomEnergy_bound (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    bottomEnergy S U ≤ 4 * (S.card : ℝ) := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  have h := (bottomEnergy_le S U x hx).trans (tupleEnergy_bound S U x)
  simpa [hx] using h

omit [Nontrivial E] in
theorem bottomEnergy_mul_norm (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) :
    bottomEnergy S U * ‖x‖ ^ 2 ≤ tupleEnergy S U x := by
  by_cases hx : x = 0
  · simp [hx, tupleEnergy]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy : ‖(‖x‖⁻¹ : ℂ) • x‖ = 1 := by simp [norm_smul, norm_inv, hn]
  have h := bottomEnergy_le S U ((‖x‖⁻¹ : ℂ) • x) hy
  rw [tupleEnergy_smul] at h
  calc
    bottomEnergy S U * ‖x‖ ^ 2 ≤
        ‖(‖x‖⁻¹ : ℂ)‖ ^ 2 * tupleEnergy S U x * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
    _ = tupleEnergy S U x := by
      rw [_root_.mul_right_comm]
      simp [norm_inv, hn]

theorem exists_energy_lt (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ = 1 ∧ tupleEnergy S U x < bottomEnergy S U + ε := by
  obtain ⟨r, ⟨x, hx, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (energyValues_nonempty S U) (lt_add_of_pos_right (bottomEnergy S U) hε)
  exact ⟨x, hx, hr⟩

end NuclearUltrapower

namespace NuclearUltrapower

namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (ω : Ultrafilter ι) {Γ : Type w}

/-- Finite Laplacian energies pass to the Hilbert ultraproduct exactly. -/
theorem tupleEnergy_tendsto (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (x : UltraPreHilbert E ω) :
    Tendsto (fun i => tupleEnergy S (fun g => U g i) (UltraPreHilbert.family ω x i))
      (ω : Filter ι) (𝓝 (tupleEnergy S (fun g => unitary ω (U g))
        (x : HilbertUltraproduct E ω))) := by
  unfold tupleEnergy
  apply tendsto_finsetSum
  intro s _
  have h := (UltraPreHilbert.norm_tendsto ω (preUnitary ω (U s) x - x)).pow 2
  convert h using 1
  · rfl
  · rw [unitary_coe, ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]

variable [∀ i, Nontrivial (E i)]

/-- Bottom matching energies always have an ultralimit, with the
uniform upper bound 4 |S| and no dimension restriction. -/
theorem bottomEnergy_tendsto (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    Tendsto (fun i => bottomEnergy S (fun g => U g i)) (ω : Filter ι)
      (𝓝 (limUnder (ω : Filter ι) (fun i => bottomEnergy S (fun g => U g i)))) := by
  apply hilbert_tendsto_ultralimit_of_bounded
  refine ⟨4 * (S.card : ℝ), fun i => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (bottomEnergy_nonneg _ _)]
  exact bottomEnergy_bound _ _

omit [∀ i, Nontrivial (E i)] in
/-- Lower coordinate Rayleigh bounds pass to every vector of the completion,
not merely to vectors given by elementary tensors or bounded families. -/
theorem limit_energy_lower (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    {r : ℝ} (hr : Tendsto (fun i => bottomEnergy S (fun g => U g i))
      (ω : Filter ι) (𝓝 r)) (x : HilbertUltraproduct E ω) :
    r * ‖x‖ ^ 2 ≤ tupleEnergy S (fun g => unitary ω (U g)) x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (tupleEnergy_continuous _ _)
  | ih x =>
    rw [UniformSpace.Completion.norm_coe]
    apply le_of_tendsto_of_tendsto (hr.mul ((UltraPreHilbert.norm_tendsto ω x).pow 2))
      (tupleEnergy_tendsto ω S U x)
    exact Filter.Eventually.of_forall (fun i => bottomEnergy_mul_norm _ _ _)

/-- Varying-dimensional spectral gap, expressed in the equivalent Rayleigh
formulation from the tensor-norm formulation. No uniform dimension bound and
no coordinate group relations are assumed. -/
theorem varying_gap [Group Γ] (S : Finset Γ) (κ : ℝ)
    (hgap : HasKazhdanGap.{w, max u v} S κ)
    (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g * h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0))
    {r : ℝ} (hr : Tendsto (fun i => bottomEnergy S (fun g => U g i))
      (ω : Filter ι) (𝓝 r)) : r = 0 ∨ κ ≤ r ∧ r ≤ 4 * (S.card : ℝ) := by
  have hr0 : 0 ≤ r := ge_of_tendsto hr (Filter.Eventually.of_forall
    (fun i => bottomEnergy_nonneg S (fun g => U g i)))
  have hrR : r ≤ 4 * (S.card : ℝ) := le_of_tendsto hr (Filter.Eventually.of_forall
    (fun i => bottomEnergy_bound S (fun g => U g i)))
  by_cases hz : r = 0
  · exact Or.inl hz
  right
  refine ⟨?_, hrR⟩
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  let ρ := approximateRepresentation ω U h1 hmul
  have hno (x : HilbertUltraproduct E ω) (hx : ∀ g, ρ g x = x) : x = 0 := by
    have h := limit_energy_lower ω S U hr x
    have he : tupleEnergy S (fun g => unitary ω (U g)) x = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      change ‖ρ s x - x‖ ^ 2 = 0
      rw [hx, sub_self, norm_zero, zero_pow (by decide)]
    rw [he] at h
    have hn : ‖x‖ = 0 := by
      have hs : ‖x‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hrpos).mp (by simpa [mul_comm] using h)
      nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  by_contra! hlt
  let ε := (κ - r) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  choose x hx hxE using (fun i => exists_energy_lt S (fun g => U g i) hε)
  let y : UltraPreHilbert E ω := (⟨x, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩; exact (hx i).le⟩⟩ : lp E ∞)
  have hyn : ‖y‖ = 1 := by
    apply tendsto_nhds_unique (UltraPreHilbert.norm_tendsto ω y)
    exact tendsto_const_nhds.congr (fun i => (hx i).symm)
  have hbound : tupleEnergy S (fun g => unitary ω (U g)) (y : HilbertUltraproduct E ω)
      ≤ r + ε := by
    apply le_of_tendsto_of_tendsto (tupleEnergy_tendsto ω S U y) (hr.add_const ε)
    exact Filter.Eventually.of_forall (fun i => (hxE i).le)
  have hg := hgap (HilbertUltraproduct E ω) ρ hno (y : HilbertUltraproduct E ω)
  rw [UniformSpace.Completion.norm_coe, hyn, one_pow, mul_one] at hg
  change κ ≤ tupleEnergy S (fun g => unitary ω (U g)) (y : HilbertUltraproduct E ω) at hg
  dsimp [ε] at hbound
  linarith

end HilbertUltraproduct
end NuclearUltrapower
end
end
end

end OAI
