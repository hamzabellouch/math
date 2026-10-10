import Mathlib

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

section CompletedOperators

variable {H K L : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup L] [NormedSpace ℂ L]

lemma norm_completion_le (T : H →L[ℂ] K) : ‖T.completion‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x => simpa using T.le_opNorm x

lemma norm_completion (T : H →L[ℂ] K) : ‖T.completion‖ = ‖T‖ := by
  apply le_antisymm (norm_completion_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa using T.completion.le_opNorm (x : Completion H)

lemma completion_comp (S : K →L[ℂ] L) (T : H →L[ℂ] K) :
    (S.comp T).completion = S.completion.comp T.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

lemma completion_add (S T : H →L[ℂ] K) :
    (S + T).completion = S.completion + T.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp [← Completion.coe_add]

lemma completion_smul (c : ℂ) (T : H →L[ℂ] K) :
    (c • T).completion = c • T.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (c • T).completion.continuous
      (T.completion.continuous.const_smul c)
  | ih x => simp only [ContinuousLinearMap.completion_apply_coe,
      smul_apply, Completion.coe_smul]

lemma completion_zero : (0 : H →L[ℂ] K).completion = 0 := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

end CompletedOperators

section CompletedHilbertTensor

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma inner_mapL_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x y : H ⊗[ℂ] K) :
    inner ℂ ((TensorProduct.mapL S T) x) y =
      inner ℂ x ((TensorProduct.mapL (star S) (star T)) y) := by
  induction x using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction y using TensorProduct.inductionOn with
    | tmul y₁ y₂ =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    | add y₁ y₂ h₁ h₂ => simp only [inner_add_right, map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]

lemma completion_mapL_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    star (TensorProduct.mapL S T).completion =
      (TensorProduct.mapL (star S) (star T)).completion := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      simp only [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe]
      exact inner_mapL_star S T y x

end CompletedHilbertTensor

structure ComplexHilbert where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [innerProductSpace : InnerProductSpace ℂ Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance] ComplexHilbert.normedAddCommGroup
  ComplexHilbert.innerProductSpace ComplexHilbert.completeSpace

instance : CoeSort ComplexHilbert.{u} (Type u) := ⟨ComplexHilbert.Carrier⟩

instance completedTensorCStar (H K : ComplexHilbert.{u}) :
    CStarAlgebra (Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) := inferInstance

instance hilbertOperatorsCStar (H : ComplexHilbert.{u}) :
    CStarAlgebra (H →L[ℂ] H) := inferInstance

structure SpatialRepresentation (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  left : ComplexHilbert.{max u v}
  right : ComplexHilbert.{max u v}
  leftRep : A →⋆ₙₐ[ℂ] (left →L[ℂ] left)
  rightRep : B →⋆ₙₐ[ℂ] (right →L[ℂ] right)

abbrev SpatialRepresentation.hilbert {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (π : SpatialRepresentation A B) : ComplexHilbert.{max u v} where
  Carrier := Completion (π.left ⊗[ℂ] π.right)

abbrev SpatialRepresentation.space {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (π : SpatialRepresentation A B) := Completion (π.left ⊗[ℂ] π.right)

def SpatialAmbient (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : Type (max u v + 1) :=
  lp (fun π : SpatialRepresentation A B => π.space →L[ℂ] π.space) ∞

instance spatialAmbientCStar (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (SpatialAmbient A B) := by
  unfold SpatialAmbient
  infer_instance

instance spatialAmbientCoeFun (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    CoeFun (SpatialAmbient A B) (fun _ => ∀ π : SpatialRepresentation A B, π.space →L[ℂ] π.space) :=
  ⟨fun z => z.val⟩

def spatialElementary {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (a : A) (b : B) : SpatialAmbient A B :=
  ⟨fun π => (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion,
    memℓp_infty ⟨‖a‖ * ‖b‖, by
      rintro _ ⟨π, rfl⟩
      dsimp only
      rw [norm_completion]
      exact (TensorProduct.norm_mapL_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π.leftRep a) (NonUnitalStarAlgHom.norm_apply_le π.rightRep b)
          (norm_nonneg _) (norm_nonneg _))⟩⟩

section ElementaryTensors

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

@[simp]
lemma spatialElementary_zero_left (b : B) : spatialElementary (0 : A) b = 0 := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL _ _).completion = 0
  simp [completion_zero]

@[simp]
lemma spatialElementary_zero_right (a : A) : spatialElementary a (0 : B) = 0 := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL _ _).completion = 0
  simp [completion_zero]

lemma spatialElementary_add_left (a a' : A) (b : B) :
    spatialElementary (a + a') b = spatialElementary a b + spatialElementary a' b := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (a + a')) (π.rightRep b)).completion =
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion +
    (TensorProduct.mapL (π.leftRep a') (π.rightRep b)).completion
  rw [map_add, TensorProduct.mapL_add_left, completion_add]

lemma spatialElementary_add_right (a : A) (b b' : B) :
    spatialElementary a (b + b') = spatialElementary a b + spatialElementary a b' := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep a) (π.rightRep (b + b'))).completion =
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion +
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b')).completion
  rw [map_add, TensorProduct.mapL_add_right, completion_add]

lemma spatialElementary_smul_left (c : ℂ) (a : A) (b : B) :
    spatialElementary (c • a) b = c • spatialElementary a b := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (c • a)) (π.rightRep b)).completion =
    c • (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
  rw [map_smul, TensorProduct.mapL_smul_left, completion_smul]

lemma spatialElementary_smul_right (c : ℂ) (a : A) (b : B) :
    spatialElementary a (c • b) = c • spatialElementary a b := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep a) (π.rightRep (c • b))).completion =
    c • (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
  rw [map_smul, TensorProduct.mapL_smul_right, completion_smul]

lemma spatialElementary_mul (a a' : A) (b b' : B) :
    spatialElementary (a * a') (b * b') = spatialElementary a b * spatialElementary a' b' := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (a * a')) (π.rightRep (b * b'))).completion =
    (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion *
    (TensorProduct.mapL (π.leftRep a') (π.rightRep b')).completion
  rw [map_mul, map_mul, TensorProduct.mapL_mul]
  exact completion_comp _ _

@[simp]
lemma spatialElementary_star (a : A) (b : B) :
    spatialElementary (star a) (star b) = star (spatialElementary a b) := by
  apply Subtype.ext
  funext π
  change (TensorProduct.mapL (π.leftRep (star a)) (π.rightRep (star b))).completion =
    star (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
  rw [map_star, map_star]
  exact (completion_mapL_star _ _).symm

lemma norm_spatialElementary_le (a : A) (b : B) : ‖spatialElementary a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro π
  change ‖(TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion‖ ≤ _
  rw [norm_completion]
  exact (TensorProduct.norm_mapL_le _ _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π.leftRep a)
      (NonUnitalStarAlgHom.norm_apply_le π.rightRep b) (norm_nonneg _) (norm_nonneg _))

end ElementaryTensors

def minimalTensorSubalgebra (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalStarSubalgebra ℂ (SpatialAmbient A B) :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range fun p : A × B => spatialElementary p.1 p.2)).topologicalClosure

abbrev MinimalTensor (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] := minimalTensorSubalgebra A B

instance (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (MinimalTensor A B) := by
  letI : IsClosed ((minimalTensorSubalgebra A B : NonUnitalStarSubalgebra ℂ
    (SpatialAmbient A B)) : Set (SpatialAmbient A B)) :=
    isClosed_closure
  exact inferInstance

section Exactness

variable {A : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def SpatialRepresentation.precompRight (π : SpatialRepresentation A D)
    (q : C →⋆ₙₐ[ℂ] D) : SpatialRepresentation A C where
  left := π.left
  right := π.right
  leftRep := π.leftRep
  rightRep := π.rightRep.comp q

def tensorKernelIdeal (q : C →⋆ₙₐ[ℂ] D) : NonUnitalStarSubalgebra ℂ (SpatialAmbient A C) :=
  (NonUnitalStarAlgebra.adjoin ℂ
    {z | ∃ a : A, ∃ c : C, q c = 0 ∧ z = spatialElementary a c}).topologicalClosure

end Exactness

def Exact (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (C D : Type u) [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (q : C →⋆ₙₐ[ℂ] D), Function.Surjective q →
    ∀ z : MinimalTensor A C,
      (∀ π : SpatialRepresentation A D, (z.val : SpatialAmbient A C) (π.precompRight q) = 0) →
      z.val ∈ tensorKernelIdeal (A := A) q

section Nuclearity

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def CompletelyPositive (φ : A →L[ℂ] B) : Prop :=
  ∀ n : ℕ, ∀ x : CStarMatrix (Fin n) (Fin n) A, 0 ≤ x →
    0 ≤ CStarMatrix.ofMatrix (fun i j => φ (x i j))

def CompletelyPositive.toMap {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ) :
    CompletelyPositiveMap A B where
  toLinearMap := φ.toLinearMap
  map_cstarMatrix_nonneg' n x hx := hφ n x hx

lemma completelyPositive_of_map (φ : A →L[ℂ] B) (ψ : CompletelyPositiveMap A B)
    (h : ψ.toLinearMap = φ.toLinearMap) : CompletelyPositive φ := by
  intro n x hx
  have hm := ψ.map_cstarMatrix_nonneg' n x hx
  have he : x.map ψ.toLinearMap = CStarMatrix.ofMatrix (fun i j => φ (x i j)) := by
    ext i j
    exact congrArg (fun f : A →ₗ[ℂ] B => f (x i j)) h
  exact he ▸ hm

def Nuclear (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Prop :=
  ∀ F : Finset A, ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      ∃ ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] A,
      CompletelyPositive φ ∧ CompletelyPositive ψ ∧ ‖φ‖ ≤ 1 ∧ ‖ψ‖ ≤ 1 ∧
        ∀ a ∈ F, ‖ψ (φ a) - a‖ < ε

end Nuclearity

structure CuntzRepresentation where
  hilbert : ComplexHilbert.{0}
  [nontrivial : Nontrivial hilbert]
  generators : ℕ → hilbert →L[ℂ] hilbert
  relations : ∀ i j, star (generators i) * generators j = if i = j then 1 else 0

attribute [instance] CuntzRepresentation.nontrivial

abbrev CuntzAmbient :=
  lp (fun π : CuntzRepresentation => π.hilbert →L[ℂ] π.hilbert) ∞

instance : CStarAlgebra CuntzAmbient where

lemma CuntzRepresentation.norm_generator (π : CuntzRepresentation) (i : ℕ) :
    ‖π.generators i‖ = 1 := by
  have h : ‖π.generators i‖ * ‖π.generators i‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, π.relations i i, ite_eq_left rfl, norm_one]
  nlinarith [norm_nonneg (π.generators i)]

def cuntzGenerator (i : ℕ) : CuntzAmbient :=
  ⟨fun π => π.generators i, memℓp_infty ⟨1, by
    rintro _ ⟨π, rfl⟩
    exact (π.norm_generator i).le⟩⟩

def oInfinitySubalgebra : StarSubalgebra ℂ CuntzAmbient :=
  (StarAlgebra.adjoin ℂ (Set.range cuntzGenerator)).topologicalClosure

abbrev OInfinity := oInfinitySubalgebra

instance : CStarAlgebra OInfinity := by
  letI : IsClosed (oInfinitySubalgebra : Set CuntzAmbient) :=
    isClosed_closure
  exact inferInstance

open scoped InnerProductSpace

abbrev FockSpace := lp (fun _ : List ℕ => ℂ) 2

def fockBasis (w : List ℕ) : ℂ →ₗᵢ[ℂ] FockSpace where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : List ℕ => ℂ) 2 w).toLinearMap
  norm_map' z := by
    change ‖lp.single (E := fun _ : List ℕ => ℂ) 2 w z‖ = ‖z‖
    exact lp.norm_single (E := fun _ : List ℕ => ℂ) (by norm_num : (0 : ℝ≥0∞) < 2) w z

@[simp]
lemma fockBasis_apply (w : List ℕ) (z : ℂ) :
    fockBasis w z = lp.single 2 w z := rfl

lemma fockPrefix_orthogonal (i : ℕ) :
    OrthogonalFamily ℂ (fun _ : List ℕ => ℂ) (fun w => fockBasis (i :: w)) := by
  intro w v h z t
  simp only [fockBasis_apply, lp.inner_single_left]
  rw [lp.single_apply_ne 2 _ _ (by simpa using h)]
  exact inner_zero_right _

def fockShift (i : ℕ) : FockSpace →ₗᵢ[ℂ] FockSpace :=
  (fockPrefix_orthogonal i).linearIsometry

@[simp]
lemma fockShift_single (i : ℕ) (w : List ℕ) (z : ℂ) :
    fockShift i (lp.single 2 w z) = lp.single 2 (i :: w) z :=
  (fockPrefix_orthogonal i).linearIsometry_apply_single z

lemma fockShift_apply (i : ℕ) (x : FockSpace) (w : List ℕ) :
    fockShift i x (i :: w) = x w := by
  have h := (fockPrefix_orthogonal i).hasSum_linearIsometry x
  have h' := (lp.evalCLM ℂ (fun _ : List ℕ => ℂ) 2 (i :: w)).hasSum h
  change HasSum (fun v : List ℕ =>
    lp.single (E := fun _ : List ℕ => ℂ) 2 (i :: v) (x v) (i :: w))
    (fockShift i x (i :: w)) at h'
  have h'' : HasSum (fun v => if v = w then x w else 0)
      (fockShift i x (i :: w)) := by
    convert h' using 1
    ext v
    by_cases h : v = w
    · subst v; simp
    · simp [lp.single_apply, h, Ne.symm h]
  exact h''.unique (hasSum_ite_eq w (x w))

lemma fockShift_apply_ne (i j : ℕ) (hij : i ≠ j) (x : FockSpace) (w : List ℕ) :
    fockShift j x (i :: w) = 0 := by
  have h := (fockPrefix_orthogonal j).hasSum_linearIsometry x
  have h' := (lp.evalCLM ℂ (fun _ : List ℕ => ℂ) 2 (i :: w)).hasSum h
  change HasSum (fun v : List ℕ =>
    lp.single (E := fun _ : List ℕ => ℂ) 2 (j :: v) (x v) (i :: w))
    (fockShift j x (i :: w)) at h'
  have h'' : HasSum (fun _ : List ℕ => (0 : ℂ))
      (fockShift j x (i :: w)) := by
    convert h' using 1
    ext v
    simp [lp.single_apply, hij]
  exact h''.unique hasSum_zero

lemma fockShift_adjoint_apply (i : ℕ) (x : FockSpace) (w : List ℕ) :
    (fockShift i).toContinuousLinearMap.adjoint x w = x (i :: w) := by
  have h := ContinuousLinearMap.adjoint_inner_right (fockShift i).toContinuousLinearMap
    (lp.single (E := fun _ : List ℕ => ℂ) 2 w 1) x
  change inner ℂ (lp.single 2 w 1) ((fockShift i).toContinuousLinearMap.adjoint x) =
    inner ℂ (fockShift i (lp.single 2 w 1)) x at h
  simpa [fockShift_single, lp.inner_single_left, RCLike.inner_apply] using h

lemma fockShift_relations (i j : ℕ) :
    star (fockShift i).toContinuousLinearMap * (fockShift j).toContinuousLinearMap =
      if i = j then 1 else 0 := by
  ext x w
  change ((fockShift i).toContinuousLinearMap.adjoint ((fockShift j) x)) w = _
  rw [fockShift_adjoint_apply]
  by_cases h : i = j
  · subst j
    simp [fockShift_apply]
  · simp [h, fockShift_apply_ne i j h]

instance fockSpace_nontrivial : Nontrivial FockSpace := by
  refine ⟨⟨lp.single 2 [] 1, 0, ?_⟩⟩
  intro h
  have h' := congrArg (fun x : FockSpace => x []) h
  simp at h'

def fockRepresentation : CuntzRepresentation where
  hilbert := { Carrier := FockSpace }
  generators i := (fockShift i).toContinuousLinearMap
  relations := fockShift_relations

instance : Nonempty CuntzRepresentation := ⟨fockRepresentation⟩

instance : Nontrivial CuntzAmbient := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h' := congrArg (fun x : CuntzAmbient => x fockRepresentation) h
  exact zero_ne_one h'

instance : Nontrivial OInfinity := inferInstance

def oInfinityEvaluation (π : CuntzRepresentation) :
    OInfinity →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def oInfinityIsometry (i : ℕ) : OInfinity :=
  ⟨cuntzGenerator i, StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)⟩

@[simp]
lemma oInfinityEvaluation_isometry (π : CuntzRepresentation) (i : ℕ) :
    oInfinityEvaluation π (oInfinityIsometry i) = π.generators i := rfl

lemma oInfinityIsometry_relations (i j : ℕ) :
    star (oInfinityIsometry i) * oInfinityIsometry j = if i = j then 1 else 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext π
  change star (π.generators i) * π.generators j = _
  rw [π.relations i j]
  split_ifs <;> rfl

end WeakPureInfiniteness
end

end OAI
