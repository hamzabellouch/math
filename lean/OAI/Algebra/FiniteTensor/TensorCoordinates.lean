import Mathlib
import OAI.Algebra.FiniteTensor.ExteriorForms
import OAI.Algebra.FiniteTensor.FrobeniusQuotient

namespace OAI

/-! Frobenius coordinate sums, tensor decompositions and exterior coordinate maps. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
open scoped TensorProduct
variable (K σ : Type*) [Field K] (p : ℕ)
variable {K σ p} {B : Type*} [CommRing B] [Algebra K B]
 
def evaluate (v : σ → B) (hv : ∀ i, v i ^ p=0) : Ring K σ p →ₐ[K] B :=
  Ideal.Quotient.liftₐ (ideal K σ p) (MvPolynomial.aeval v) (by
    change ideal K σ p ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simp [hv])

@[simp] theorem evaluate_coord (v : σ → B) (hv : ∀ i, v i ^ p=0) (i : σ) :
    evaluate v hv (coord K σ p i)=v i := by
  change (MvPolynomial.aeval v) (MvPolynomial.X i)=v i
  exact MvPolynomial.aeval_X v i

@[ext] theorem hom_ext {f g : Ring K σ p →ₐ[K] B}
    (h : ∀ i, f (coord K σ p i)=g (coord K σ p i)) : f=g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

variable (K σ p) {τ : Type*}
 
def rename (f : σ → τ) : Ring K σ p →ₐ[K] Ring K τ p :=
  evaluate (fun i => coord K τ p (f i)) (fun i => variable_pow K τ p (f i))

@[simp] theorem rename_coord (f : σ → τ) (i : σ) :
    rename K σ p f (coord K σ p i)=coord K τ p (f i) := evaluate_coord _ _ _

variable (τ)
def toTensor : Ring K (σ ⊕ τ) p →ₐ[K] Ring K σ p ⊗[K] Ring K τ p :=
  evaluate (Sum.elim
    (fun i => Algebra.TensorProduct.includeLeft (R:=K) (S:=K) (coord K σ p i))
    (fun j => Algebra.TensorProduct.includeRight (R:=K) (coord K τ p j))) (by
      intro u
      cases u with
      | inl i => change (Algebra.TensorProduct.includeLeft (R:=K) (S:=K) (coord K σ p i))^p=0
                 rw [← map_pow,variable_pow,map_zero]
      | inr j => change (Algebra.TensorProduct.includeRight (R:=K) (coord K τ p j))^p=0
                 rw [← map_pow,variable_pow,map_zero])

def fromTensor : Ring K σ p ⊗[K] Ring K τ p →ₐ[K] Ring K (σ ⊕ τ) p :=
  Algebra.TensorProduct.lift (rename K σ p Sum.inl) (rename K τ p Sum.inr)
    (fun _ _ => Commute.all _ _)

@[simp] theorem toTensor_inl (i : σ) :
    toTensor K σ p τ (coord K (σ ⊕ τ) p (.inl i)) = coord K σ p i ⊗ₜ[K] (1:Ring K τ p) :=
  evaluate_coord _ _ _
@[simp] theorem toTensor_inr (j : τ) :
    toTensor K σ p τ (coord K (σ ⊕ τ) p (.inr j)) = (1:Ring K σ p) ⊗ₜ[K] coord K τ p j :=
  evaluate_coord _ _ _
@[simp] theorem fromTensor_tmul (a : Ring K σ p) (b : Ring K τ p) :
    fromTensor K σ p τ (a ⊗ₜ[K] b) = rename K σ p Sum.inl a * rename K τ p Sum.inr b := by
  simp [fromTensor]

theorem from_toTensor : (fromTensor K σ p τ).comp (toTensor K σ p τ) = AlgHom.id _ _ := by
  apply hom_ext
  intro u
  cases u <;> simp

theorem to_fromTensor : (toTensor K σ p τ).comp (fromTensor K σ p τ) = AlgHom.id _ _ := by
  apply Algebra.TensorProduct.ext
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change toTensor K σ p τ (fromTensor K σ p τ (coord K σ p i ⊗ₜ[K] 1)) = coord K σ p i ⊗ₜ[K] 1
    simp
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change toTensor K σ p τ (fromTensor K σ p τ (1 ⊗ₜ[K] coord K τ p j)) = 1 ⊗ₜ[K] coord K τ p j
    simp

 
def sumTensorEquiv : Ring K (σ ⊕ τ) p ≃ₐ[K] Ring K σ p ⊗[K] Ring K τ p :=
  { toTensor K σ p τ with
    invFun := fromTensor K σ p τ
    left_inv := fun a => AlgHom.congr_fun (from_toTensor K σ p τ) a
    right_inv := fun a => AlgHom.congr_fun (to_fromTensor K σ p τ) a }

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ : Type*) [Field K] (p : ℕ)
variable {τ : Type*} [DecidableEq τ]

omit [DecidableEq τ] in
@[simp] theorem rename_mk (f : σ → τ) (a : MvPolynomial σ K) :
    rename K σ p f (Ideal.Quotient.mk (ideal K σ p) a) =
      Ideal.Quotient.mk (ideal K τ p) (MvPolynomial.rename f a) := by
  have h : (rename K σ p f).comp (Ideal.Quotient.mkₐ K (ideal K σ p)) =
      (Ideal.Quotient.mkₐ K (ideal K τ p)).comp (MvPolynomial.rename f) := by
    ext i
    simpa [coord] using rename_coord K σ p f i
  exact AlgHom.congr_fun h a

variable [CharP K p]
 
omit [DecidableEq τ] in
theorem derivative_rename (f : σ → τ) (hf : Function.Injective f) (i : σ) (a : Ring K σ p) :
    derivative K τ p (f i) (rename K σ p f a)=rename K σ p f (derivative K σ p i a) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [rename_mk,derivative_mk,MvPolynomial.pderiv_rename hf]

 
theorem derivative_rename_other (f : σ → τ) (j : τ) (hj : j∉Set.range f) (a : Ring K σ p) :
    derivative K τ p j (rename K σ p f a)=0 := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [rename_mk,derivative_mk]
  have hz : MvPolynomial.pderiv j (MvPolynomial.rename f a)=0 := by
    induction a using MvPolynomial.induction_on with
    | C c => simp
    | add a b ha hb => simp [ha,hb]
    | mul_X a i ha =>
        have hji : j≠f i := fun h => hj ⟨i,h.symm⟩
        simp [ha,hji]
  rw [hz,map_zero]

end
end PD4Tensor.FrobeniusTruncation

 

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct
variable (K σ τ : Type*) [Field K]

def sumCoordinateIsometry :
    (0 : QuadraticForm K (σ ⊕ τ → K)).IsometryEquiv
      ((0 : QuadraticForm K (σ → K)).prod (0 : QuadraticForm K (τ → K))) :=
  { LinearEquiv.sumArrowLequivProdArrow σ τ K K with
    map_app' := by intro x; simp }

 

def sumExteriorEquiv : E K (σ ⊕ τ) ≃ₗ[K] E K σ ⊗[K] E K τ :=
  (CliffordAlgebra.equivOfIsometry (sumCoordinateIsometry K σ τ)).toLinearEquiv.trans
    ((CliffordAlgebra.prodEquiv (0 : QuadraticForm K (σ → K))
      (0 : QuadraticForm K (τ → K))).toLinearEquiv.trans
      (GradedTensorProduct.of K (CliffordAlgebra.evenOdd (0 : QuadraticForm K (σ → K)))
        (CliffordAlgebra.evenOdd (0 : QuadraticForm K (τ → K)))).symm)

def inlCoordinate : (σ → K) →ₗ[K] (σ ⊕ τ → K) :=
  (LinearEquiv.sumArrowLequivProdArrow σ τ K K).symm.toLinearMap.comp
    (LinearMap.inl K (σ → K) (τ → K))
def inrCoordinate : (τ → K) →ₗ[K] (σ ⊕ τ → K) :=
  (LinearEquiv.sumArrowLequivProdArrow σ τ K K).symm.toLinearMap.comp
    (LinearMap.inr K (σ → K) (τ → K))

def inlExterior : E K σ →ₐ[K] E K (σ ⊕ τ) := ExteriorAlgebra.map (inlCoordinate K σ τ)
def inrExterior : E K τ →ₐ[K] E K (σ ⊕ τ) := ExteriorAlgebra.map (inrCoordinate K σ τ)

@[simp] theorem sumExteriorEquiv_symm_tmul (a : E K σ) (b : E K τ) :
    (sumExteriorEquiv K σ τ).symm (a ⊗ₜ[K] b) =
      inlExterior K σ τ a * inrExterior K σ τ b := by
  simp only [sumExteriorEquiv,LinearEquiv.trans_symm,LinearEquiv.symm_symm,
    LinearEquiv.trans_apply]
  change (CliffordAlgebra.equivOfIsometry (sumCoordinateIsometry K σ τ)).symm
    (CliffordAlgebra.toProd _ _ (_ ᵍ⊗ₜ[K] _)) = _
  rw [CliffordAlgebra.toProd,GradedTensorProduct.lift_tmul,map_mul]
  have h1 : (CliffordAlgebra.equivOfIsometry (sumCoordinateIsometry K σ τ)).symm.toAlgHom.comp
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl _ _)) = inlExterior K σ τ := by
    ext v
    change CliffordAlgebra.map (sumCoordinateIsometry K σ τ).symm.toIsometry
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl _ _) (CliffordAlgebra.ι _ v)) =
      ExteriorAlgebra.map (inlCoordinate K σ τ) (ExteriorAlgebra.ι K v)
    rw [CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
    rfl
  have h2 : (CliffordAlgebra.equivOfIsometry (sumCoordinateIsometry K σ τ)).symm.toAlgHom.comp
      (CliffordAlgebra.map (QuadraticMap.Isometry.inr _ _)) = inrExterior K σ τ := by
    ext v
    change CliffordAlgebra.map (sumCoordinateIsometry K σ τ).symm.toIsometry
      (CliffordAlgebra.map (QuadraticMap.Isometry.inr _ _) (CliffordAlgebra.ι _ v)) =
      ExteriorAlgebra.map (inrCoordinate K σ τ) (ExteriorAlgebra.ι K v)
    rw [CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
    rfl
  rw [show (CliffordAlgebra.equivOfIsometry (sumCoordinateIsometry K σ τ)).symm
      ((CliffordAlgebra.map (QuadraticMap.Isometry.inl _ _)) a) = inlExterior K σ τ a from
      AlgHom.congr_fun h1 a,
    show (CliffordAlgebra.equivOfIsometry (sumCoordinateIsometry K σ τ)).symm
      ((CliffordAlgebra.map (QuadraticMap.Isometry.inr _ _)) b) = inrExterior K σ τ b from
      AlgHom.congr_fun h2 b]

end
end PD4Tensor.Forms

namespace PD4Tensor.Forms
noncomputable section
variable (K σ τ : Type*) [Field K] [DecidableEq σ] [DecidableEq τ]
@[simp] theorem inlExterior_dx (i : σ) :
    inlExterior K σ τ (dx K σ i) = dx K (σ ⊕ τ) (Sum.inl i) := by
  simp only [inlExterior,dx,ExteriorAlgebra.map_apply_ι]
  congr 1
  ext x
  cases x <;> simp [inlCoordinate,Pi.single_apply]
@[simp] theorem inrExterior_dx (j : τ) :
    inrExterior K σ τ (dx K τ j) = dx K (σ ⊕ τ) (Sum.inr j) := by
  simp only [inrExterior,dx,ExteriorAlgebra.map_apply_ι]
  congr 1
  ext x
  cases x <;> simp [inrCoordinate,Pi.single_apply]

theorem involute_map {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (e : ExteriorAlgebra K M) :
    CliffordAlgebra.involute (ExteriorAlgebra.map f e) =
      ExteriorAlgebra.map f (CliffordAlgebra.involute e) := by
  induction e using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | add a b ha hb => simp [ha,hb]
  | mul a b ha hb => simp [ha,hb]
end
end PD4Tensor.Forms
end

end OAI
