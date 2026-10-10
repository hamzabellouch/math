import Mathlib
import OAI.Algebra.FiniteTensor.CoordinateEquivalences

namespace OAI

/-! Finite coordinate charts, coefficient extensions and nilpotent deformation equivalences. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K σ τ : Type*) [CommRing K] (e : σ → ℕ) (f : τ → ℕ)

def leftInclusion : Ring K σ e →ₐ[K] Ring K (σ ⊕ τ) (Sum.elim e f) :=
  evaluate (fun i => coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inl i))
    (fun i => coord_pow K (σ ⊕ τ) (Sum.elim e f) (Sum.inl i))

def leftRestriction (hf : ∀ j, 0<f j) :
    Ring K (σ ⊕ τ) (Sum.elim e f) →ₐ[K] Ring K σ e :=
  evaluate (Sum.elim (coord K σ e) (fun _ => 0)) (by
    intro i
    cases i with
    | inl i => exact coord_pow K σ e i
    | inr j => exact zero_pow (Nat.ne_of_gt (hf j)))

@[simp] theorem leftInclusion_coord (i : σ) :
    leftInclusion K σ τ e f (coord K σ e i)=
      coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inl i) := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  exact MvPolynomial.aeval_X _ i

@[simp] theorem leftRestriction_coord (hf : ∀ j, 0<f j) (i : σ ⊕ τ) :
    leftRestriction K σ τ e f hf (coord K (σ ⊕ τ) (Sum.elim e f) i)=
      Sum.elim (coord K σ e) (fun _ => 0) i := by
  exact evaluate_coord _ _ i

def rightIdeal : Ideal (Ring K (σ ⊕ τ) (Sum.elim e f)) :=
  Ideal.span (Set.range (fun j => coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j)))

@[simp] theorem leftRestriction_leftInclusion (hf : ∀ j, 0<f j) (a : Ring K σ e) :
    leftRestriction K σ τ e f hf (leftInclusion K σ τ e f a)=a := by
  have h : (leftRestriction K σ τ e f hf).comp (leftInclusion K σ τ e f)=AlgHom.id K _ := by
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply,leftInclusion_coord,leftRestriction_coord,
      Sum.elim_inl,AlgHom.id_apply]
  exact DFunLike.congr_fun h a

theorem leftRestriction_surjective (hf : ∀ j, 0<f j) :
    Function.Surjective (leftRestriction K σ τ e f hf) := by
  intro a
  exact ⟨leftInclusion K σ τ e f a,leftRestriction_leftInclusion K σ τ e f hf a⟩

 
theorem leftRestriction_ker (hf : ∀ j, 0<f j) :
    RingHom.ker (leftRestriction K σ τ e f hf).toRingHom=rightIdeal K σ τ e f := by
  apply le_antisymm
  · intro a ha
    change leftRestriction K σ τ e f hf a=0 at ha
    have he := error_mem (rightIdeal K σ τ e f)
      ((leftInclusion K σ τ e f).comp (leftRestriction K σ τ e f hf)) (by
        intro i
        cases i with
        | inl i => simp only [AlgHom.comp_apply,leftRestriction_coord,Sum.elim_inl,
            leftInclusion_coord,sub_self,Ideal.zero_mem]
        | inr j =>
          simp only [AlgHom.comp_apply,leftRestriction,evaluate_coord,Sum.elim_inr,
            map_zero,sub_zero]
          exact Ideal.subset_span (Set.mem_range_self j)) a
    simpa only [AlgHom.comp_apply,ha,map_zero,sub_zero] using he
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change leftRestriction K σ τ e f hf (coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j))=0
    simp [leftRestriction]

 

theorem graphRestriction_ker (hf : ∀ j, 0<f j)
    (g : Ring K (σ ⊕ τ) (Sum.elim e f) ≃ₐ[K] Ring K (σ ⊕ τ) (Sum.elim e f)) :
    RingHom.ker ((leftRestriction K σ τ e f hf).comp g.toAlgHom).toRingHom =
      Ideal.span (Set.range (fun j =>
        g.symm (coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j)))) := by
  have hmap : (rightIdeal K σ τ e f).map g.symm.toRingHom =
      Ideal.span (Set.range (fun j =>
        g.symm (coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j)))) := by
    rw [rightIdeal,Ideal.map_span]
    congr 1
    exact Set.range_comp g.symm _ |>.symm
  rw [←hmap]
  ext a
  rw [Ideal.mem_map_iff_of_surjective (g.symm.toRingHom) g.symm.surjective]
  constructor
  · intro ha
    refine ⟨g a,?_,g.symm_apply_apply a⟩
    rw [←leftRestriction_ker K σ τ e f hf]
    exact ha
  · rintro ⟨b,hb,rfl⟩
    change leftRestriction K σ τ e f hf (g (g.symm b))=0
    rw [g.apply_symm_apply]
    rw [←leftRestriction_ker K σ τ e f hf] at hb
    exact hb

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
variable (K σ τ : Type*) [CommRing K] (e : σ → ℕ) (f : τ → ℕ)

def rightInclusion : Ring K τ f →ₐ[K] Ring K (σ ⊕ τ) (Sum.elim e f) :=
  evaluate (fun j => coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j))
    (fun j => coord_pow K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j))

@[simp] theorem rightInclusion_coord (j : τ) :
    rightInclusion K σ τ e f (coord K τ f j)=coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inr j) := by
  change (MvPolynomial.aeval _) (MvPolynomial.X j)=_
  exact MvPolynomial.aeval_X _ j

def toTensor : Ring K (σ ⊕ τ) (Sum.elim e f) →ₐ[K] Ring K σ e ⊗[K] Ring K τ f :=
  evaluate (Sum.elim
    (fun i => Algebra.TensorProduct.includeLeft (R:=K) (S:=K) (coord K σ e i))
    (fun j => Algebra.TensorProduct.includeRight (R:=K) (coord K τ f j))) (by
      intro u
      cases u with
      | inl i => change (Algebra.TensorProduct.includeLeft (R:=K) (S:=K) (coord K σ e i))^e i=0
                 rw [←map_pow,coord_pow,map_zero]
      | inr j => change (Algebra.TensorProduct.includeRight (R:=K) (coord K τ f j))^f j=0
                 rw [←map_pow,coord_pow,map_zero])

def fromTensor : Ring K σ e ⊗[K] Ring K τ f →ₐ[K] Ring K (σ ⊕ τ) (Sum.elim e f) :=
  Algebra.TensorProduct.lift (leftInclusion K σ τ e f) (rightInclusion K σ τ e f)
    (fun _ _ => Commute.all _ _)

@[simp] theorem toTensor_inl (i : σ) :
    toTensor K σ τ e f (coord K (σ ⊕ τ) (Sum.elim e f) (.inl i)) =
      coord K σ e i ⊗ₜ[K] (1 : Ring K τ f) := evaluate_coord _ _ _
@[simp] theorem toTensor_inr (j : τ) :
    toTensor K σ τ e f (coord K (σ ⊕ τ) (Sum.elim e f) (.inr j)) =
      (1 : Ring K σ e) ⊗ₜ[K] coord K τ f j := evaluate_coord _ _ _
@[simp] theorem fromTensor_tmul (a : Ring K σ e) (b : Ring K τ f) :
    fromTensor K σ τ e f (a ⊗ₜ[K] b)=leftInclusion K σ τ e f a * rightInclusion K σ τ e f b := by
  simp [fromTensor]

theorem from_toTensor : (fromTensor K σ τ e f).comp (toTensor K σ τ e f)=AlgHom.id _ _ := by
  apply hom_ext
  intro u
  cases u <;> simp

theorem to_fromTensor : (toTensor K σ τ e f).comp (fromTensor K σ τ e f)=AlgHom.id _ _ := by
  apply Algebra.TensorProduct.ext
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change toTensor K σ τ e f (fromTensor K σ τ e f (coord K σ e i ⊗ₜ[K] 1))=coord K σ e i ⊗ₜ[K] 1
    simp
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change toTensor K σ τ e f (fromTensor K σ τ e f (1 ⊗ₜ[K] coord K τ f j))=1 ⊗ₜ[K] coord K τ f j
    simp

 

def sumTensorEquiv : Ring K (σ ⊕ τ) (Sum.elim e f) ≃ₐ[K] Ring K σ e ⊗[K] Ring K τ f :=
  { toTensor K σ τ e f with
    invFun := fromTensor K σ τ e f
    left_inv := fun a => AlgHom.congr_fun (from_toTensor K σ τ e f) a
    right_inv := fun a => AlgHom.congr_fun (to_fromTensor K σ τ e f) a }

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
variable (K R σ : Type*) [CommRing K] [CommRing R] [Algebra K R] (e : σ → ℕ)

def coefficientMap : Ring K σ e →ₐ[K] Ring R σ e :=
  evaluate (coord R σ e) (coord_pow R σ e)

@[simp] theorem coefficientMap_coord (i : σ) :
    coefficientMap K R σ e (coord K σ e i)=coord R σ e i := evaluate_coord _ _ _

def baseToTensor : Ring R σ e →ₐ[R] R ⊗[K] Ring K σ e :=
  evaluate (fun i => Algebra.TensorProduct.includeRight (A:=R) (coord K σ e i)) (by
    intro i
    rw [←map_pow,coord_pow,map_zero])

def baseFromTensor : R ⊗[K] Ring K σ e →ₐ[R] Ring R σ e :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Ring R σ e)) (coefficientMap K R σ e)
    (fun _ _ => Commute.all _ _)

@[simp] theorem baseToTensor_coord (i : σ) :
    baseToTensor K R σ e (coord R σ e i)=(1 : R) ⊗ₜ[K] coord K σ e i := evaluate_coord _ _ _

@[simp] theorem baseFromTensor_tmul (r : R) (a : Ring K σ e) :
    baseFromTensor K R σ e (r ⊗ₜ[K] a)=r • coefficientMap K R σ e a := by
  change algebraMap R (Ring R σ e) r * coefficientMap K R σ e a=r • coefficientMap K R σ e a
  exact (Algebra.smul_def r _).symm

theorem baseFrom_toTensor :
    (baseFromTensor K R σ e).comp (baseToTensor K R σ e)=AlgHom.id R _ := by
  apply hom_ext
  intro i
  simp

theorem baseTo_fromTensor :
    (baseToTensor K R σ e).comp (baseFromTensor K R σ e)=AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext'
  intro r a
  change baseToTensor K R σ e (baseFromTensor K R σ e (r ⊗ₜ[K] a))=r ⊗ₜ[K] a
  rw [baseFromTensor_tmul,map_smul]
  have h : ((baseToTensor K R σ e).restrictScalars K).comp (coefficientMap K R σ e) =
      Algebra.TensorProduct.includeRight (R:=K) (A:=R) (B:=Ring K σ e) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change baseToTensor K R σ e (coefficientMap K R σ e (coord K σ e i))=(1 : R) ⊗ₜ[K] coord K σ e i
    rw [coefficientMap_coord,baseToTensor_coord]
  have ha := AlgHom.congr_fun h a
  change baseToTensor K R σ e (coefficientMap K R σ e a)=(1 : R) ⊗ₜ[K] a at ha
  rw [ha,TensorProduct.smul_tmul']
  simp

 

def baseChangeEquiv : Ring R σ e ≃ₐ[R] R ⊗[K] Ring K σ e :=
  { baseToTensor K R σ e with
    invFun := baseFromTensor K R σ e
    left_inv := fun a => AlgHom.congr_fun (baseFrom_toTensor K R σ e) a
    right_inv := fun a => AlgHom.congr_fun (baseTo_fromTensor K R σ e) a }

 

def extendEquiv (g : Ring K σ e ≃ₐ[K] Ring K σ e) : Ring R σ e ≃ₐ[R] Ring R σ e :=
  (baseChangeEquiv K R σ e).trans
    ((Algebra.TensorProduct.congr ((AlgEquiv.refl : R ≃ₐ[R] R)) g).trans (baseChangeEquiv K R σ e).symm)

@[simp] theorem extendEquiv_coord (g : Ring K σ e ≃ₐ[K] Ring K σ e) (i : σ) :
    extendEquiv K R σ e g (coord R σ e i)=coefficientMap K R σ e (g (coord K σ e i)) := by
  change baseFromTensor K R σ e
    ((Algebra.TensorProduct.congr ((AlgEquiv.refl : R ≃ₐ[R] R)) g) (baseToTensor K R σ e (coord R σ e i)))=_
  simp

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
variable (K σ τ : Type*) [CommRing K] (e : σ → ℕ) (f : τ → ℕ)

def rightRestriction (he : ∀ i, 0<e i) :
    Ring K (σ ⊕ τ) (Sum.elim e f) →ₐ[K] Ring K τ f :=
  evaluate (Sum.elim (fun _ => 0) (coord K τ f)) (by
    intro i
    cases i with
    | inl i => exact zero_pow (Nat.ne_of_gt (he i))
    | inr j => exact coord_pow K τ f j)

@[simp] theorem rightRestriction_coord (he : ∀ i, 0<e i) (i : σ ⊕ τ) :
    rightRestriction K σ τ e f he (coord K (σ ⊕ τ) (Sum.elim e f) i)=
      Sum.elim (fun _ => 0) (coord K τ f) i := evaluate_coord _ _ _

def leftIdeal : Ideal (Ring K (σ ⊕ τ) (Sum.elim e f)) :=
  Ideal.span (Set.range (fun i => coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inl i)))

theorem rightRestriction_ker (he : ∀ i, 0<e i) :
    RingHom.ker (rightRestriction K σ τ e f he).toRingHom=leftIdeal K σ τ e f := by
  apply le_antisymm
  · intro a ha
    change rightRestriction K σ τ e f he a=0 at ha
    have herr := error_mem (leftIdeal K σ τ e f)
      ((rightInclusion K σ τ e f).comp (rightRestriction K σ τ e f he)) (by
        intro i
        cases i with
        | inl i =>
          simp only [AlgHom.comp_apply,rightRestriction_coord,Sum.elim_inl,map_zero,sub_zero]
          exact Ideal.subset_span (Set.mem_range_self i)
        | inr j =>
          simp only [AlgHom.comp_apply,rightRestriction_coord,Sum.elim_inr,
            rightInclusion_coord,sub_self,Ideal.zero_mem]) a
    simpa only [AlgHom.comp_apply,ha,map_zero,sub_zero] using herr
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change rightRestriction K σ τ e f he (coord K (σ ⊕ τ) (Sum.elim e f) (Sum.inl i))=0
    simp

 

def mixedEquiv : Ring K (σ ⊕ τ) (Sum.elim e f) ≃ₐ[K] Ring (Ring K σ e) τ f :=
  (sumTensorEquiv K σ τ e f).trans
    ((baseChangeEquiv K (Ring K σ e) τ f).symm.restrictScalars K)

@[simp] theorem mixedEquiv_inl (i : σ) :
    mixedEquiv K σ τ e f (coord K (σ ⊕ τ) (Sum.elim e f) (.inl i))=
      algebraMap (Ring K σ e) (Ring (Ring K σ e) τ f) (coord K σ e i) := by
  change baseFromTensor K (Ring K σ e) τ f (toTensor K σ τ e f
    (coord K (σ ⊕ τ) (Sum.elim e f) (.inl i)))=_
  rw [toTensor_inl,baseFromTensor_tmul,map_one]
  exact (Algebra.algebraMap_eq_smul_one (A:=Ring (Ring K σ e) τ f) (coord K σ e i)).symm

@[simp] theorem mixedEquiv_inr (j : τ) :
    mixedEquiv K σ τ e f (coord K (σ ⊕ τ) (Sum.elim e f) (.inr j))=coord (Ring K σ e) τ f j := by
  change baseFromTensor K (Ring K σ e) τ f (toTensor K σ τ e f
    (coord K (σ ⊕ τ) (Sum.elim e f) (.inr j)))=_
  rw [toTensor_inr,baseFromTensor_tmul,one_smul,coefficientMap_coord]

def coefficientSpecialization (he : ∀ i, 0<e i) : Ring (Ring K σ e) τ f →ₐ[K] Ring K τ f :=
  (rightRestriction K σ τ e f he).comp (mixedEquiv K σ τ e f).symm.toAlgHom

@[simp] theorem coefficientSpecialization_coord (he : ∀ i, 0<e i) (j : τ) :
    coefficientSpecialization K σ τ e f he (coord (Ring K σ e) τ f j)=coord K τ f j := by
  rw [←mixedEquiv_inr K σ τ e f j]
  change rightRestriction K σ τ e f he
    ((mixedEquiv K σ τ e f).symm (mixedEquiv K σ τ e f _))=_
  rw [AlgEquiv.symm_apply_apply,rightRestriction_coord]
  rfl

@[simp] theorem coefficientSpecialization_coefficientMap (he : ∀ i, 0<e i) (a : Ring K τ f) :
    coefficientSpecialization K σ τ e f he (coefficientMap K (Ring K σ e) τ f a)=a := by
  have hh : (coefficientSpecialization K σ τ e f he).comp (coefficientMap K (Ring K σ e) τ f)=
      AlgHom.id K _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change coefficientSpecialization K σ τ e f he
      (coefficientMap K (Ring K σ e) τ f (coord K τ f j))=coord K τ f j
    rw [coefficientMap_coord,coefficientSpecialization_coord]
  exact AlgHom.congr_fun hh a

@[simp] theorem coefficientSpecialization_parameter (he : ∀ i, 0<e i) (i : σ) :
    coefficientSpecialization K σ τ e f he
      (algebraMap (Ring K σ e) (Ring (Ring K σ e) τ f) (coord K σ e i))=0 := by
  rw [←mixedEquiv_inl K σ τ e f i]
  change rightRestriction K σ τ e f he
    ((mixedEquiv K σ τ e f).symm (mixedEquiv K σ τ e f _))=0
  rw [AlgEquiv.symm_apply_apply,rightRestriction_coord]
  rfl

def coefficientIdeal : Ideal (Ring (Ring K σ e) τ f) :=
  Ideal.span (Set.range (fun i =>
    algebraMap (Ring K σ e) (Ring (Ring K σ e) τ f) (coord K σ e i)))

 

theorem coefficientSpecialization_ker (he : ∀ i, 0<e i) :
    RingHom.ker (coefficientSpecialization K σ τ e f he).toRingHom=coefficientIdeal K σ τ e f := by
  have hm : (leftIdeal K σ τ e f).map (mixedEquiv K σ τ e f).toRingHom=
      coefficientIdeal K σ τ e f := by
    rw [leftIdeal,coefficientIdeal,Ideal.map_span]
    congr 1
    ext a
    simp only [Set.mem_image,Set.mem_range]
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(mixedEquiv_inl K σ τ e f i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,mixedEquiv_inl K σ τ e f i⟩
  rw [←hm]
  ext a
  rw [Ideal.mem_map_iff_of_surjective (mixedEquiv K σ τ e f).toRingHom (mixedEquiv K σ τ e f).surjective]
  constructor
  · intro ha
    refine ⟨(mixedEquiv K σ τ e f).symm a,?_,(mixedEquiv K σ τ e f).apply_symm_apply a⟩
    rw [←rightRestriction_ker K σ τ e f he]
    exact ha
  · rintro ⟨b,hb,rfl⟩
    change rightRestriction K σ τ e f he
      ((mixedEquiv K σ τ e f).symm (mixedEquiv K σ τ e f b))=0
    rw [AlgEquiv.symm_apply_apply]
    rw [←rightRestriction_ker K σ τ e f he] at hb
    exact hb

theorem coefficientIdeal_nilpotent [Fintype σ] : IsNilpotent (coefficientIdeal K σ τ e f) := by
  have hfg : (coefficientIdeal K σ τ e f).FG := Submodule.fg_span (Set.finite_range _)
  apply hfg.isNilpotent_iff_le_nilradical.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact mem_nilradical.mpr ((show IsNilpotent (coord K σ e i) from ⟨e i,coord_pow K σ e i⟩).map _)

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor
noncomputable section
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

 

theorem bijective_of_nilpotent_deformation {ι : Type*} (z : ι → A)
    (f : A →ₐ[K] A) (c : A ≃ₐ[K] A)
    (hfz : ∀ i, f (z i)=z i) (hcz : ∀ i, c (z i)=z i)
    (he : ∀ a, c a-f a∈Ideal.span (Set.range z))
    (hn : IsNilpotent (Ideal.span (Set.range z))) : Function.Bijective f := by
  let g := f.comp c.symm.toAlgHom
  have hg₀ (a : A) : a-g a∈Ideal.span (Set.range z) := by
    simpa only [g,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply] using he (c.symm a)
  have hg₁ (i : ι) : z i-g (z i)∈Ideal.span (Set.range z)^2 := by
    have hci : c.symm (z i)=z i := by
      apply c.injective
      simp only [c.apply_symm_apply,hcz]
    simp only [g,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,hci,hfz,sub_self]
    exact Ideal.zero_mem _
  obtain ⟨N,hN⟩ := hn
  have hg := bijective_of_identity_tangent (Ideal.span (Set.range z)) g hg₀
    (coordinate_error_on_span z g hg₀ hg₁) N hN
  exact (Function.Bijective.of_comp_iff _ c.symm.bijective).mp hg

end
end PD4Tensor

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable {K σ : Type*} [CommRing K] {e : σ → ℕ}
  {B : Type*} [CommRing B] [Algebra K B]

 

theorem difference_mem (J : Ideal B) (f g : Ring K σ e →ₐ[K] B)
    (hz : ∀ i, f (coord K σ e i)-g (coord K σ e i)∈J) (a : Ring K σ e) :
    f a-g a∈J := by
  refine Quotient.inductionOn' a ?_
  intro q
  change f (Ideal.Quotient.mk (ideal K σ e) q)-g (Ideal.Quotient.mk (ideal K σ e) q)∈J
  induction q using MvPolynomial.induction_on with
  | C c =>
    change f (algebraMap K (Ring K σ e) c)-g (algebraMap K (Ring K σ e) c)∈J
    simp
  | add q r hq hr =>
    simpa only [map_add,add_sub_add_comm] using J.add_mem hq hr
  | mul_X q i hq =>
    change f (Ideal.Quotient.mk _ q * coord K σ e i)-g (Ideal.Quotient.mk _ q * coord K σ e i)∈J
    have h := J.add_mem
      (Ideal.mul_mem_left J (f (Ideal.Quotient.mk (ideal K σ e) q)) (hz i))
      (Ideal.mul_mem_right (g (coord K σ e i)) J hq)
    convert h using 1
    simp only [map_mul]
    ring

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K σ τ : Type*) [CommRing K] [Fintype σ] (e : σ → ℕ) (f : τ → ℕ)

 

theorem bijective_of_central_equiv (he : ∀ i, 0<e i)
    (c : Ring K τ f ≃ₐ[K] Ring K τ f)
    (F : Ring (Ring K σ e) τ f →ₐ[Ring K σ e] Ring (Ring K σ e) τ f)
    (hF : ∀ j, coefficientSpecialization K σ τ e f he (F (coord (Ring K σ e) τ f j))=
      c (coord K τ f j)) : Function.Bijective F := by
  let z (i : σ) := algebraMap (Ring K σ e) (Ring (Ring K σ e) τ f) (coord K σ e i)
  let cE := extendEquiv K (Ring K σ e) τ f c
  apply bijective_of_nilpotent_deformation z F cE
  · intro i
    exact F.commutes _
  · intro i
    exact cE.commutes _
  · intro a
    apply difference_mem (Ideal.span (Set.range z)) cE.toAlgHom F _ a
    intro j
    change cE (coord (Ring K σ e) τ f j)-F (coord (Ring K σ e) τ f j)∈coefficientIdeal K σ τ e f
    rw [←coefficientSpecialization_ker K σ τ e f he]
    change coefficientSpecialization K σ τ e f he
      (cE (coord (Ring K σ e) τ f j)-F (coord (Ring K σ e) τ f j))=0
    rw [map_sub,show cE (coord (Ring K σ e) τ f j)=
      coefficientMap K (Ring K σ e) τ f (c (coord K τ f j)) from extendEquiv_coord _ _ _ _ _ _,
      coefficientSpecialization_coefficientMap,hF,sub_self]
  · exact coefficientIdeal_nilpotent K σ τ e f

end
end PD4Tensor.FiniteCoordinates
end

end OAI
