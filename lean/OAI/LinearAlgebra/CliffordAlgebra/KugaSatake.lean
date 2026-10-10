import Mathlib

namespace OAI

/-! Rational even-Clifford operators, functorial transport, and their tensor forms in output-first order. -/

namespace KugaSatake

section CliffordOperator

variable {T : Type*} [AddCommGroup T] [Module ℚ T]
variable (q : QuadraticForm ℚ T)

theorem sandwich_mem_even (v w : T) (a : CliffordAlgebra.even q) :
    CliffordAlgebra.ι q v * (a : CliffordAlgebra q) * CliffordAlgebra.ι q w ∈
      CliffordAlgebra.even q := by
  change _ ∈ CliffordAlgebra.evenOdd q 0
  have h := SetLike.mul_mem_graded
    (SetLike.mul_mem_graded (CliffordAlgebra.ι_mem_evenOdd_one q v) a.property)
    (CliffordAlgebra.ι_mem_evenOdd_one q w)
  simpa only [add_zero, show (1 : ZMod 2) + 1 = 0 from rfl] using h

def cliffordOperator (w : T) : T →ₗ[ℚ] Module.End ℚ (CliffordAlgebra.even q) where
  toFun v :=
    { toFun := fun a =>
        ⟨CliffordAlgebra.ι q v * (a : CliffordAlgebra q) * CliffordAlgebra.ι q w,
         sandwich_mem_even q v w a⟩
      map_add' a b := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' c a := Subtype.ext (by simp) }
  map_add' v v' := by
    ext a
    simp [add_mul]
  map_smul' c v := by
    ext a
    simp

@[simp]
theorem cliffordOperator_apply (w v : T) (a : CliffordAlgebra.even q) :
    (cliffordOperator q w v a : CliffordAlgebra q) =
      CliffordAlgebra.ι q v * (a : CliffordAlgebra q) * CliffordAlgebra.ι q w := rfl

theorem clifford_ι_injective : Function.Injective (CliffordAlgebra.ι q) := by
  intro v v' h
  apply (ExteriorAlgebra.ι_inj ℚ v v').mp
  have hh := congrArg (CliffordAlgebra.equivExterior q) h
  simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply] using hh

theorem cliffordOperator_injective (w : T) (hw : q w ≠ 0) :
    Function.Injective (cliffordOperator q w) := by
  intro v v' h
  have he := congrArg
    (fun f : Module.End ℚ (CliffordAlgebra.even q) => (f 1 : CliffordAlgebra q)) h
  simp only [cliffordOperator_apply, OneMemClass.coe_one, mul_one] at he
  have hu : IsUnit (CliffordAlgebra.ι q w) :=
    CliffordAlgebra.isUnit_ι_of_isUnit q (isUnit_iff_ne_zero.mpr hw)
  exact clifford_ι_injective q (hu.mul_left_inj.mp he)

theorem vector_mul_inverse (w : T) (hw : q w ≠ 0) :
    CliffordAlgebra.ι q w * CliffordAlgebra.ι q ((q w)⁻¹ • w) = 1 := by
  rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
    Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hw, map_one]

theorem inverse_mul_vector (w : T) (hw : q w ≠ 0) :
    CliffordAlgebra.ι q ((q w)⁻¹ • w) * CliffordAlgebra.ι q w = 1 := by
  rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
    Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hw, map_one]

def changeRightFactor (w₀ w : T) : CliffordAlgebra.even q :=
  ⟨CliffordAlgebra.ι q ((q w₀)⁻¹ • w₀) * CliffordAlgebra.ι q w,
   CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero q _ _⟩

@[simp]
theorem changeRightFactor_coe (w₀ w : T) :
    (changeRightFactor q w₀ w : CliffordAlgebra q) =
    CliffordAlgebra.ι q ((q w₀)⁻¹ • w₀) * CliffordAlgebra.ι q w := rfl

theorem cliffordOperator_change_right (w₀ w : T) (hw₀ : q w₀ ≠ 0) (v : T) :
    (LinearMap.mulRight ℚ (changeRightFactor q w₀ w)).comp
        (cliffordOperator q w₀ v) = cliffordOperator q w v := by
  ext a
  change (CliffordAlgebra.ι q v * (a : CliffordAlgebra q) * CliffordAlgebra.ι q w₀) *
      (CliffordAlgebra.ι q ((q w₀)⁻¹ • w₀) * CliffordAlgebra.ι q w) = _
  calc
    _ = (CliffordAlgebra.ι q v * (a : CliffordAlgebra q)) *
        (CliffordAlgebra.ι q w₀ * CliffordAlgebra.ι q ((q w₀)⁻¹ • w₀)) *
        CliffordAlgebra.ι q w := by simp only [mul_assoc]
    _ = _ := by rw [vector_mul_inverse q w₀ hw₀, mul_one]; rfl

theorem changeRightFactor_mul_reverse (w₀ w : T) (hw₀ : q w₀ ≠ 0) (hw : q w ≠ 0) :
    changeRightFactor q w₀ w * changeRightFactor q w w₀ = 1 := by
  apply Subtype.ext
  change (CliffordAlgebra.ι q ((q w₀)⁻¹ • w₀) * CliffordAlgebra.ι q w) *
    (CliffordAlgebra.ι q ((q w)⁻¹ • w) * CliffordAlgebra.ι q w₀) = 1
  calc
    _ = CliffordAlgebra.ι q ((q w₀)⁻¹ • w₀) *
      (CliffordAlgebra.ι q w * CliffordAlgebra.ι q ((q w)⁻¹ • w)) *
      CliffordAlgebra.ι q w₀ := by simp only [mul_assoc]
    _ = 1 := by rw [vector_mul_inverse q w hw, mul_one, inverse_mul_vector q w₀ hw₀]

def changeRightUnit (w₀ w : T) (hw₀ : q w₀ ≠ 0) (hw : q w ≠ 0) :
    (CliffordAlgebra.even q)ˣ where
  val := changeRightFactor q w₀ w
  inv := changeRightFactor q w w₀
  val_inv := changeRightFactor_mul_reverse q w₀ w hw₀ hw
  inv_val := changeRightFactor_mul_reverse q w w₀ hw hw₀

end CliffordOperator

section CliffordTransport

variable {T T' : Type*}
  [AddCommGroup T] [Module ℚ T] [AddCommGroup T'] [Module ℚ T']
  {q : QuadraticForm ℚ T} {q' : QuadraticForm ℚ T'}

theorem cliffordMap_mem_even (f : q →qᵢ q') (a : CliffordAlgebra q)
    (ha : a ∈ CliffordAlgebra.even q) :
    CliffordAlgebra.map f a ∈ CliffordAlgebra.even q' := by
  induction a, ha using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact (CliffordAlgebra.even q').algebraMap_mem r
  | add a b ha hb ia ib =>
    rw [map_add]
    exact (CliffordAlgebra.even q').add_mem ia ib
  | ι_mul_ι_mul v w a ha ia =>
    simp only [map_mul, CliffordAlgebra.map_apply_ι]
    exact (CliffordAlgebra.even q').mul_mem
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero q' (f v) (f w)) ia

def evenCliffordMap (f : q →qᵢ q') :
    CliffordAlgebra.even q →ₐ[ℚ] CliffordAlgebra.even q' where
  toFun a := ⟨CliffordAlgebra.map f a, cliffordMap_mem_even f a a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (CliffordAlgebra.map f) (a : CliffordAlgebra q) (b : CliffordAlgebra q))
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add (CliffordAlgebra.map f) (a : CliffordAlgebra q) (b : CliffordAlgebra q))
  commutes' r := Subtype.ext (AlgHom.commutes _ r)

@[simp]
theorem evenCliffordMap_coe (f : q →qᵢ q') (a : CliffordAlgebra.even q) :
    (evenCliffordMap f a : CliffordAlgebra q') =
      CliffordAlgebra.map f (a : CliffordAlgebra q) := rfl

theorem evenCliffordMap_operator (f : q →qᵢ q') (w v : T)
    (a : CliffordAlgebra.even q) :
    evenCliffordMap f (cliffordOperator q w v a) =
      cliffordOperator q' (f w) (f v) (evenCliffordMap f a) := by
  apply Subtype.ext
  simp only [evenCliffordMap_coe, cliffordOperator_apply, map_mul,
    CliffordAlgebra.map_apply_ι]

def evenCliffordEquiv (e : q.IsometryEquiv q') :
    CliffordAlgebra.even q ≃ₐ[ℚ] CliffordAlgebra.even q' :=
  AlgEquiv.ofAlgHom (evenCliffordMap e.toIsometry) (evenCliffordMap e.symm.toIsometry)
    (by
      apply AlgHom.ext
      intro a
      apply Subtype.ext
      change CliffordAlgebra.map e.toIsometry
        (CliffordAlgebra.map e.symm.toIsometry (a : CliffordAlgebra q')) = _
      exact CliffordAlgebra.leftInverse_map_of_leftInverse e.symm.toIsometry e.toIsometry
        (fun v => e.toLinearEquiv.apply_symm_apply v) a)
    (by
      apply AlgHom.ext
      intro a
      apply Subtype.ext
      change CliffordAlgebra.map e.symm.toIsometry
        (CliffordAlgebra.map e.toIsometry (a : CliffordAlgebra q)) = _
      exact CliffordAlgebra.leftInverse_map_of_leftInverse e.toIsometry e.symm.toIsometry
        (fun v => e.toLinearEquiv.symm_apply_apply v) a)

end CliffordTransport

section TensorConversion

open scoped TensorProduct

variable (W : Type*) [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

noncomputable def tensorEndEquiv :
    W ⊗[ℚ] Module.Dual ℚ W ≃ₗ[ℚ] Module.End ℚ W :=
  (TensorProduct.comm ℚ W (Module.Dual ℚ W)).trans (dualTensorHomEquiv ℚ W W)

@[simp]
theorem tensorEndEquiv_tmul_apply (u : W) (f : Module.Dual ℚ W) (a : W) :
    tensorEndEquiv W (u ⊗ₜ[ℚ] f) a = f a • u := rfl

noncomputable def tensorForm (Eflat : W ≃ₗ[ℚ] Module.Dual ℚ W) :
    Module.End ℚ W ≃ₗ[ℚ] W ⊗[ℚ] W :=
  (tensorEndEquiv W).symm.trans
    (TensorProduct.congr (LinearEquiv.refl ℚ W) Eflat.symm)

@[simp]
theorem tensorForm_tensorEndEquiv (Eflat : W ≃ₗ[ℚ] Module.Dual ℚ W)
    (z : W ⊗[ℚ] Module.Dual ℚ W) :
    tensorForm W Eflat (tensorEndEquiv W z) =
      TensorProduct.map LinearMap.id Eflat.symm.toLinearMap z := by
  simp only [tensorForm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

variable {U V : Type*}
  [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
  [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

theorem tensorEndEquiv_naturality (p : U →ₗ[ℚ] V) (i : V →ₗ[ℚ] U)
    (z : U ⊗[ℚ] Module.Dual ℚ U) :
    tensorEndEquiv V (TensorProduct.map p i.dualMap z) =
      p.comp ((tensorEndEquiv U z).comp i) := by
  induction z using TensorProduct.inductionOn with
  | tmul u f =>
    ext a
    simp
  | add z z' hz hz' =>
    simp only [map_add, hz, hz', LinearMap.add_comp, LinearMap.comp_add]

theorem tensorForm_compression (p : U →ₗ[ℚ] V) (i : V →ₗ[ℚ] U)
    (EU : U ≃ₗ[ℚ] Module.Dual ℚ U) (EV : V ≃ₗ[ℚ] Module.Dual ℚ V)
    (f : Module.End ℚ U) :
    TensorProduct.map p (EV.symm.toLinearMap.comp (i.dualMap.comp EU.toLinearMap))
      (tensorForm U EU f) = tensorForm V EV (p.comp (f.comp i)) := by
  obtain ⟨z, rfl⟩ := (tensorEndEquiv U).surjective f
  rw [tensorForm_tensorEndEquiv, ← tensorEndEquiv_naturality,
    tensorForm_tensorEndEquiv]
  induction z using TensorProduct.inductionOn with
  | tmul u f => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem tensorForm_postcomp (E : U ≃ₗ[ℚ] Module.Dual ℚ U)
    (p f : Module.End ℚ U) :
    TensorProduct.map p LinearMap.id (tensorForm U E f) =
      tensorForm U E (p.comp f) := by
  have h := tensorForm_compression p (LinearMap.id : U →ₗ[ℚ] U) E E f
  have hid : E.symm.toLinearMap.comp
      ((LinearMap.id : U →ₗ[ℚ] U).dualMap.comp E.toLinearMap) = LinearMap.id := by
    ext u
    simp
  rw [hid] at h
  simpa only [LinearMap.comp_id] using h

end TensorConversion

section SpecifiedTensor

open scoped TensorProduct

variable {T : Type*} [AddCommGroup T] [Module ℚ T] [FiniteDimensional ℚ T]
variable (q : QuadraticForm ℚ T)

instance clifford_finite : FiniteDimensional ℚ (CliffordAlgebra q) := by
  exact Module.Finite.of_basis
    ((Module.finBasis ℚ T).ExteriorAlgebra.map (CliffordAlgebra.equivExterior q).symm)

instance evenClifford_finite : FiniteDimensional ℚ (CliffordAlgebra.even q) := by
  exact FiniteDimensional.of_injective
    (CliffordAlgebra.even q).val.toLinearMap Subtype.val_injective

noncomputable def cliffordTensor
    (Eflat : CliffordAlgebra.even q ≃ₗ[ℚ] Module.Dual ℚ (CliffordAlgebra.even q))
    (w : T) : T →ₗ[ℚ] CliffordAlgebra.even q ⊗[ℚ] CliffordAlgebra.even q :=
  (tensorForm (CliffordAlgebra.even q) Eflat).toLinearMap.comp (cliffordOperator q w)

@[simp]
theorem cliffordTensor_apply
    (Eflat : CliffordAlgebra.even q ≃ₗ[ℚ] Module.Dual ℚ (CliffordAlgebra.even q))
    (w v : T) :
    cliffordTensor q Eflat w v =
      tensorForm (CliffordAlgebra.even q) Eflat (cliffordOperator q w v) := rfl

theorem cliffordTensor_injective
    (Eflat : CliffordAlgebra.even q ≃ₗ[ℚ] Module.Dual ℚ (CliffordAlgebra.even q))
    (w : T) (hw : q w ≠ 0) : Function.Injective (cliffordTensor q Eflat w) :=
  (tensorForm (CliffordAlgebra.even q) Eflat).injective.comp
    (cliffordOperator_injective q w hw)

theorem cliffordTensor_change_right
    (Eflat : CliffordAlgebra.even q ≃ₗ[ℚ] Module.Dual ℚ (CliffordAlgebra.even q))
    (w₀ w : T) (hw₀ : q w₀ ≠ 0) (v : T) :
    TensorProduct.map (LinearMap.mulRight ℚ (changeRightFactor q w₀ w)) LinearMap.id
      (cliffordTensor q Eflat w₀ v) = cliffordTensor q Eflat w v := by
  rw [cliffordTensor_apply, tensorForm_postcomp, cliffordOperator_change_right q w₀ w hw₀,
    cliffordTensor_apply]

end SpecifiedTensor

end KugaSatake

end OAI
