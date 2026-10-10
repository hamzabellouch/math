import OAI.RepresentationTheory.KazhdanLusztig.Decomposition

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/

section

namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 abbrev SymmetricCoefficient := SymmetricAlgebra ℝ (Extended M)

 def coefficientAction (w : W) : SymmetricCoefficient (M := M) ≃ₐ[ℝ]
    SymmetricCoefficient (M := M) := symmetricAction (extendedAction M cs w)

@[simp] theorem coefficientAction_ι (w : W) (v : Extended M) :
    coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) v) =
      SymmetricAlgebra.ι ℝ (Extended M) (extendedAction M cs w v) :=
  symmetricAction_ι _ _

 theorem coefficientAction_simple (i : I) : coefficientAction cs (cs.simple i) =
    reflectionAction (extendedRoot M i) (extendedForm M (extendedRoot M i))
      (extendedForm_root_self M i) := by
  rw [coefficientAction,extendedAction_simple_eq]

 theorem coefficientAction_mul (w z : W) (a : SymmetricCoefficient (M := M)) :
    coefficientAction cs (w*z) a = coefficientAction cs w (coefficientAction cs z a) := by
  have he : (coefficientAction cs (w*z)).toAlgHom =
      (coefficientAction cs w).toAlgHom.comp (coefficientAction cs z).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change coefficientAction cs (w*z) (SymmetricAlgebra.ι ℝ (Extended M) x) =
      coefficientAction cs w (coefficientAction cs z (SymmetricAlgebra.ι ℝ (Extended M) x))
    simp only [coefficientAction_ι,map_mul,LinearEquiv.mul_apply]
  exact congrArg (fun f : SymmetricCoefficient (M := M) →ₐ[ℝ] SymmetricCoefficient (M := M) => f a) he

 def simpleFixed (i : I) : Subalgebra ℝ (SymmetricCoefficient (M := M)) :=
  fixed (coefficientAction cs (cs.simple i))

 abbrev simpleRootPolynomial (i : I) : SymmetricCoefficient (M := M) :=
  SymmetricAlgebra.ι ℝ (Extended M) (extendedRoot M i)

 theorem simple_involutive (i : I) : Function.Involutive (coefficientAction cs (cs.simple i)) := by
  rw [coefficientAction_simple]
  exact reflectionAction_involutive _ _ _

 theorem simpleRootPolynomial_ne_zero (i : I) : simpleRootPolynomial (M := M) i ≠ 0 :=
  reflectionRoot_ne_zero _ _ (extendedForm_root_self M i)

 theorem simple_anti (i : I) : coefficientAction cs (cs.simple i)
    (simpleRootPolynomial (M := M) i) = -simpleRootPolynomial (M := M) i := by
  rw [coefficientAction_simple]
  exact reflectionAction_anti _ _ _

 theorem simple_divisible (i : I) (a : SymmetricCoefficient (M := M)) :
    simpleRootPolynomial (M := M) i ∣ a-coefficientAction cs (cs.simple i) a := by
  rw [coefficientAction_simple]
  exact reflectionAction_divisible _ _ _ a

 def simpleCoordinates (i : I) : SymmetricCoefficient (M := M) ≃ₗ[simpleFixed cs i]
    (simpleFixed cs i × simpleFixed cs i) :=
  coordinates _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 instance simpleFixed_free (i : I) : Module.Free (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  Module.Free.of_equiv (simpleCoordinates cs i).symm

 instance simpleFixed_finite (i : I) : Module.Finite (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  Module.Finite.equiv (simpleCoordinates cs i).symm

 def simpleTrace (i : I) : SymmetricCoefficient (M := M) →ₗ[simpleFixed cs i] simpleFixed cs i :=
  trace _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 def simpleDuality (i : I) : SymmetricCoefficient (M := M) ≃ₗ[simpleFixed cs i]
    Dual (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  duality _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 theorem simpleDuality_apply (i : I) (a b : SymmetricCoefficient (M := M)) :
    simpleDuality cs i a b = simpleTrace cs i (a*b) :=
  duality_apply _ _ _ _ _ _ a b

end
end KLInvariance.TitsSpace

end


section

/-! Integral restriction and extension of perfect pairings for a genuine
Frobenius extension. This supplies the duality operation used by
Bott--Samelson translation, not an assumed duality on a BMP sheaf. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A)
  (hd : ∀ a b, d a b = tr (a*b))
  (M : Type um) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
noncomputable section

 def restrictDual : Dual A M →ₗ[R] Dual R M where
  toFun f := tr.comp (f.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

 def fiber (f : Dual R M) (m : M) : Dual R A :=
  f.comp ((LinearMap.toSpanSingleton A M m).restrictScalars R)

@[simp] theorem fiber_apply (f : Dual R M) (m : M) (a : A) :
    fiber M f m a = f (a • m) := rfl

include hd in
 theorem trace_recover_fiber (f : Dual R M) (m : M) (a : A) :
    tr (d.symm (fiber M f m) * a) = f (a • m) := by
  rw [← hd,d.apply_symm_apply,fiber_apply]

include hd in
 theorem recover_fiber_smul (f : Dual R M) (m : M) (a : A) :
    d.symm (fiber M f (a • m)) = a * d.symm (fiber M f m) := by
  apply d.injective
  apply LinearMap.ext
  intro b
  rw [d.apply_symm_apply,hd,fiber_apply]
  have he : a * d.symm (fiber M f m) * b = d.symm (fiber M f m) * (b*a) := by ring
  rw [he,trace_recover_fiber tr d hd]
  simp only [mul_smul]

 def recoverDual (f : Dual R M) : Dual A M where
  toFun m := d.symm (fiber M f m)
  map_add' m n := by
    apply d.injective
    rw [map_add,d.apply_symm_apply,d.apply_symm_apply,d.apply_symm_apply]
    ext a
    simp [smul_add]
  map_smul' a m := by
    simpa only [RingHom.id_apply,smul_eq_mul] using recover_fiber_smul tr d hd M f m a

@[simp] theorem recoverDual_apply (f : Dual R M) (m : M) :
    recoverDual tr d hd M f m = d.symm (fiber M f m) := rfl

 theorem restrict_recover (f : Dual R M) :
    restrictDual tr M (recoverDual tr d hd M f) = f := by
  ext m
  change tr (d.symm (fiber M f m)) = f m
  simpa only [mul_one,one_smul] using trace_recover_fiber tr d hd M f m 1

 theorem recover_restrict (f : Dual A M) :
    recoverDual tr d hd M (restrictDual tr M f) = f := by
  ext m
  apply d.injective
  change d (d.symm _) = d (f m)
  rw [d.apply_symm_apply]
  ext a
  change tr (f (a • m)) = d (f m) a
  rw [map_smul,smul_eq_mul,hd,mul_comm]

 def restrictionEquiv : Dual A M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective (restrictDual tr M)
    ⟨fun f g h => by
      have hh := congrArg (recoverDual tr d hd M) h
      simpa only [recover_restrict] using hh,
    fun f => ⟨recoverDual tr d hd M f,restrict_recover tr d hd M f⟩⟩

 theorem restrictionEquiv_apply (f : Dual A M) (m : M) :
    restrictionEquiv tr d hd M f m = tr (f m) := rfl

/-- Restricting an integral perfect pairing along a Frobenius trace is again
integral and perfect; no localization or fraction-field argument is used. -/
 def restrictPairing (p : M ≃ₗ[A] Dual A M) : M ≃ₗ[R] Dual R M :=
  (p.restrictScalars R).trans (restrictionEquiv tr d hd M)

 theorem restrictPairing_apply (p : M ≃ₗ[A] Dual A M) (m n : M) :
    restrictPairing tr d hd M p m n = tr (p m n) := rfl

end
end KLInvariance.FrobeniusDuality

namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
variable {R : Type ur} [CommRing R] (A : Type ua) [CommRing A] [Algebra R A]
  {M : Type um} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
noncomputable section

 def extendPairing (p : M ≃ₗ[R] Dual R M) :
    (A ⊗[R] M) ≃ₗ[A] Dual A (A ⊗[R] M) :=
  (p.baseChange R A M (Dual R M)).trans
    (TensorProduct.isBaseChange (R := R) (S := A) (M := M)).toDualBaseChange

 theorem extendPairing_tmul (p : M ≃ₗ[R] Dual R M) (a b : A) (m n : M) :
    extendPairing A p (a ⊗ₜ[R] m) (b ⊗ₜ[R] n) =
      a * b * algebraMap R A (p m n) := by
  have hn : b ⊗ₜ[R] n = b • (1 ⊗ₜ[R] n) := by simp only [smul_tmul',smul_eq_mul,mul_one]
  rw [hn,map_smul]
  change b * ((TensorProduct.isBaseChange (R := R) (S := A) (M := M)).toDualBaseChange
    (a ⊗ₜ[R] p m) ((TensorProduct.mk R A M 1) n)) = _
  rw [IsBaseChange.toDualBaseChange_tmul]
  ring

end
end KLInvariance.FrobeniusDuality

end


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

structure PairedModule (A : Type ua) [CommRing A] where
  carrier : Type um
  [add : AddCommGroup carrier]
  [module : Module A carrier]
  free : Module.Free A carrier
  finite : Module.Finite A carrier
  pairing : carrier ≃ₗ[A] Dual A carrier

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite
instance {A : Type ua} [CommRing A] : CoeSort (PairedModule.{ua,um} A) (Type um) := ⟨PairedModule.carrier⟩

 def unitPairing (A : Type ua) [CommRing A] : A ≃ₗ[A] Dual A A where
  toFun a := LinearMap.mul A A a
  invFun f := f 1
  left_inv a := mul_one a
  right_inv f := by
    apply LinearMap.ext
    intro a
    change f 1 * a = f a
    rw [mul_comm,← smul_eq_mul,← map_smul,smul_eq_mul,mul_one]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

 def unitModule (A : Type ua) [CommRing A] : PairedModule A where
  carrier := A
  free := inferInstance
  finite := inferInstance
  pairing := unitPairing A

variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A) (hd : ∀ a b, d a b = tr (a*b))
  (N : PairedModule.{ua,um} A)

local instance restrictedModule : Module R N := Module.compHom N (algebraMap R A)
local instance restrictedTower : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

 def restrictionBasis : Basis
    (Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex A N) R N :=
  (Module.Free.chooseBasis R A).smulTower (Module.Free.chooseBasis A N)

local instance restrictedFree : Module.Free R N := Module.Free.of_basis (restrictionBasis N)
local instance restrictedFinite : Module.Finite R N := Module.Finite.trans A N

 def inducedModule : PairedModule A where
  carrier := A ⊗[R] N
  free := inferInstance
  finite := inferInstance
  pairing := extendPairing A (restrictPairing tr d hd N N.pairing)

 theorem inducedModule_pairing_tmul (a b : A) (m n : N) :
    (inducedModule tr d hd N).pairing (a ⊗ₜ[R] m) (b ⊗ₜ[R] n) =
      a*b*algebraMap R A (tr (N.pairing m n)) :=
  extendPairing_tmul A _ a b m n

end
end KLInvariance.FrobeniusDuality

end


section

/-! Integral balanced duality under Bott--Samelson tensor induction. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

structure PairedBimodule (A : Type ua) [CommRing A] where
  obj : PairedModule.{ua,um} A
  right : A →+* End A obj
  balanced : ∀ a m n, obj.pairing (right a m) n = obj.pairing m (right a n)
  symmetric : ∀ m n, obj.pairing m n = obj.pairing n m

 def unitBimodule (A : Type ua) [CommRing A] : PairedBimodule A where
  obj := unitModule A
  right := Algebra.lmul A A |>.toRingHom
  balanced a m n := by
    change A at m n
    change (a*m)*n = m*(a*n)
    ring
  symmetric m n := by
    change A at m n
    exact mul_comm m n

variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A) (hd : ∀ a b, d a b = tr (a*b))
  (N : PairedModule.{ua,um} A)

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def restrictedRight (right : A →+* End A N) : A →+* End R N where
  toFun a := (right a).restrictScalars R
  map_one' := by ext m; change (right 1) m = m; rw [map_one]; rfl
  map_mul' a b := by
    ext m
    change (right (a*b)) m = (right a) ((right b) m)
    rw [map_mul]
    rfl
  map_zero' := by ext m; change (right 0) m = 0; rw [map_zero]; rfl
  map_add' a b := by ext m; change (right (a+b)) m = (right a) m + (right b) m; rw [map_add]; rfl

 def inducedRight (right : A →+* End A N) : A →+* End A (inducedModule tr d hd N) :=
  (Module.End.baseChangeHom R A N).toRingHom.comp (restrictedRight N right)

@[simp] theorem inducedRight_tmul (right : A →+* End A N) (r a : A) (m : N) :
    inducedRight tr d hd N right r (a ⊗ₜ[R] m) = a ⊗ₜ[R] right r m := rfl

 theorem inducedPairing_balanced (right : A →+* End A N)
    (hb : ∀ a m n, N.pairing (right a m) n = N.pairing m (right a n))
    (r : A) (m n : inducedModule tr d hd N) :
    (inducedModule tr d hd N).pairing (inducedRight tr d hd N right r m) n =
      (inducedModule tr d hd N).pairing m (inducedRight tr d hd N right r n) := by
  change A ⊗[R] N at m n
  change extendPairing A (restrictPairing tr d hd N N.pairing)
    (((right r).restrictScalars R).baseChange A m) n =
    extendPairing A (restrictPairing tr d hd N N.pairing) m
    (((right r).restrictScalars R).baseChange A n)
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a m =>
    induction n using TensorProduct.inductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add,h₁,h₂]
    | tmul b n =>
      simp only [LinearMap.baseChange_tmul,extendPairing_tmul,restrictPairing_apply,
        LinearMap.restrictScalars_apply,hb]

 theorem inducedPairing_symmetric (hs : ∀ m n, N.pairing m n = N.pairing n m)
    (m n : inducedModule tr d hd N) :
    (inducedModule tr d hd N).pairing m n = (inducedModule tr d hd N).pairing n m := by
  change A ⊗[R] N at m n
  change extendPairing A (restrictPairing tr d hd N N.pairing) m n =
    extendPairing A (restrictPairing tr d hd N N.pairing) n m
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a m =>
    induction n using TensorProduct.inductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
    | tmul b n =>
      rw [extendPairing_tmul,extendPairing_tmul,restrictPairing_apply,restrictPairing_apply,hs,mul_comm a b]

 def inducedBimodule (N : PairedBimodule.{ua,um} A) : PairedBimodule A where
  obj := inducedModule tr d hd N.obj
  right := inducedRight tr d hd N.obj N.right
  balanced := inducedPairing_balanced tr d hd N.obj N.right N.balanced
  symmetric := inducedPairing_symmetric tr d hd N.obj N.symmetric

end
end KLInvariance.FrobeniusDuality

end


section

/-! Genuine tensor-defined Bott--Samelson bimodules for the extended real
Coxeter realization. The perfect pairing is integral and balanced. This
construction alone does not identify indecomposable BMP summands or prove
the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSamelson : List I → PairedBimodule.{u,u} (SymmetricCoefficient (M := M))
  | [] => unitBimodule _
  | i :: l => inducedBimodule (simpleTrace cs i) (simpleDuality cs i)
    (simpleDuality_apply cs i) (bottSamelson l)

 abbrev BottSamelsonModule (l : List I) := (bottSamelson cs l).obj

 def bottSamelsonDuality (l : List I) : BottSamelsonModule cs l ≃ₗ[SymmetricCoefficient (M := M)]
    Dual (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSamelson cs l).obj.pairing

 def bottSamelsonRight (l : List I) : SymmetricCoefficient (M := M) →+*
    End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSamelson cs l).right

 theorem bottSamelson_balanced (l : List I) (a : SymmetricCoefficient (M := M))
    (m n : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l (bottSamelsonRight cs l a m) n =
      bottSamelsonDuality cs l m (bottSamelsonRight cs l a n) :=
  (bottSamelson cs l).balanced a m n

 theorem bottSamelson_symmetric (l : List I) (m n : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l m n = bottSamelsonDuality cs l n m :=
  (bottSamelson cs l).symmetric m n

end
end KLInvariance.TitsSpace

end


section

/-! The integral reflection trace lowers the actual polynomial grading by one.
This is the graded rank-two Frobenius input, not a BMP character assertion. -/
namespace KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [IsDomain A]
  [Algebra k A] (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedSMul 𝓐 𝓐]

 theorem homogeneous_of_mul {a b : A} {d n : ℤ}
    (ha : a ∈ 𝓐 d) (hne : a ≠ 0) (hab : a*b ∈ 𝓐 n) : b ∈ 𝓐 (n-d) := by
  have hc := component_homogeneous_smul 𝓐 𝓐 d a ha n b
  have he : component 𝓐 n (a*b)=a*b :=
    DirectSum.decompose_of_mem_same 𝓐 hab
  rw [smul_eq_mul,he,smul_eq_mul] at hc
  have hb : b=component 𝓐 (n-d) b := mul_left_cancel₀ hne hc
  rw [hb]
  exact (DirectSum.decompose 𝓐 b (n-d)).property

end KLInvariance.Graded

namespace KLInvariance.ReflectionFrobenius
open KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 theorem trace_difference (a : A) :
    2*α*(trace τ α hinv hα hanti hdiv a : A) = a-τ a := by
  have h := expand_coordinates τ α hinv hα hanti hdiv a
  have ht := congrArg τ h
  simp only [expand_apply,map_add,map_mul,fixed_val,hanti] at h ht
  change 2*α*((coordinates τ α hinv hα hanti hdiv a).2 : A) = a-τ a
  linear_combination h-ht

 theorem trace_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    (trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 (n-1) := by
  apply homogeneous_of_mul 𝓐 hroot hα
  have hd := (𝓐 n).sub_mem ha (hτ n a ha)
  have hal := (𝓐 n).smul_mem ((2:k)⁻¹) hd
  have ht := trace_difference τ α hinv hα hanti hdiv a
  have htwo : (2:A)*algebraMap k A ((2:k)⁻¹) = 1 := by
    rw [show (2:A)=algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp
  have he : α*(trace τ α hinv hα hanti hdiv a : A) =
      (2:k)⁻¹ • (a-τ a) := by
    rw [Algebra.smul_def]
    linear_combination (algebraMap k A ((2:k)⁻¹))*ht -
      (α*(trace τ α hinv hα hanti hdiv a : A))*htwo
  exact he ▸ hal

 theorem coordinates_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    ((coordinates τ α hinv hα hanti hdiv a).1 : A) ∈ 𝓐 n ∧
    ((coordinates τ α hinv hα hanti hdiv a).2 : A) ∈ 𝓐 (n-1) := by
  have ht := trace_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot hτ ha
  constructor
  · have hp : α*(trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 n := by
      simpa only [smul_eq_mul,vadd_eq_add,show (1:ℤ)+(n-1)=n by omega] using
        SetLike.GradedSMul.smul_mem hroot ht
    have he : ((coordinates τ α hinv hα hanti hdiv a).1 : A) =
        a-α*(trace τ α hinv hα hanti hdiv a : A) := by
      have h := expand_coordinates τ α hinv hα hanti hdiv a
      change ((coordinates τ α hinv hα hanti hdiv a).1 : A) +
        α*(trace τ α hinv hα hanti hdiv a : A)=a at h
      linear_combination h
    exact he ▸ (𝓐 n).sub_mem ha hp
  · exact ht

end
end KLInvariance.ReflectionFrobenius

end


section

/-! The actual two-element homogeneous basis of a reflection Frobenius
extension. This basis is used in the tensor-defined Bott--Samelson modules. -/
namespace KLInvariance.ReflectionFrobenius
open Module
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 def reflectionBasis : Basis (Fin 2) (fixed τ) A :=
  (Basis.finTwoProd (fixed τ)).map (coordinates τ α hinv hα hanti hdiv).symm

 theorem reflectionBasis_zero : reflectionBasis τ α hinv hα hanti hdiv 0 = 1 := by
  change expand τ α (Basis.finTwoProd (fixed τ) 0) = 1
  simp [expand_apply]

 theorem reflectionBasis_one : reflectionBasis τ α hinv hα hanti hdiv 1 = α := by
  change expand τ α (Basis.finTwoProd (fixed τ) 1) = α
  simp [expand_apply]

 theorem reflectionBasis_homogeneous (𝓐 : ℤ → Submodule k A)
    [SetLike.GradedOne 𝓐] (hroot : α ∈ 𝓐 1) (i : Fin 2) :
    reflectionBasis τ α hinv hα hanti hdiv i ∈ 𝓐 (i.val : ℤ) := by
  fin_cases i
  · change reflectionBasis τ α hinv hα hanti hdiv (0 : Fin 2) ∈ 𝓐 0
    rw [reflectionBasis_zero]
    exact SetLike.one_mem_graded 𝓐
  · change reflectionBasis τ α hinv hα hanti hdiv (1 : Fin 2) ∈ 𝓐 1
    rw [reflectionBasis_one]
    exact hroot

end
end KLInvariance.ReflectionFrobenius

end


section

/-! Homogeneous integral Bott--Samelson pairing at the genuine tensor basis.
No indecomposable summand or character identity is postulated here. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct ReflectionFrobenius
universe uk ua um ui
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

variable [Module.Free (fixed τ) A] [Module.Finite (fixed τ) A]

variable (N : PairedModule.{ua,um} A)
  {ι : Type ui} (b : Basis ι A N)
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def inducedBasis : Basis (Fin 2 × ι) A
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N) :=
  ((reflectionBasis τ α hinv hα hanti hdiv).smulTower b).baseChange A

 theorem inducedBasis_apply (i : Fin 2) (j : ι) :
    inducedBasis τ α hinv hα hanti hdiv N b (i,j) =
      (1:A) ⊗ₜ[fixed τ] (reflectionBasis τ α hinv hα hanti hdiv i • b j) := by
  change (((reflectionBasis τ α hinv hα hanti hdiv).smulTower b).baseChange A) (i,j) = _
  rw [Basis.baseChange_apply,Basis.smulTower_apply]

 theorem inducedPairing_basis (i i' : Fin 2) (j j' : ι) :
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N).pairing
      (inducedBasis τ α hinv hα hanti hdiv N b (i,j))
      (inducedBasis τ α hinv hα hanti hdiv N b (i',j')) =
      (trace τ α hinv hα hanti hdiv
        (reflectionBasis τ α hinv hα hanti hdiv i *
          reflectionBasis τ α hinv hα hanti hdiv i' * N.pairing (b j) (b j')) : A) := by
  rw [inducedBasis_apply,inducedBasis_apply]
  let : Module.Free (fixed τ) N := Module.Free.of_basis
    ((reflectionBasis τ α hinv hα hanti hdiv).smulTower b)
  let : Module.Finite (fixed τ) N := Module.Finite.trans A N
  change extendPairing A (restrictPairing (trace τ α hinv hα hanti hdiv)
    (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N N.pairing) _ _ = _
  rw [extendPairing_tmul,restrictPairing_apply]
  simp only [one_mul]
  change ((trace τ α hinv hα hanti hdiv _) : A) = _
  apply congrArg Subtype.val
  apply congrArg (trace τ α hinv hα hanti hdiv)
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

 theorem inducedPairing_basis_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    (d : ι → ℤ) (l : ℤ)
    (hb : ∀ j j', N.pairing (b j) (b j') ∈ 𝓐 (d j+d j'-l))
    (i i' : Fin 2) (j j' : ι) :
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N).pairing
      (inducedBasis τ α hinv hα hanti hdiv N b (i,j))
      (inducedBasis τ α hinv hα hanti hdiv N b (i',j')) ∈
      𝓐 ((i.val+d j)+(i'.val+d j')-(l+1)) := by
  rw [inducedPairing_basis]
  have h := trace_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot hτ
    (SetLike.GradedMul.mul_mem
      (SetLike.GradedMul.mul_mem
        (reflectionBasis_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot i)
        (reflectionBasis_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot i'))
      (hb j j'))
  convert h using 1
  congr 1
  omega

end
end KLInvariance.FrobeniusDuality

end


section

namespace KLInvariance.Graded
universe uk us
variable {k : Type uk} [Field k] {σ : Type us}

 theorem algHom_polynomialGrading (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ polynomialGrading k σ 1)
    {n : ℤ} {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    f p ∈ polynomialGrading k σ n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (polynomialGrading k σ n).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (polynomialGrading k σ n).add_mem hp hq
  | monomial d c hd =>
    rw [MvPolynomial.monomial_eq,map_mul]
    have hc : f (MvPolynomial.C c)=MvPolynomial.C c := f.commutes c
    rw [hc]
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    simp only [Finsupp.prod,map_prod,map_pow]
    have hh := SetLike.prod_pow_mem_graded (polynomialGrading k σ)
      (fun _ : σ => (1:ℤ)) (fun i => f (MvPolynomial.X i)) d (F := d.support)
      (fun i _ => hX i)
    simpa only [Finsupp.weight_apply,Finsupp.sum] using hd ▸ hh

end KLInvariance.Graded

namespace KLInvariance.ReflectionFrobenius
open Module KLInvariance.Graded
universe uk uv us
variable {k : Type uk} [Field k] [CharZero k]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {σ : Type us} [Fintype σ] (basis : Basis σ k V)
noncomputable section

 def polynomialLinear (v : V) : MvPolynomial σ k :=
  SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V v)

omit [CharZero k] in
 theorem polynomialLinear_homogeneous (v : V) :
    polynomialLinear basis v ∈ polynomialGrading k σ 1 := by
  classical
  unfold polynomialLinear
  rw [← basis.sum_repr v]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading k σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => (1:ℤ)) i)

 def polynomialAction (e : V ≃ₗ[k] V) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  ((SymmetricAlgebra.equivMvPolynomial basis).symm.trans (symmetricAction e)).trans
    (SymmetricAlgebra.equivMvPolynomial basis)

omit [CharZero k] [Fintype σ] in
@[simp] theorem polynomialAction_linear (e : V ≃ₗ[k] V) (v : V) :
    polynomialAction basis e (polynomialLinear basis v) = polynomialLinear basis (e v) := by
  simp [polynomialAction,polynomialLinear]

omit [CharZero k] in
 theorem polynomialAction_homogeneous (e : V ≃ₗ[k] V) {n : ℤ}
    {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    polynomialAction basis e p ∈ polynomialGrading k σ n := by
  apply algHom_polynomialGrading (polynomialAction basis e).toAlgHom _ hp
  intro i
  change polynomialAction basis e (MvPolynomial.X i) ∈ _
  have hx : MvPolynomial.X i = polynomialLinear basis (basis i) := by
    simp [polynomialLinear]
  rw [hx,polynomialAction_linear]
  exact polynomialLinear_homogeneous basis _

variable (root : V) (coroot : Dual k V) (hroot : coroot root=2)

 abbrev polynomialReflection : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  polynomialAction basis (Module.reflection hroot)

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_involutive : Function.Involutive
    (polynomialReflection basis root coroot hroot) := by
  intro p
  change SymmetricAlgebra.equivMvPolynomial basis
    (reflectionAction root coroot hroot
      ((SymmetricAlgebra.equivMvPolynomial basis).symm
        (SymmetricAlgebra.equivMvPolynomial basis
          (reflectionAction root coroot hroot
            ((SymmetricAlgebra.equivMvPolynomial basis).symm p)))))=p
  rw [AlgEquiv.symm_apply_apply,reflectionAction_involutive,AlgEquiv.apply_symm_apply]

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_anti : polynomialReflection basis root coroot hroot
    (polynomialLinear basis root) = -polynomialLinear basis root := by
  change SymmetricAlgebra.equivMvPolynomial basis
    (reflectionAction root coroot hroot
      ((SymmetricAlgebra.equivMvPolynomial basis).symm
        (SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V root)))) = _
  rw [AlgEquiv.symm_apply_apply,reflectionAction_anti,map_neg]
  rfl

omit [Fintype σ] in
include coroot hroot in
 theorem polynomialLinear_ne_zero : polynomialLinear basis root ≠ 0 := by
  intro h
  apply reflectionRoot_ne_zero root coroot hroot
  exact (SymmetricAlgebra.equivMvPolynomial basis).injective (by simpa [polynomialLinear] using h)

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_divisible (p : MvPolynomial σ k) :
    polynomialLinear basis root ∣ p-polynomialReflection basis root coroot hroot p := by
  obtain ⟨d,hd⟩ := reflectionAction_divisible root coroot hroot
    ((SymmetricAlgebra.equivMvPolynomial basis).symm p)
  refine ⟨SymmetricAlgebra.equivMvPolynomial basis d,?_⟩
  simpa [polynomialLinear,polynomialReflection,polynomialAction] using
    congrArg (SymmetricAlgebra.equivMvPolynomial basis) hd

 def polynomialTrace : MvPolynomial σ k →ₗ[fixed (polynomialReflection basis root coroot hroot)]
    fixed (polynomialReflection basis root coroot hroot) :=
  trace _ _ (polynomialReflection_involutive basis root coroot hroot)
    (polynomialLinear_ne_zero basis root coroot hroot)
    (polynomialReflection_anti basis root coroot hroot)
    (polynomialReflection_divisible basis root coroot hroot)

 theorem polynomialTrace_homogeneous {n : ℤ} {p : MvPolynomial σ k}
    (hp : p ∈ polynomialGrading k σ n) :
    (polynomialTrace basis root coroot hroot p : MvPolynomial σ k) ∈ polynomialGrading k σ (n-1) :=
  trace_homogeneous _ _ _ _ _ _ (polynomialGrading k σ)
    (polynomialLinear_homogeneous basis root)
    (fun _ _ h => polynomialAction_homogeneous basis (Module.reflection hroot) h) hp

end
end KLInvariance.ReflectionFrobenius

end


section

/-! The genuine symmetric-algebra grading of the extended real realization,
transported along a specified realization basis only to access polynomial
homogeneous components. The algebra and action are unchanged. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionFrobenius
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def symmetricGrading : ℤ → Submodule ℝ (SymmetricCoefficient (M := M)) :=
  fun n => (polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap

omit [Fintype σ] in
 theorem mem_symmetricGrading (n : ℤ) (a : SymmetricCoefficient (M := M)) :
    a ∈ symmetricGrading basis n ↔
      SymmetricAlgebra.equivMvPolynomial basis a ∈ polynomialGrading ℝ σ n := by
  constructor
  · rintro ⟨p,hp,hpa⟩
    rw [← hpa]
    simpa using hp
  · intro h
    exact ⟨_,h,(SymmetricAlgebra.equivMvPolynomial basis).symm_apply_apply a⟩

 instance symmetricGrading_decomposition : DirectSum.Decomposition (symmetricGrading basis) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply image_isInternal (polynomialGrading ℝ σ)
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap
    (SymmetricAlgebra.equivMvPolynomial basis).symm.surjective
  intro n p hp
  have hz : p=0 := (SymmetricAlgebra.equivMvPolynomial basis).symm.injective
    (by simpa using hp)
  subst p
  simp

 instance symmetricGrading_graded : SetLike.GradedMonoid (symmetricGrading basis) where
  one_mem := (mem_symmetricGrading basis 0 1).mpr (by
    rw [map_one]
    exact SetLike.one_mem_graded (polynomialGrading ℝ σ))
  mul_mem := by
    intro n m a b ha hb
    apply (mem_symmetricGrading basis (n+m) (a*b)).mpr
    rw [map_mul]
    exact SetLike.GradedMul.mul_mem ((mem_symmetricGrading basis n a).mp ha)
      ((mem_symmetricGrading basis m b).mp hb)

omit [Fintype σ] in
 theorem symmetricGrading_negative (n : ℤ) (hn : n<0) :
    symmetricGrading basis n = ⊥ := by
  simp [symmetricGrading,polynomialGrading_negative ℝ σ n hn]

 theorem simpleRoot_homogeneous (i : I) :
    simpleRootPolynomial (M := M) i ∈ symmetricGrading basis 1 := by
  apply (mem_symmetricGrading basis 1 _).mpr
  exact polynomialLinear_homogeneous basis _

 theorem coefficientAction_homogeneous (w : W) (n : ℤ)
    (a : SymmetricCoefficient (M := M)) (ha : a ∈ symmetricGrading basis n) :
    coefficientAction cs w a ∈ symmetricGrading basis n := by
  apply (mem_symmetricGrading basis n _).mpr
  have h := polynomialAction_homogeneous basis (extendedAction M cs w)
    ((mem_symmetricGrading basis n a).mp ha)
  simpa only [polynomialAction,AlgEquiv.trans_apply,AlgEquiv.symm_apply_apply,
    coefficientAction] using h

end
end KLInvariance.TitsSpace

end


section

/-! A grading defined by an actual homogeneous free basis, with an explicit
coefficient test. Used to put the genuine grading on tensor Bott--Samelsons. -/
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {ι : Type ui} [Fintype ι] (b : Basis ι A N) (d : ι → ℤ)
noncomputable section

 def basisPiece (n : ℤ) : Submodule k N :=
  (shiftedPiece 𝓐 d n).comap (b.equivFun.restrictScalars k).toLinearMap

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
 theorem mem_basisPiece (n : ℤ) (m : N) :
    m ∈ basisPiece 𝓐 b d n ↔ ∀ i, b.repr m i ∈ 𝓐 (n-d i) := Iff.rfl

 instance basisPiece_decomposition : DirectSum.Decomposition (basisPiece 𝓐 b d) := by
  let _ : DirectSum.Decomposition (shiftedPiece 𝓐 d) := (shifted_isInternal 𝓐 d).chooseDecomposition
  apply DirectSum.IsInternal.chooseDecomposition
  have he : basisPiece 𝓐 b d = fun n => (shiftedPiece 𝓐 d n).map
      (b.equivFun.restrictScalars k).symm.toLinearMap := by
    funext n
    exact Submodule.comap_equiv_eq_map_symm _ _
  rw [he]
  apply image_isInternal (shiftedPiece 𝓐 d)
    (b.equivFun.restrictScalars k).symm.toLinearMap
    (b.equivFun.restrictScalars k).symm.surjective
  intro n m hm
  have hz : m=0 := (b.equivFun.restrictScalars k).symm.injective (by simpa using hm)
  subst m
  simp

 instance basisPiece_graded : SetLike.GradedSMul 𝓐 (basisPiece 𝓐 b d) where
  smul_mem := by
    intro n m a x ha hx i
    change b.repr (a • x) i ∈ 𝓐 ((n+m)-d i)
    rw [map_smul,Finsupp.smul_apply,smul_eq_mul]
    change ∀ i, b.repr x i ∈ 𝓐 (m-d i) at hx
    have h := SetLike.GradedMul.mul_mem ha (hx i)
    simpa only [add_sub_assoc] using h

omit [DirectSum.Decomposition 𝓐] in
 theorem basis_mem_piece (i : ι) : b i ∈ basisPiece 𝓐 b d (d i) := by
  classical
  intro j
  change b.repr (b i) j ∈ 𝓐 (d i-d j)
  by_cases hij : i=j
  · subst j
    simp only [Basis.repr_self,Finsupp.single_eq_same,sub_self]
    exact SetLike.one_mem_graded 𝓐
  · rw [Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hij)]
    exact Submodule.zero_mem _

omit [DirectSum.Decomposition 𝓐] in
 theorem pairing_homogeneous (p : N →ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n m : ℤ} {x y : N} (hx : x ∈ basisPiece 𝓐 b d n)
    (hy : y ∈ basisPiece 𝓐 b d m) : p x y ∈ 𝓐 (n+m-l) := by
  classical
  have hexp : p x y = ∑ i, ∑ j,
      b.repr x i * b.repr y j * p (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr x,← b.sum_repr y]
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,
      Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  change ∀ i, b.repr x i ∈ 𝓐 (n-d i) at hx
  change ∀ i, b.repr y i ∈ 𝓐 (m-d i) at hy
  have h := SetLike.GradedMul.mul_mem
    (SetLike.GradedMul.mul_mem (hx i) (hy j)) (hp i j)
  convert h using 1
  congr 1
  omega

end
end KLInvariance.Graded

end


section

/-! The actual tensor-defined Bott--Samelson module has the word grading and
its integral duality lowers degree by word length (degree-one roots).
This does not identify an indecomposable summand with the BMP sheaf. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def BottIndex : List I → Type u
  | [] => PUnit
  | _ :: l => Fin 2 × BottIndex l

 instance bottIndex_fintype : (l : List I) → Fintype (BottIndex l)
  | [] => inferInstanceAs (Fintype PUnit)
  | _ :: l => by
      let _ := bottIndex_fintype l
      exact inferInstanceAs (Fintype (Fin 2 × BottIndex l))

 def bottDegree : (l : List I) → BottIndex l → ℤ
  | [], _ => 0
  | _ :: l, e => e.1.val + bottDegree l e.2

omit [Fintype I] in
 theorem bottDegree_nonneg (l : List I) (e : BottIndex l) : 0 ≤ bottDegree l e := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact add_nonneg (Int.natCast_nonneg _) (ih e.2)

 def bottBasis : (l : List I) → Basis (BottIndex l) (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l)
  | [] => Basis.singleton PUnit _
  | i :: l => by
      let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
        simpleFixed_free cs i
      let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
        simpleFixed_finite cs i
      exact inducedBasis (coefficientAction cs (cs.simple i))
        (simpleRootPolynomial i) (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
        (simple_anti cs i) (simple_divisible cs i) (bottSamelson cs l).obj (bottBasis l)

 theorem bottBasis_pairing_homogeneous (l : List I) (e f : BottIndex l) :
    bottSamelsonDuality cs l (bottBasis cs l e) (bottBasis cs l f) ∈
      symmetricGrading basis (bottDegree l e+bottDegree l f-l.length) := by
  induction l with
  | nil =>
    change PUnit at e f
    change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) e) *
      (Basis.singleton PUnit (SymmetricCoefficient (M := M)) f) ∈ symmetricGrading basis 0
    simp only [Basis.singleton_apply, one_mul]
    exact SetLike.one_mem_graded _
  | cons i l ih =>
    change (Fin 2 × BottIndex l) at e f
    rcases e with ⟨ei, ej⟩
    rcases f with ⟨fi, fj⟩
    let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
      simpleFixed_free cs i
    let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
      simpleFixed_finite cs i
    have h := inducedPairing_basis_homogeneous
      (coefficientAction cs (cs.simple i)) (simpleRootPolynomial i)
      (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
      (simple_anti cs i) (simple_divisible cs i) (bottSamelson cs l).obj
      (bottBasis cs l) (symmetricGrading basis) (simpleRoot_homogeneous basis i)
      (coefficientAction_homogeneous cs basis (cs.simple i))
      (bottDegree l) l.length ih ei fi ej fj
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,bottDegree]
    convert h using 1; rfl

 instance bottRealModule (l : List I) : Module ℝ (BottSamelsonModule cs l) :=
  Module.compHom _ (algebraMap ℝ (SymmetricCoefficient (M := M)))

 instance bottRealTower (l : List I) :
    IsScalarTower ℝ (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

 def bottPiece (l : List I) : ℤ → Submodule ℝ (BottSamelsonModule cs l) :=
  basisPiece (symmetricGrading basis) (bottBasis cs l) (bottDegree l)

 instance bottPiece_decomposition (l : List I) : DirectSum.Decomposition (bottPiece cs basis l) :=
  basisPiece_decomposition _ _ _

 instance bottPiece_graded (l : List I) :
    SetLike.GradedSMul (symmetricGrading basis) (bottPiece cs basis l) :=
  basisPiece_graded _ _ _

 theorem bottDuality_homogeneous (l : List I) {n m : ℤ}
    {x y : BottSamelsonModule cs l} (hx : x ∈ bottPiece cs basis l n)
    (hy : y ∈ bottPiece cs basis l m) :
    bottSamelsonDuality cs l x y ∈ symmetricGrading basis (n+m-l.length) := by
  exact pairing_homogeneous (symmetricGrading basis) (bottBasis cs l) (bottDegree l)
    (bottSamelsonDuality cs l).toLinearMap l.length
    (bottBasis_pairing_homogeneous cs basis l) hx hy

end
end KLInvariance.TitsSpace

end


section

/-! Actual subexpression-weight coordinates of the tensor Bott--Samelson
module, and the genuine right-action eigenvalue. These are the localization
maps required for moment-sheaf realization; no character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v un
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem coefficientAction_one (a : SymmetricCoefficient (M := M)) :
    coefficientAction cs 1 a = a := by
  have h := coefficientAction_mul cs 1 1 a
  rw [one_mul] at h
  exact (coefficientAction cs 1).injective h.symm

 def bottWeight : (l : List I) → BottIndex l → W
  | [], _ => 1
  | i::l, e => if e.1=0 then bottWeight l e.2 else cs.simple i*bottWeight l e.2

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def weightFunctional (i : I) (N : PairedModule.{u,un} (SymmetricCoefficient (M := M)))
    (f : N →ₗ[SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M))
    (ε : Fin 2) : N →ₗ[simpleFixed cs i] SymmetricCoefficient (M := M) where
  toFun m := if ε=0 then f m else coefficientAction cs (cs.simple i) (f m)
  map_add' m n := by split_ifs <;> simp only [map_add]
  map_smul' c m := by
    change (if ε=0 then f ((c:SymmetricCoefficient (M:=M)) • m) else
      coefficientAction cs (cs.simple i) (f ((c:SymmetricCoefficient (M:=M)) • m))) = _
    split_ifs
    · simp only [map_smul,Subalgebra.smul_def,RingHom.id_apply]
    · rw [map_smul]
      change coefficientAction cs (cs.simple i)
        ((c:SymmetricCoefficient (M:=M))*f m) =
        (c:SymmetricCoefficient (M:=M))*coefficientAction cs (cs.simple i) (f m)
      rw [map_mul, show coefficientAction cs (cs.simple i) (c:SymmetricCoefficient (M:=M)) = c from c.property]

 def inducedFunctional (i : I) (N : PairedModule.{u,un} (SymmetricCoefficient (M := M)))
    (f : N →ₗ[simpleFixed cs i] SymmetricCoefficient (M := M)) :
    (SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] N) →ₗ[SymmetricCoefficient (M := M)]
      SymmetricCoefficient (M := M) :=
  AlgebraTensorModule.lift ((LinearMap.id : SymmetricCoefficient (M := M) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)).smulRight f)

 def bottEvaluation : (l : List I) → BottIndex l →
    BottSamelsonModule cs l →ₗ[SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)
  | [], _ => LinearMap.id
  | i::l, e => inducedFunctional cs i (bottSamelson cs l).obj
      (weightFunctional cs i (bottSamelson cs l).obj (bottEvaluation l e.2) e.1)

 theorem bottEvaluation_tmul (i : I) (l : List I) (e : BottIndex (i::l))
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottEvaluation cs (i::l) e (a ⊗ₜ[simpleFixed cs i] m) =
      a*(if e.1=0 then bottEvaluation cs l e.2 m else
        coefficientAction cs (cs.simple i) (bottEvaluation cs l e.2 m)) := rfl

 theorem bottEvaluation_right (l : List I) (e : BottIndex l)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottEvaluation cs l e (bottSamelsonRight cs l a m) =
      coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e m := by
  induction l with
  | nil =>
    change SymmetricCoefficient (M := M) at m
    change a*m = coefficientAction cs 1 a * m
    rw [coefficientAction_one]
  | cons i l ih =>
    change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
    induction m using TensorProduct.inductionOn with
    | add m n hm hn => erw [map_add,map_add,map_add,hm,hn,mul_add]
    | tmul b m =>
      change bottEvaluation cs (i::l) e (b ⊗ₜ[simpleFixed cs i] bottSamelsonRight cs l a m) = _
      erw [bottEvaluation_tmul,bottEvaluation_tmul,ih]
      change b*(if e.1=0 then _ else _) = coefficientAction cs
        (if e.1=0 then bottWeight cs l e.2 else cs.simple i*bottWeight cs l e.2) a * _
      split_ifs with h
      · ring
      · rw [map_mul,coefficientAction_mul]
        ring

end
end KLInvariance.TitsSpace

end


section

/-! Localization coordinates for tensor induction over a reflection wall.
This is an integral injectivity argument, not character normalization. -/
namespace KLInvariance.ReflectionFrobenius
open scoped Matrix
universe ua ui
variable {A : Type ua} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type ui} [Fintype ι] (τ : A ≃+* A) (α : A)
noncomputable section

 def wallCoordinate (E : Matrix ι ι A) (v : Fin 2 × ι → A) : Fin 2 × ι → A := fun e =>
  if e.1=0 then (E *ᵥ (fun j => v (0,j)+α*v (1,j))) e.2
  else ((E.map τ) *ᵥ (fun j => v (0,j)-α*v (1,j))) e.2

 def wallMatrix (E : Matrix ι ι A) : Matrix (Fin 2 × ι) (Fin 2 × ι) A := fun e f =>
  if e.1=0 then (if f.1=0 then E e.2 f.2 else α*E e.2 f.2)
  else if f.1=0 then τ (E e.2 f.2) else -α*τ (E e.2 f.2)

omit [IsDomain A] [CharZero A] in
 theorem wallMatrix_mulVec (E : Matrix ι ι A) (v : Fin 2 × ι → A) :
    wallMatrix τ α E *ᵥ v = wallCoordinate τ α E v := by
  classical
  funext ⟨r,j⟩
  change (∑ c : Fin 2 × ι, wallMatrix τ α E (r,j) c * v c) = _
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  fin_cases r <;>
    simp [wallMatrix,wallCoordinate,Matrix.mulVec,dotProduct,
      Finset.sum_add_distrib,mul_add,
      mul_left_comm,mul_assoc,sub_eq_add_neg]

omit [IsDomain A] [CharZero A] in
 theorem matrixTwist_injective (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (Matrix.mulVec (E.map τ)) := by
  intro v w hv
  have hh : E *ᵥ (fun j => τ.symm (v j)) = E *ᵥ (fun j => τ.symm (w j)) := by
    funext i
    have h := congrArg τ.symm (congrFun hv i)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply,
      RingEquiv.symm_apply_apply] using h
  have hh' := hE hh
  funext i
  exact τ.symm.injective (congrFun hh' i)

 theorem wallCoordinate_injective (hα : α ≠ 0) (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (wallCoordinate τ α E) := by
  intro v w hv
  have h₀ : (fun j => v (0,j)+α*v (1,j)) = (fun j => w (0,j)+α*w (1,j)) := by
    apply hE
    funext j
    simpa only [wallCoordinate,ite_eq_left rfl,ite_true] using congrFun hv (0,j)
  have h₁ : (fun j => v (0,j)-α*v (1,j)) = (fun j => w (0,j)-α*w (1,j)) := by
    apply matrixTwist_injective τ E hE
    funext j
    simpa only [wallCoordinate,show (1:Fin 2) ≠ 0 by decide,ite_false] using congrFun hv (1,j)
  funext ⟨ε,j⟩
  have h0 := congrFun h₀ j
  have h1 := congrFun h₁ j
  have hi1 : v (1,j)=w (1,j) := by
    have hh : (2:A)*α*(v (1,j)-w (1,j))=0 := by linear_combination h0-h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero two_ne_zero hα))
  have hi0 : v (0,j)=w (0,j) := by simpa only [hi1,add_left_inj] using h0
  fin_cases ε
  · exact hi0
  · exact hi1

end
end KLInvariance.ReflectionFrobenius

end


section

/-! The actual tensor Bott--Samelson module embeds integrally in its individual
subexpression coordinates. Together with the checked weight eigenvalue this
identifies its generic support. It does not assert the integral moment-sheaf
recognition or the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open scoped Matrix
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottEvaluationMatrix (l : List I) : Matrix (BottIndex l) (BottIndex l)
    (SymmetricCoefficient (M := M)) := fun e j => bottEvaluation cs l e (bottBasis cs l j)

 theorem bottEvaluation_expand (l : List I) (e : BottIndex l) (m : BottSamelsonModule cs l) :
    bottEvaluation cs l e m =
      (bottEvaluationMatrix cs l *ᵥ (bottBasis cs l).equivFun m) e := by
  classical
  conv_lhs => rw [← (bottBasis cs l).sum_repr m]
  simp only [map_sum,map_smul,smul_eq_mul,Matrix.mulVec,dotProduct,
    bottEvaluationMatrix,Basis.equivFun_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

 theorem bottEvaluationMatrix_cons (i : I) (l : List I)
    (r c : Fin 2) (j k : BottIndex l) :
    bottEvaluationMatrix cs (i::l) (r,j) (c,k) =
      if r=0 then (if c=0 then bottEvaluationMatrix cs l j k else
        simpleRootPolynomial i*bottEvaluationMatrix cs l j k)
      else if c=0 then coefficientAction cs (cs.simple i) (bottEvaluationMatrix cs l j k)
      else -simpleRootPolynomial i*coefficientAction cs (cs.simple i) (bottEvaluationMatrix cs l j k) := by
  let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
    simpleFixed_free cs i
  let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
    simpleFixed_finite cs i
  change bottEvaluation cs (i::l) (r,j)
    (inducedBasis (coefficientAction cs (cs.simple i)) (simpleRootPolynomial i)
      (simple_involutive cs i) (simpleRootPolynomial_ne_zero i) (simple_anti cs i)
      (simple_divisible cs i) (bottSamelson cs l).obj (bottBasis cs l) (c,k)) = _
  rw [inducedBasis_apply]
  erw [bottEvaluation_tmul]
  fin_cases r <;> fin_cases c <;>
    simp only [Fin.zero_eta,Fin.isValue,Fin.mk_one,ite_true,
      show (1:Fin 2) ≠ 0 by decide,ite_false,reflectionBasis_zero,reflectionBasis_one,
      one_smul,one_mul,map_smul,smul_eq_mul,map_mul,simple_anti,bottEvaluationMatrix]

 theorem bottEvaluationMatrix_mulVec_cons (i : I) (l : List I)
    (v : BottIndex (i::l) → SymmetricCoefficient (M := M)) :
    bottEvaluationMatrix cs (i::l) *ᵥ v =
      wallCoordinate (coefficientAction cs (cs.simple i)).toRingEquiv
        (simpleRootPolynomial i) (bottEvaluationMatrix cs l) v := by
  have heq : bottEvaluationMatrix cs (i::l) =
      wallMatrix (coefficientAction cs (cs.simple i)).toRingEquiv
        (simpleRootPolynomial i) (bottEvaluationMatrix cs l) := by
    funext e f
    rcases e with ⟨r,j⟩
    rcases f with ⟨c,k⟩
    exact bottEvaluationMatrix_cons cs i l r c j k
  rw [heq]
  exact wallMatrix_mulVec (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial i) (bottEvaluationMatrix cs l) v

 theorem bottEvaluationMatrix_injective (l : List I) :
    Function.Injective (Matrix.mulVec (bottEvaluationMatrix cs l)) := by
  classical
  let : CharZero (SymmetricCoefficient (M := M)) := Algebra.charZero_of_charZero ℝ _
  induction l with
  | nil =>
    intro v w h
    funext j
    change PUnit at j
    cases j
    have hh := congrFun h PUnit.unit
    let : Unique (BottIndex ([] : List I)) := inferInstanceAs (Unique PUnit)
    have hcol (k : BottIndex ([] : List I)) :
        bottEvaluationMatrix cs [] PUnit.unit k = 1 := by
      change PUnit at k
      change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) k) = 1
      simp only [Basis.singleton_apply]
    simp only [Matrix.mulVec,dotProduct,hcol,one_mul,Finset.univ_unique,
      Finset.sum_singleton] at hh
    simpa only [Subsingleton.elim (default : BottIndex ([] : List I)) PUnit.unit] using hh
  | cons i l ih =>
    intro v w h
    apply wallCoordinate_injective (coefficientAction cs (cs.simple i)).toRingEquiv
      (simpleRootPolynomial i) (simpleRootPolynomial_ne_zero i) (bottEvaluationMatrix cs l) ih
    rw [← bottEvaluationMatrix_mulVec_cons,← bottEvaluationMatrix_mulVec_cons]
    exact h

 theorem bottEvaluation_injective (l : List I) :
    Function.Injective (fun m : BottSamelsonModule cs l => fun e => bottEvaluation cs l e m) := by
  intro m n h
  apply (bottBasis cs l).equivFun.injective
  apply bottEvaluationMatrix_injective cs l
  funext e
  rw [← bottEvaluation_expand,← bottEvaluation_expand]
  exact congrFun h e

end
end KLInvariance.TitsSpace

end


section

/-! Integral denominators exhibit the full generic subexpression support of
an actual tensor word. No moment-sheaf character assertion is made. -/
namespace KLInvariance.TitsSpace
open Module
open scoped Matrix
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottCoordinateDenominator (l : List I) : SymmetricCoefficient (M := M) := by
  classical
  exact (bottEvaluationMatrix cs l).det

 theorem bottCoordinateDenominator_ne_zero (l : List I) :
    bottCoordinateDenominator cs l ≠ 0 := by
  classical
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact Matrix.mulVec_injective_iff.mp (bottEvaluationMatrix_injective cs l)

 theorem bottEvaluation_contains_scaled_coordinates (l : List I)
    (v : BottIndex l → SymmetricCoefficient (M := M)) :
    ∃ m : BottSamelsonModule cs l, ∀ e,
      bottEvaluation cs l e m = bottCoordinateDenominator cs l * v e := by
  classical
  refine ⟨(bottBasis cs l).equivFun.symm ((bottEvaluationMatrix cs l).adjugate *ᵥ v),?_⟩
  intro e
  rw [bottEvaluation_expand]
  simp only [LinearEquiv.apply_symm_apply,Matrix.mulVec_mulVec,Matrix.mul_adjugate,
    Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,bottCoordinateDenominator]

end
end KLInvariance.TitsSpace

end


section

/-! Faithfulness of the actual polynomial action; distinct Coxeter weights
have distinct integral polynomial characters. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem symmetricCoefficient_ι_injective :
    Function.Injective (SymmetricAlgebra.ι ℝ (Extended M)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ (x-y)).mp
  intro f
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he := congrArg (SymmetricAlgebra.lift f) h
  simpa only [SymmetricAlgebra.lift_ι_apply] using he

 theorem coefficientAction_injective : Function.Injective (coefficientAction cs) := by
  intro x y h
  apply extendedAction_injective M cs
  apply LinearEquiv.ext
  intro v
  apply symmetricCoefficient_ι_injective (M := M)
  have he := congrArg (fun g : SymmetricCoefficient (M := M) ≃ₐ[ℝ]
    SymmetricCoefficient (M := M) => g (SymmetricAlgebra.ι ℝ (Extended M) v)) h
  simpa only [coefficientAction_ι] using he

 theorem coefficientAction_separates {x y : W} (hxy : x ≠ y) :
    ∃ a : SymmetricCoefficient (M := M), coefficientAction cs x a ≠ coefficientAction cs y a := by
  by_contra! h
  apply hxy
  apply coefficientAction_injective cs
  exact AlgEquiv.ext h

end
end KLInvariance.TitsSpace

end


section

/-! Integral weight support and orthogonality for the actual tensor module.
These are the vertex support statements behind the section pairing, not an
identification of the minimal BMP sheaf or its character. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance (l : List I) : DecidableEq (BottIndex l) := Classical.decEq _

 def bottWeightSupported (l : List I) (x : W) : Submodule (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l) where
  carrier := {m | ∀ e, bottWeight cs l e ≠ x → bottEvaluation cs l e m = 0}
  zero_mem' := by intro e _; exact map_zero _
  add_mem' := by intro m n hm hn e he; rw [map_add,hm e he,hn e he,zero_add]
  smul_mem' := by intro a m hm e he; rw [map_smul,hm e he,smul_zero]

 theorem bott_weight_eigen (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : m ∈ bottWeightSupported cs l x) (a : SymmetricCoefficient (M := M)) :
    bottSamelsonRight cs l a m = coefficientAction cs x a • m := by
  apply bottEvaluation_injective cs l
  funext e
  change bottEvaluation cs l e (bottSamelsonRight cs l a m) =
    bottEvaluation cs l e (coefficientAction cs x a • m)
  erw [bottEvaluation_right,map_smul]
  change _ = coefficientAction cs x a * bottEvaluation cs l e m
  by_cases he : bottWeight cs l e = x
  · rw [he]
  · rw [hm e he,mul_zero,mul_zero]

 theorem bott_eigen_supported (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : ∀ a : SymmetricCoefficient (M := M),
      bottSamelsonRight cs l a m = coefficientAction cs x a • m) :
    m ∈ bottWeightSupported cs l x := by
  intro e he
  obtain ⟨a,ha⟩ := coefficientAction_separates cs he
  have h := congrArg (bottEvaluation cs l e) (hm a)
  erw [bottEvaluation_right,map_smul] at h
  change coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e m =
    coefficientAction cs x a * bottEvaluation cs l e m at h
  have hh : (coefficientAction cs (bottWeight cs l e) a-coefficientAction cs x a) *
      bottEvaluation cs l e m = 0 := by rw [sub_mul,h,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha)

 theorem bott_distinct_weight_orthogonal (l : List I) {x y : W} (hxy : x ≠ y)
    {m n : BottSamelsonModule cs l} (hm : m ∈ bottWeightSupported cs l x)
    (hn : n ∈ bottWeightSupported cs l y) : bottSamelsonDuality cs l m n = 0 := by
  obtain ⟨a,ha⟩ := coefficientAction_separates cs hxy
  have h := bottSamelson_balanced cs l a m n
  rw [bott_weight_eigen cs l x hm,bott_weight_eigen cs l y hn] at h
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h
  have he : (coefficientAction cs x a-coefficientAction cs y a) *
      bottSamelsonDuality cs l m n = 0 := by rw [sub_mul,h,sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha)

 def bottCoordinateLift (l : List I) (e : BottIndex l) : BottSamelsonModule cs l := by
  classical
  exact (bottEvaluation_contains_scaled_coordinates cs l (Pi.single e 1)).choose

 theorem bottCoordinateLift_eval (l : List I) (e j : BottIndex l) :
    bottEvaluation cs l j (bottCoordinateLift cs l e) =
      bottCoordinateDenominator cs l * (Pi.single e 1 : BottIndex l → SymmetricCoefficient (M := M)) j := by
  classical
  exact (bottEvaluation_contains_scaled_coordinates cs l (Pi.single e 1)).choose_spec j

 theorem bottCoordinateLift_supported (l : List I) (e : BottIndex l) :
    bottCoordinateLift cs l e ∈ bottWeightSupported cs l (bottWeight cs l e) := by
  intro j hj
  rw [bottCoordinateLift_eval]
  have hje : j ≠ e := fun h => hj (congrArg (bottWeight cs l) h)
  rw [Pi.single_eq_of_ne hje, mul_zero]

 theorem bottCoordinateExpansion (l : List I) (m : BottSamelsonModule cs l) :
    bottCoordinateDenominator cs l • m =
      ∑ e : BottIndex l, bottEvaluation cs l e m • bottCoordinateLift cs l e := by
  classical
  apply bottEvaluation_injective cs l
  funext j
  simp only [map_smul,map_sum,bottCoordinateLift_eval,smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same,mul_one,mul_comm]
  · intro e _ hej
    rw [Pi.single_eq_of_ne (Ne.symm hej),mul_zero,mul_zero]
  · simp

end
end KLInvariance.TitsSpace

end


section

/-! The actual tensor word's integral weight-support lattice is the dual of
its integral projected stalk lattice. This is not merely a fraction-field
isomorphism. It still does NOT identify BMP sections with an indecomposable
summand of the tensor word, or prove the character theorem. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottWeightProjection (l : List I) (x : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  LinearMap.pi (fun e => bottEvaluation cs l e.val)

 theorem bottWeightProjection_eq_zero (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    bottWeightProjection cs l x m = 0 ↔ ∀ e, bottWeight cs l e=x → bottEvaluation cs l e m=0 := by
  constructor
  · intro h e he
    exact congrFun h ⟨e,he⟩
  · intro h
    funext e
    exact h e.val e.property

 theorem bott_supported_annihilates (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : m ∈ bottWeightSupported cs l x) (n : BottSamelsonModule cs l)
    (hn : bottWeightProjection cs l x n=0) : bottSamelsonDuality cs l m n=0 := by
  classical
  have hn' := (bottWeightProjection_eq_zero cs l x n).mp hn
  have hsum : ∑ e : BottIndex l, bottEvaluation cs l e n *
      bottSamelsonDuality cs l m (bottCoordinateLift cs l e) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : bottWeight cs l e=x
    · rw [hn' e he,zero_mul]
    · rw [bott_distinct_weight_orthogonal cs l (Ne.symm he) hm
        (bottCoordinateLift_supported cs l e),mul_zero]
  have hh := congrArg (bottSamelsonDuality cs l m) (bottCoordinateExpansion cs l n)
  simp only [map_smul,map_sum,smul_eq_mul] at hh
  rw [hsum] at hh
  exact (mul_eq_zero.mp hh).resolve_left (bottCoordinateDenominator_ne_zero cs l)

 theorem bott_annihilates_supported (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : ∀ n : BottSamelsonModule cs l, bottWeightProjection cs l x n=0 →
      bottSamelsonDuality cs l m n=0) : m ∈ bottWeightSupported cs l x := by
  apply bott_eigen_supported cs l x
  intro a
  apply (bottSamelsonDuality cs l).injective
  apply LinearMap.ext
  intro n
  have hn : bottWeightProjection cs l x
      (bottSamelsonRight cs l a n - coefficientAction cs x a • n)=0 := by
    apply (bottWeightProjection_eq_zero cs l x _).mpr
    intro e he
    erw [map_sub,bottEvaluation_right,map_smul]
    change coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e n -
      coefficientAction cs x a * bottEvaluation cs l e n=0
    rw [he,sub_self]
  have hh := hm _ hn
  simp only [map_sub,map_smul,smul_eq_mul] at hh
  rw [bottSamelson_balanced]
  change bottSamelsonDuality cs l m (bottSamelsonRight cs l a n) =
    (bottSamelsonDuality cs l (coefficientAction cs x a • m)) n
  rw [map_smul,LinearMap.smul_apply,smul_eq_mul]
  exact sub_eq_zero.mp hh

 theorem bott_supported_iff_annihilates (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    m ∈ bottWeightSupported cs l x ↔ ∀ n : BottSamelsonModule cs l,
      bottWeightProjection cs l x n=0 → bottSamelsonDuality cs l m n=0 :=
  ⟨fun h => bott_supported_annihilates cs l x h,fun h => bott_annihilates_supported cs l x h⟩

 def bottStalk (l : List I) (x : W) : Submodule (SymmetricCoefficient (M := M))
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  LinearMap.range (bottWeightProjection cs l x)

 def bottStalkProjection (l : List I) (x : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] bottStalk cs l x :=
  (bottWeightProjection cs l x).rangeRestrict

 theorem bottStalkProjection_surjective (l : List I) (x : W) :
    Function.Surjective (bottStalkProjection cs l x) := by
  rintro ⟨v,m,hm⟩
  exact ⟨m,Subtype.ext hm⟩

 theorem bottStalkProjection_eq_zero (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x m=0 ↔ bottWeightProjection cs l x m=0 := by
  exact Subtype.ext_iff

 def bottStalkDualToSupport (l : List I) (x : W) :
    Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) →ₗ[SymmetricCoefficient (M := M)]
      bottWeightSupported cs l x :=
  ((bottSamelsonDuality cs l).symm.toLinearMap.comp
    (bottStalkProjection cs l x).dualMap).codRestrict (bottWeightSupported cs l x) (by
    intro lam
    apply bott_annihilates_supported cs l x
    intro n hn
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply]
    change lam (bottStalkProjection cs l x n)=0
    rw [(bottStalkProjection_eq_zero cs l x n).mpr hn,map_zero])

 theorem bottStalkDualToSupport_bijective (l : List I) (x : W) :
    Function.Bijective (bottStalkDualToSupport cs l x) := by
  constructor
  · intro lam mu he
    apply LinearMap.dualMap_injective_of_surjective (bottStalkProjection_surjective cs l x)
    apply (bottSamelsonDuality cs l).symm.injective
    exact congrArg Subtype.val he
  · intro m
    have hm : bottSamelsonDuality cs l m.val ∈
        (LinearMap.ker (bottStalkProjection cs l x)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      exact bott_supported_annihilates cs l x m.property n
        ((bottStalkProjection_eq_zero cs l x n).mp hn)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _
      (bottStalkProjection_surjective cs l x)] at hm
    obtain ⟨lam,hlam⟩ := hm
    refine ⟨lam,?_⟩
    apply Subtype.ext
    change (bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam)=m.val
    rw [hlam,LinearEquiv.symm_apply_apply]

 def bottStalkDuality (l : List I) (x : W) : bottWeightSupported cs l x ≃ₗ[
    SymmetricCoefficient (M := M)] Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  (LinearEquiv.ofBijective (bottStalkDualToSupport cs l x)
    (bottStalkDualToSupport_bijective cs l x)).symm

end
end KLInvariance.TitsSpace

end


section

/-! Full reflection labels, rather than just simple-wall labels, in the
actual tensor bimodule coefficient action. -/
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem coefficientAction_reflection {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t = reflectionAction (embed M a) (extendedForm M (embed M a))
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  rw [coefficientAction,ha.extendedAction_eq]

 theorem reflectionCoefficient_anti {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t (SymmetricAlgebra.ι ℝ (Extended M) (embed M a)) =
      -SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := by
  rw [coefficientAction_reflection cs ha]
  exact reflectionAction_anti _ _ _

 theorem reflectionCoefficient_divisible {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (p : SymmetricCoefficient (M := M)) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣ p-coefficientAction cs t p := by
  rw [coefficientAction_reflection cs ha]
  exact reflectionAction_divisible _ _ _ p

 theorem reflectionCoefficient_difference {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (x : W) : ∃ p : SymmetricCoefficient (M := M),
    coefficientAction cs x p-coefficientAction cs (t*x) p =
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := by
  let α := SymmetricAlgebra.ι ℝ (Extended M) (embed M a)
  let c : SymmetricCoefficient (M := M) := (1/2 : ℝ) • α
  refine ⟨(coefficientAction cs x).symm c,?_⟩
  rw [coefficientAction_mul,AlgEquiv.apply_symm_apply]
  change (1/2 : ℝ) • α - coefficientAction cs t ((1/2 : ℝ) • α) = α
  rw [map_smul,reflectionCoefficient_anti cs ha]
  module

end
end KLInvariance.TitsSpace

end


section

/-! Exact Bruhat support of the actual tensor word's subexpression weights.
The ambient Coxeter system is not assumed crystallographic. -/
namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSubword : (l : List I) → BottIndex l → List I
  | [], _ => []
  | i::l, e => if e.1=0 then bottSubword l e.2 else i::bottSubword l e.2

 theorem bottSubword_sublist (l : List I) (e : BottIndex l) :
    (bottSubword l e).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i l ih =>
    by_cases h : e.1=0
    · rw [bottSubword,ite_eq_left h]
      exact List.Sublist.cons i (ih e.2)
    · rw [bottSubword,ite_eq_right h]
      exact List.Sublist.cons_cons i (ih e.2)

 theorem bottSubword_wordProd (l : List I) (e : BottIndex l) :
    cs.wordProd (bottSubword l e) = bottWeight cs l e := by
  induction l with
  | nil => exact cs.wordProd_nil
  | cons i l ih =>
    by_cases h : e.1=0
    · simp only [bottSubword,bottWeight,ite_eq_left h,ih]
    · simp only [bottSubword,bottWeight,ite_eq_right h,cs.wordProd_cons,ih]

 theorem exists_bottSubword {ν l : List I} (h : ν.Sublist l) :
    ∃ e : BottIndex l, bottSubword l e = ν := by
  induction h with
  | slnil => exact ⟨PUnit.unit,rfl⟩
  | cons i h ih =>
    obtain ⟨e,he⟩ := ih
    exact ⟨(0,e),by simpa only [bottSubword,ite_true] using he⟩
  | cons_cons i h ih =>
    obtain ⟨e,he⟩ := ih
    exact ⟨(1,e),by simp only [bottSubword,show (1:Fin 2) ≠ 0 by decide,ite_false,he]⟩

 theorem bottWeight_bruhat (l : List I) (hl : cs.IsReduced l) (e : BottIndex l) :
    BruhatLE cs (bottWeight cs l e) (cs.wordProd l) := by
  rw [← bottSubword_wordProd]
  exact bruhat_of_subword cs (bottSubword_sublist l e) hl

 theorem exists_bottWeight (l : List I) (hl : cs.IsReduced l) {x : W}
    (hx : BruhatLE cs x (cs.wordProd l)) : ∃ e : BottIndex l, bottWeight cs l e=x := by
  obtain ⟨ν,hν,_,he⟩ := (bruhat_iff_reduced_subword cs hl).mp hx
  obtain ⟨e,he'⟩ := exists_bottSubword hν
  exact ⟨e,by rw [← bottSubword_wordProd,he',he]⟩

 theorem bottWeight_range (l : List I) (hl : cs.IsReduced l) :
    Set.range (bottWeight cs l) = {x | BruhatLE cs x (cs.wordProd l)} := by
  ext x
  constructor
  · rintro ⟨e,rfl⟩
    exact bottWeight_bruhat cs l hl e
  · exact exists_bottWeight cs l hl

end
end KLInvariance.TitsSpace

end


section

/-! The actual integral two-vertex projection sheaf of a tensor
Bott--Samelson module. This is the localization-functor construction, not
an assumed BMP sheaf. Surjectivity onto ALL sections, flabbiness, free stalks,
and the indecomposable normalization remain separate obligations. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalkProjection_right (l : List I) (x : W)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x (bottSamelsonRight cs l a m) =
      coefficientAction cs x a • bottStalkProjection cs l x m := by
  apply Subtype.ext
  funext e
  change bottEvaluation cs l e.val (bottSamelsonRight cs l a m) =
    coefficientAction cs x a * bottEvaluation cs l e.val m
  rw [bottEvaluation_right,e.property]

 def bottProjectionSheaf (l : List I) (u b : W) : Sheaf (R := SymmetricCoefficient (M := M))
    (graph cs u b) where
  vertex x := ModuleCat.of _ (bottStalk cs l x.val)
  edge e := ModuleCat.of _ (PairProjection.Edge
    (bottStalkProjection cs l (source cs u b e).val)
    (bottStalkProjection cs l (target cs u b e).val))
  lower e := by
    change (bottStalk cs l (source cs u b e).val) →ₗ[SymmetricCoefficient (M := M)] _
    exact PairProjection.lower (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val)
  upper e := by
    change (bottStalk cs l (target cs u b e).val) →ₗ[SymmetricCoefficient (M := M)] _
    exact PairProjection.upper (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val)

 def bottSection (l : List I) (u b : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] (bottProjectionSheaf cs l u b).sections Set.univ where
  toFun m := ⟨fun x => bottStalkProjection cs l x.val m,by
    intro e _ _
    exact PairProjection.compatible _ _ m⟩
  map_add' := by
    intro m n
    apply Subtype.ext
    funext x
    exact map_add (bottStalkProjection cs l x.val) m n
  map_smul' := by
    intro r m
    apply Subtype.ext
    funext x
    exact map_smul (bottStalkProjection cs l x.val) r m

 theorem bottProjectionSheaf_generated (l : List I) (u b : W) :
    (bottProjectionSheaf cs l u b).Generated := by
  intro x v
  obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val v
  exact ⟨(bottSection cs l u b m).val,(bottSection cs l u b m).property,hm⟩

 theorem bottProjectionSheaf_lower_surjective (l : List I) (u b : W) (e : Edge cs u b) :
    Function.Surjective ((bottProjectionSheaf cs l u b).lower e) :=
  PairProjection.lower_surjective _ _ (bottStalkProjection_surjective cs l _)

 theorem bottProjectionSheaf_upper_surjective (l : List I) (u b : W) (e : Edge cs u b) :
    Function.Surjective ((bottProjectionSheaf cs l u b).upper e) :=
  PairProjection.upper_surjective _ _ (bottStalkProjection_surjective cs l _)

/-- An actual Bruhat reflection root annihilates the integral edge quotient. -/
 theorem bottProjectionSheaf_annihilated (l : List I) (u b : W) (e : Edge cs u b)
    {a : I → ℝ} (ha : Represents M cs (label cs u b e) a)
    (z : (bottProjectionSheaf cs l u b).edge e) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z = 0 := by
  obtain ⟨p,hp⟩ := reflectionCoefficient_difference cs ha (source cs u b e).val
  rw [label_mul_source] at hp
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs l _) (bottStalkProjection_surjective cs l _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs l _ p) (bottStalkProjection_right cs l _ p) z

 theorem bottSection_injective (l : List I) (hl : cs.IsReduced l) :
    Function.Injective (bottSection cs l 1 (cs.wordProd l)) := by
  intro m n h
  apply bottEvaluation_injective cs l
  funext e
  let x : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hh := congrArg (fun z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    z.val x) h
  exact congrFun (congrArg Subtype.val hh) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace

end


section

/-! Exact kernels of the actual pair-projection quotient, in a form that
separates integral divisibility from annihilation of the edge. -/
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : M →ₗ[R] X) (g : M →ₗ[R] Y)

 theorem kernel_upper (y : Y) : upper f g y=0 ↔ ∃ m : M, f m=0 ∧ g m=y := by
  have he : upper f g y=0 ↔ lower f g 0=upper f g y := by
    rw [map_zero, eq_comm]
  rw [he, compatible_iff]

 theorem upper_kernel_of_divisibility (α : R)
    (hker : ∀ m : M, f m=0 → ∃ n : Y, g m=α • n)
    (hann : ∀ z : Edge f g, α • z=0) (y : Y) :
    upper f g y=0 ↔ ∃ n : Y, y=α • n := by
  constructor
  · intro h
    obtain ⟨m,hm,rfl⟩ := (kernel_upper f g y).mp h
    exact hker m hm
  · rintro ⟨n,rfl⟩
    rw [map_smul]
    exact hann _

end KLInvariance.PairProjection

end


section

/-! The exact simple-wall kernel for the actual integral tensor word module.
This is a step toward word-sheaf recognition, not a character theorem or a
proof of combinatorial invariance. No stalk freeness is assumed. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

/-- The reflection is linear over its actual invariant subalgebra. -/
def simpleFixedAction (i : I) : SymmetricCoefficient (M := M) →ₗ[simpleFixed cs i]
    SymmetricCoefficient (M := M) where
  toFun := coefficientAction cs (cs.simple i)
  map_add' := map_add _
  map_smul' c a := by
    change coefficientAction cs (cs.simple i) ((c : SymmetricCoefficient (M := M))*a) =
      (c : SymmetricCoefficient (M := M))*coefficientAction cs (cs.simple i) a
    rw [map_mul, show coefficientAction cs (cs.simple i)
      (c : SymmetricCoefficient (M := M)) = c from c.property]

/-- Reflect the first tensor factor. It is not asserted to be left A-linear. -/
def bottSimpleFlip (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[simpleFixed cs i]
    BottSamelsonModule cs (i::l) :=
  TensorProduct.map (simpleFixedAction cs i)
    (LinearMap.id : BottSamelsonModule cs l →ₗ[simpleFixed cs i] BottSamelsonModule cs l)

@[simp] theorem bottSimpleFlip_tmul (i : I) (l : List I)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottSimpleFlip cs i l (a ⊗ₜ[simpleFixed cs i] m) =
      coefficientAction cs (cs.simple i) a ⊗ₜ[simpleFixed cs i] m := rfl

/-- The integral divisibility statement, before any localization. -/
theorem bottSimpleFlip_divisible (i : I) (l : List I) (m : BottSamelsonModule cs (i::l)) :
    ∃ n : BottSamelsonModule cs (i::l),
      m-bottSimpleFlip cs i l m = simpleRootPolynomial (M := M) i • n := by
  change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
  induction m using TensorProduct.inductionOn with
  | add m n hm hn =>
    obtain ⟨m',hm'⟩ := hm
    obtain ⟨n',hn'⟩ := hn
    refine ⟨m'+n', ?_⟩
    erw [map_add, add_sub_add_comm, hm', hn', smul_add]
  | tmul a m =>
    obtain ⟨b,hb⟩ := simple_divisible cs i a
    refine ⟨b ⊗ₜ[simpleFixed cs i] m, ?_⟩
    erw [bottSimpleFlip_tmul, ← sub_tmul, hb]
    rfl


/-- Exchange the two branches of the first subexpression slot. -/
def bottIndexFlip (i : I) (l : List I) (e : BottIndex (i::l)) : BottIndex (i::l) :=
  (1-e.1,e.2)

omit [Fintype I] in
theorem bottWeight_flip (i : I) (l : List I) (e : BottIndex (i::l)) :
    bottWeight cs (i::l) (bottIndexFlip i l e) = cs.simple i * bottWeight cs (i::l) e := by
  rcases e with ⟨ε,e⟩
  fin_cases ε <;> simp [bottIndexFlip, bottWeight, cs.simple_mul_simple_cancel_left]

theorem bottEvaluation_flip (i : I) (l : List I) (e : BottIndex (i::l))
    (m : BottSamelsonModule cs (i::l)) :
    bottEvaluation cs (i::l) e (bottSimpleFlip cs i l m) =
      coefficientAction cs (cs.simple i)
        (bottEvaluation cs (i::l) (bottIndexFlip i l e) m) := by
  change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => erw [map_add, map_add, map_add, map_add, hm, hn]
  | tmul a m =>
    rcases e with ⟨ε,e⟩
    fin_cases ε
    · change coefficientAction cs (cs.simple i) a * bottEvaluation cs l e m =
        coefficientAction cs (cs.simple i)
          (a * coefficientAction cs (cs.simple i) (bottEvaluation cs l e m))
      rw [map_mul, simple_involutive cs i]
    · change coefficientAction cs (cs.simple i) a *
        coefficientAction cs (cs.simple i) (bottEvaluation cs l e m) =
        coefficientAction cs (cs.simple i) (a * bottEvaluation cs l e m)
      rw [map_mul]

theorem bottStalkProjection_flip_zero (i : I) (l : List I) (x : W)
    {m : BottSamelsonModule cs (i::l)} (hm : bottStalkProjection cs (i::l) x m=0) :
    bottStalkProjection cs (i::l) (cs.simple i*x) (bottSimpleFlip cs i l m)=0 := by
  apply (bottStalkProjection_eq_zero cs _ _ _).mpr
  apply (bottWeightProjection_eq_zero cs _ _ _).mpr
  intro e he
  rw [bottEvaluation_flip]
  have hh := (bottWeightProjection_eq_zero cs _ _ _).mp
    ((bottStalkProjection_eq_zero cs _ _ _).mp hm)
  rw [hh (bottIndexFlip i l e) (by
    rw [bottWeight_flip, he, cs.simple_mul_simple_cancel_left]), map_zero]

/-- The reverse inclusion to edge annihilation for the simple wall at the
first tensor letter, expressed directly on kernel projections. -/
theorem bottSimpleWall_kernel_projection (i : I) (l : List I) (x : W)
    {m : BottSamelsonModule cs (i::l)} (hm : bottStalkProjection cs (i::l) x m=0) :
    ∃ n : bottStalk cs (i::l) (cs.simple i*x),
      bottStalkProjection cs (i::l) (cs.simple i*x) m = simpleRootPolynomial (M := M) i • n := by
  obtain ⟨n,hn⟩ := bottSimpleFlip_divisible cs i l m
  refine ⟨bottStalkProjection cs (i::l) (cs.simple i*x) n, ?_⟩
  have he := congrArg (bottStalkProjection cs (i::l) (cs.simple i*x)) hn
  rw [map_sub, map_smul, bottStalkProjection_flip_zero cs i l x hm, sub_zero] at he
  exact he

theorem simpleCoefficient_difference (i : I) (x : W) :
    ∃ p : SymmetricCoefficient (M := M),
      coefficientAction cs x p - coefficientAction cs (cs.simple i*x) p =
        simpleRootPolynomial (M := M) i := by
  let α := simpleRootPolynomial (M := M) i
  refine ⟨(coefficientAction cs x).symm ((1/2 : ℝ) • α), ?_⟩
  rw [coefficientAction_mul, AlgEquiv.apply_symm_apply]
  change (1/2 : ℝ) • α - coefficientAction cs (cs.simple i) ((1/2 : ℝ) • α) = α
  rw [map_smul, simple_anti]
  module


/-- Any old word's simple-edge quotient is killed by the actual label. -/
theorem bottSimpleEdge_annihilated (i : I) (l : List I) (x : W)
    (z : PairProjection.Edge (bottStalkProjection cs l x)
      (bottStalkProjection cs l (cs.simple i*x))) :
    simpleRootPolynomial (M := M) i • z = 0 := by
  obtain ⟨p,hp⟩ := simpleCoefficient_difference cs i x
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs _ _) (bottStalkProjection_surjective cs _ _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs _ _ p) (bottStalkProjection_right cs _ _ p) z

theorem bottSimpleEdge_kernel_inclusion (i : I) (l : List I) (x : W)
    (y : bottStalk cs l (cs.simple i*x)) :
    ∃ n : BottSamelsonModule cs l, bottStalkProjection cs l x n=0 ∧
      bottStalkProjection cs l (cs.simple i*x) n=simpleRootPolynomial (M := M) i • y := by
  apply (PairProjection.kernel_upper _ _ _).mp
  rw [map_smul]
  exact bottSimpleEdge_annihilated cs i l x _

/-- The integral edge quotient is killed by its actual simple-root label. -/
theorem bottSimpleWall_annihilated (i : I) (l : List I) (x : W)
    (z : PairProjection.Edge (bottStalkProjection cs (i::l) x)
      (bottStalkProjection cs (i::l) (cs.simple i*x))) :
    simpleRootPolynomial (M := M) i • z = 0 :=
  bottSimpleEdge_annihilated cs i (i::l) x z

/-- The exact integral quotient kernel, without a free-stalk hypothesis. -/
theorem bottSimpleWall_upper_kernel (i : I) (l : List I) (x : W)
    (z : bottStalk cs (i::l) (cs.simple i*x)) :
    PairProjection.upper (bottStalkProjection cs (i::l) x)
      (bottStalkProjection cs (i::l) (cs.simple i*x)) z = 0 ↔
    ∃ n : bottStalk cs (i::l) (cs.simple i*x), z = simpleRootPolynomial (M := M) i • n :=
  PairProjection.upper_kernel_of_divisibility _ _ _
    (fun _ hm => bottSimpleWall_kernel_projection cs i l x hm)
    (bottSimpleWall_annihilated cs i l x) z

end
end KLInvariance.TitsSpace

end


section

/-! Integral simple-wall translation of a two-stalk projection lattice.
The hypotheses are explicit old-word edge properties, not character claims.
No freeness of a submodule is inferred merely from finite generation. -/
namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Restriction of the scalar action along a ring automorphism. -/
@[ext] structure Twist (_τ : R ≃+* R) (Y : Type z) where
  val : Y
namespace Twist
variable (τ : R ≃+* R) (Y : Type z) [AddCommGroup Y] [Module R Y]
local instance : RingHomInvPair τ.symm.toRingHom τ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm τ
local instance : RingHomInvPair τ.toRingHom τ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv τ
def equivVal : Twist τ Y ≃ Y where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
instance : AddCommGroup (Twist τ Y) := (equivVal τ Y).addCommGroup
instance : Module R (Twist τ Y) := by
  letI : Module R Y := Module.compHom Y τ.toRingHom
  exact ({ equivVal τ Y with map_add' := fun _ _ => rfl } : Twist τ Y ≃+ Y).module R

def equiv : Y ≃ₛₗ[τ.symm.toRingHom] Twist τ Y where
  toFun := mk
  invFun := val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r y := by
    change mk (r • y) = mk (τ (τ.symm r) • y)
    rw [τ.apply_symm_apply]

instance [Module.Free R Y] : Module.Free R (Twist τ Y) :=
  Module.Free.of_equiv (equiv τ Y)
end Twist

variable {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)

/-- The old pair relation with the scalar action on its second factor twisted.
Alpha-annihilation of the old edge is what makes this an R-submodule. -/
def lattice : Submodule R (X × Twist τ Y) where
  carrier := {p | ∃ n : N, f n=p.1 ∧ g n=p.2.val}
  zero_mem' := ⟨0,map_zero _,map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨m,hm,hm'⟩ ⟨n,hn,hn'⟩
    exact ⟨m+n,by rw [map_add,hm,hn]; rfl,by rw [map_add,hm',hn']; rfl⟩
  smul_mem' := by
    rintro r ⟨x,y⟩ ⟨n,hn,hn'⟩
    obtain ⟨c,hc⟩ := hdiv r
    obtain ⟨m,hm,hm'⟩ := hinc (c • y.val)
    have hm'' : g m=(τ r-r) • y.val := by rw [hm',hc,mul_smul]
    refine ⟨r • n+m,?_,?_⟩
    · change f (r • n+m)=r • x
      rw [map_add,map_smul,hn,hm,add_zero]
    · change g (r • n+m)=τ r • y.val
      rw [map_add,map_smul,hn',hm'',sub_smul]
      abel

/-- Saturation away from the simple wall. Regularity on the old edge module,
not an unjustified reflexivity assertion, removes a non-wall factor. -/
theorem lattice_saturated (β : R)
    (hann : ∀ e : PairProjection.Edge f g, α • e=0)
    (hreg : Function.Injective (fun e : PairProjection.Edge f g => β • e))
    (p : X × Twist τ Y) :
    β • p ∈ lattice f g τ α hdiv hinc ↔ p ∈ lattice f g τ α hdiv hinc := by
  constructor
  · rintro ⟨n,hn,hn'⟩
    apply (PairProjection.compatible_iff f g p.1 p.2.val).mp
    apply hreg
    have hn'' : g n=τ β • p.2.val := hn'
    have h := PairProjection.compatible f g n
    have hn1 : f n=β • p.1 := hn
    rw [hn1,hn'',map_smul,map_smul] at h
    obtain ⟨c,hc⟩ := hdiv β
    have he : (τ β-β) • PairProjection.upper f g p.2.val=0 := by
      rw [hc,mul_smul,smul_comm,hann,smul_zero]
    rw [sub_smul,sub_eq_zero] at he
    exact h.trans he
  · exact (lattice f g τ α hdiv hinc).smul_mem β

/-- Surjective projection to the untwisted (lower) stalk. -/
def left : lattice f g τ α hdiv hinc →ₗ[R] X :=
  (LinearMap.fst R X (Twist τ Y)).comp (lattice f g τ α hdiv hinc).subtype

 theorem left_surjective (hf : Function.Surjective f) :
    Function.Surjective (left f g τ α hdiv hinc) := by
  intro x
  obtain ⟨n,rfl⟩ := hf x
  exact ⟨⟨(f n,⟨g n⟩),n,rfl,rfl⟩,rfl⟩

/-- Its kernel is the alpha-multiple of the twisted upper stalk. -/
def kernelMap : Twist τ Y →ₗ[R] LinearMap.ker (left f g τ α hdiv hinc) where
  toFun y := ⟨⟨(0,⟨α • y.val⟩),hinc y.val⟩,rfl⟩
  map_add' y z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (0 : X)=0+0; simp
    · change Twist.mk (α • (y.val+z.val)) = Twist.mk (α • y.val+α • z.val)
      rw [smul_add]
  map_smul' r y := by
    apply Subtype.ext
    apply Subtype.ext
    change (0,Twist.mk (α • (τ r • y.val)))=(r • (0 : X),Twist.mk (τ r • (α • y.val)))
    rw [smul_zero,smul_comm α (τ r)]

 variable (hker : ∀ y : Y, (∃ n : N, f n=0 ∧ g n=y) ↔ ∃ z : Y, y=α • z)

 include hker in
 theorem kernelMap_surjective : Function.Surjective (kernelMap f g τ α hdiv hinc) := by
  rintro ⟨⟨⟨x,y⟩,n,hn,hn'⟩,hx⟩
  change x=0 at hx
  subst x
  obtain ⟨z,hz⟩ := (hker y.val).mp ⟨n,hn,hn'⟩
  refine ⟨⟨z⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl (congrArg Twist.mk hz.symm)

 theorem kernelMap_injective (hinj : Function.Injective (fun y : Y => α • y)) :
    Function.Injective (kernelMap f g τ α hdiv hinc) := by
  intro y z h
  apply Twist.ext
  exact hinj (congrArg (fun p => p.val.val.2.val) h)

noncomputable def kernelEquiv (hinj : Function.Injective (fun y : Y => α • y)) :
    Twist τ Y ≃ₗ[R] LinearMap.ker (left f g τ α hdiv hinc) :=
  LinearEquiv.ofBijective (kernelMap f g τ α hdiv hinc)
    ⟨kernelMap_injective f g τ α hdiv hinc hinj,kernelMap_surjective f g τ α hdiv hinc hker⟩

/-- A split extension of free modules is free. This does not assert the
false statement that every submodule of a free polynomial module is free. -/
theorem free_of_surjective_of_ker_free {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (π : P →ₗ[R] Q) (hπ : Function.Surjective π)
    [Module.Free R Q] [Module.Free R (LinearMap.ker π)] : Module.Free R P := by
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  let e : (LinearMap.ker π × Q) →ₗ[R] P :=
    (LinearMap.ker π).subtype.coprod s
  have hps (q : Q) : π (s q)=q := DFunLike.congr_fun hs q
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨k,q⟩ ⟨k',q'⟩ h
      have hq : q=q' := by
        have hh := congrArg π h
        simpa only [e,LinearMap.coprod_apply,Submodule.subtype_apply,map_add,LinearMap.mem_ker.mp k.property,
          LinearMap.mem_ker.mp k'.property,hps,zero_add] using hh
      subst q'
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact add_right_cancel h
    · intro p
      refine ⟨(⟨p-s (π p),?_⟩,π p),?_⟩
      · change π (p-s (π p))=0
        rw [map_sub,hps,sub_self]
      · change p-s (π p)+s (π p)=p
        abel
  exact Module.Free.of_equiv (LinearEquiv.ofBijective e he)

 include hker in
 theorem lattice_free (hf : Function.Surjective f)
    (hinj : Function.Injective (fun y : Y => α • y))
    [Module.Free R X] [Module.Free R Y] :
    Module.Free R (lattice f g τ α hdiv hinc) := by
  let : Module.Free R (LinearMap.ker (left f g τ α hdiv hinc)) :=
    Module.Free.of_equiv (kernelEquiv f g τ α hdiv hinc hker hinj)
  exact free_of_surjective_of_ker_free (left f g τ α hdiv hinc)
    (left_surjective f g τ α hdiv hinc hf)

end KLInvariance.ReflectionPairTranslation

end


section

/-! A generic tensor-generation lemma, kept separate so application to the
actual recursively paired word carrier does not unfold that carrier's data. -/

end

end OAI
