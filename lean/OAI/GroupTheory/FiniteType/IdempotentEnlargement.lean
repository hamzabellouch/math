import Mathlib

namespace OAI

noncomputable section
namespace IdempotentEnlargement
open TensorProduct

variable (K D V Z : Type*) [CommRing K] [Ring D] [Algebra K D]
  [Group V] [MulAction V Z]

abbrev RingSpace := D ⊗[K] MonoidAlgebra K V
abbrev ArraySpace := Z →₀ D

def permute : V →* Module.End K (ArraySpace D Z) where
  toFun g := Finsupp.lmapDomain D K (g • ·)
  map_one' := by
    apply Finsupp.lhom_ext
    intro z d
    simp
  map_mul' g h := by
    apply Finsupp.lhom_ext
    intro z d
    simp [Module.End.mul_apply, mul_smul]

@[simp] lemma permute_single (g : V) (z : Z) (d : D) :
    permute K D V Z g (Finsupp.single z d) = Finsupp.single (g • z) d := by
  simp [permute]

def coefficients : D →ₐ[K] Module.End K (ArraySpace D Z) where
  toFun d := Finsupp.mapRange.linearMap (LinearMap.mulLeft K d)
  map_zero' := by
    apply LinearMap.ext; intro x
    apply Finsupp.ext; intro z
    simp
  map_add' d e := by
    apply LinearMap.ext; intro x
    apply Finsupp.ext; intro z
    simp [add_mul]
  map_one' := by
    apply LinearMap.ext; intro x
    apply Finsupp.ext; intro z
    simp
  map_mul' d e := by
    apply LinearMap.ext; intro x
    apply Finsupp.ext; intro z
    simp [Module.End.mul_apply]
  commutes' c := by
    apply LinearMap.ext; intro x
    apply Finsupp.ext; intro z
    simp [Algebra.smul_def]

@[simp] lemma coefficients_single (d a : D) (z : Z) :
    coefficients K D Z d (Finsupp.single z a) = Finsupp.single z (d * a) := by
  exact Finsupp.mapRange_single (hf := (LinearMap.mulLeft K d).map_zero)

lemma coefficients_commute_permute (d : D) (g : V) :
    Commute (coefficients K D Z d) (permute K D V Z g) := by
  apply Finsupp.lhom_ext
  intro z a
  simp only [Module.End.mul_apply, permute_single, coefficients_single]

def groupAlgebraAction : MonoidAlgebra K V →ₐ[K] Module.End K (ArraySpace D Z) :=
  MonoidAlgebra.lift K (Module.End K (ArraySpace D Z)) V (permute K D V Z)

@[simp] lemma groupAlgebraAction_single (g : V) (a : K) :
    groupAlgebraAction K D V Z (MonoidAlgebra.single g a) =
      a • permute K D V Z g := by
  simp [groupAlgebraAction]

lemma coefficients_commute_groupAlgebra (d : D) (a : MonoidAlgebra K V) :
    Commute (coefficients K D Z d) (groupAlgebraAction K D V Z a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simpa using ha.add_right hb
  | single g c =>
    simpa using (coefficients_commute_permute K D V Z d g).smul_right c

def representation : RingSpace K D V →ₐ[K] Module.End K (ArraySpace D Z) :=
  Algebra.TensorProduct.lift (coefficients K D Z) (groupAlgebraAction K D V Z)
    (coefficients_commute_groupAlgebra K D V Z)

@[simp] lemma representation_tmul_single (d a : D) (g : V) (z : Z) :
    representation K D V Z (d ⊗ₜ[K] MonoidAlgebra.single g 1) (Finsupp.single z a) =
      Finsupp.single (g • z) (d * a) := by
  simp [representation, Module.End.mul_apply]

variable {D V} in
                                                   
def jVal (E : D) (g : V) : RingSpace K D V :=
  (1 - E) ⊗ₜ[K] (1 : MonoidAlgebra K V) + E ⊗ₜ[K] MonoidAlgebra.of K V g

variable {D V} in
lemma jVal_eq (E : D) (g : V) :
    jVal K E g = 1 + E ⊗ₜ[K] (MonoidAlgebra.of K V g - 1) := by
  simp only [jVal, sub_tmul, tmul_sub, Algebra.TensorProduct.one_def]
  abel

variable {D V} in
@[simp] lemma jVal_one (E : D) : jVal K E (1 : V) = 1 := by
  simp only [jVal_eq, map_one, sub_self, tmul_zero, add_zero]

variable {D V} in
@[simp] lemma jVal_identity (g : V) : jVal K (1 : D) g =
    1 ⊗ₜ[K] MonoidAlgebra.of K V g := by simp [jVal]

variable {D V} in
lemma jVal_mul (E : D) (hE : IsIdempotentElem E) (g h : V) :
    jVal K E (g * h) = jVal K E g * jVal K E h := by
  have hE' : E * E = E := hE
  have hleft : (1-E)*(1-E)=1-E := by noncomm_ring [hE']
  have hl : (1-E)*E=0 := by rw [sub_mul,one_mul,hE',sub_self]
  have hr : E*(1-E)=0 := by rw [mul_sub,mul_one,hE',sub_self]
  simp [jVal, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    hleft, hl, hr, hE']

variable {D V} in
                                                                   
def unitMap (E : D) (hE : IsIdempotentElem E) : V →* (RingSpace K D V)ˣ where
  toFun g :=
    { val := jVal K E g
      inv := jVal K E g⁻¹
      val_inv := by rw [← jVal_mul K E hE, mul_inv_cancel, jVal_one]
      inv_val := by rw [← jVal_mul K E hE, inv_mul_cancel, jVal_one] }
  map_one' := by apply Units.ext; exact jVal_one K E
  map_mul' g h := by apply Units.ext; exact jVal_mul K E hE g h

variable {D V} in
@[simp] lemma unitMap_val (E : D) (hE : IsIdempotentElem E) (g : V) :
    (unitMap K E hE g).val = jVal K E g := rfl

variable {D V} in
lemma jVal_mul_of_orthogonal (E P : D) (hEP : E*P=0) (g h : V) :
    jVal K E g * jVal K P h =
      1 + E ⊗ₜ[K] (MonoidAlgebra.of K V g - 1) +
        P ⊗ₜ[K] (MonoidAlgebra.of K V h - 1) := by
  simp only [jVal_eq, add_mul, mul_add, one_mul, mul_one,
    Algebra.TensorProduct.tmul_mul_tmul, hEP, zero_tmul, add_zero]

variable {D V} in
lemma unitMap_commute (E P : D) (hE : IsIdempotentElem E) (hP : IsIdempotentElem P)
    (hEP : E*P=0) (hPE : P*E=0) (g h : V) :
    Commute (unitMap K E hE g) (unitMap K P hP h) := by
  apply Units.ext
  change jVal K E g * jVal K P h = jVal K P h * jVal K E g
  rw [jVal_mul_of_orthogonal K E P hEP,
    jVal_mul_of_orthogonal K P E hPE]
  abel

variable {D V} in
lemma unitMap_addition (E P : D) (hE : IsIdempotentElem E) (hP : IsIdempotentElem P)
    (hSum : IsIdempotentElem (E+P)) (hEP : E*P=0) (g : V) :
    unitMap K (E+P) hSum g = unitMap K E hE g * unitMap K P hP g := by
  apply Units.ext
  change jVal K (E+P) g = jVal K E g * jVal K P g
  rw [jVal_mul_of_orthogonal K E P hEP, jVal_eq, add_tmul]
  abel

lemma representation_jVal (E : D) (g : V) (z : Z) :
    representation K D V Z (jVal K E g) (Finsupp.single z 1) =
      Finsupp.single z (1-E) + Finsupp.single (g • z) E := by
  simp only [jVal, map_add, LinearMap.add_apply]
  have h1 : (1 : MonoidAlgebra K V) = MonoidAlgebra.single (1:V) 1 := rfl
  rw [h1]
  simp [MonoidAlgebra.of_apply]

lemma representation_jVal_fixed (E : D) (g : V) (z : Z) (h : g • z = z) :
    representation K D V Z (jVal K E g) (Finsupp.single z 1) = Finsupp.single z 1 := by
  rw [representation_jVal, h, ← Finsupp.single_add]
  simp

lemma representation_jVal_identity (g : V) (z : Z) :
    representation K D V Z (jVal K (1 : D) g) (Finsupp.single z 1) =
      Finsupp.single (g • z) 1 := by
  simp

variable {D V} in
lemma unitMap_identity_injective [Nontrivial D] :
    Function.Injective (unitMap K (1 : D) (IsIdempotentElem.one) : V → _ ) := by
  intro g h he
  have hv := congrArg (fun u : (RingSpace K D V)ˣ =>
    representation K D V V u.val (Finsupp.single (1 : V) 1)) he
  simp only [unitMap_val, representation_jVal_identity, smul_eq_mul, mul_one] at hv
  exact (Finsupp.single_left_injective (one_ne_zero : (1:D)≠0)) hv

section Generated
variable (P : Set D) (hP : ∀ E ∈ P, IsIdempotentElem E)

def W : Subgroup (RingSpace K D V)ˣ :=
  Subgroup.closure (Set.range fun s : P × V => unitMap K s.1.val (hP s.1.val s.1.property) s.2)

def j (E : P) : V →* W K D V P hP :=
  (unitMap K E.val (hP E.val E.property)).codRestrict _ fun g =>
    Subgroup.subset_closure ⟨(E,g),rfl⟩

@[simp] lemma j_val (E : P) (g : V) :
    (j K D V P hP E g).val = unitMap K E.val (hP E.val E.property) g := rfl

instance arrayAction : MulAction (W K D V P hP) (ArraySpace D Z) :=
  MulAction.compHom (ArraySpace D Z)
    (((representation K D V Z).toMonoidHom.comp (Units.coeHom (RingSpace K D V))).comp
      (W K D V P hP).subtype)

@[simp] lemma j_smul (E : P) (g : V) (z : Z) :
    j K D V P hP E g • Finsupp.single z 1 =
      Finsupp.single z (1-E.val) + Finsupp.single (g • z) E.val :=
  representation_jVal K D V Z E.val g z

lemma j_fixed (E : P) (g : V) (z : Z) (h : g • z = z) :
    j K D V P hP E g • Finsupp.single z (1 : D) = Finsupp.single z 1 :=
  representation_jVal_fixed K D V Z E.val g z h

lemma j_identity_equivariant (hI : (1 : D) ∈ P) (g : V) (z : Z) :
    j K D V P hP ⟨1,hI⟩ g • Finsupp.single z (1 : D) = Finsupp.single (g • z) 1 :=
  representation_jVal_identity K D V Z g z

lemma j_identity_injective [Nontrivial D] (hI : (1 : D) ∈ P) :
    Function.Injective (j K D V P hP ⟨1,hI⟩) := by
  intro g h he
  exact unitMap_identity_injective K (congrArg Subtype.val he)

lemma j_commute (E F : P) (hEF : E.val*F.val=0) (hFE : F.val*E.val=0) (g h : V) :
    Commute (j K D V P hP E g) (j K D V P hP F h) := by
  apply Subtype.ext
  exact unitMap_commute K E.val F.val (hP E.val E.property) (hP F.val F.property)
    hEF hFE g h

lemma j_addition (E F : P) (hSum : E.val+F.val ∈ P) (hEF : E.val*F.val=0) (g : V) :
    j K D V P hP ⟨E.val+F.val,hSum⟩ g = j K D V P hP E g * j K D V P hP F g := by
  apply Subtype.ext
  exact unitMap_addition K E.val F.val (hP E.val E.property) (hP F.val F.property)
    (hP _ hSum) hEF g

end Generated

def point : Z → ArraySpace D Z := fun z => Finsupp.single z 1

lemma point_injective [Nontrivial D] : Function.Injective (point D Z) :=
  Finsupp.single_left_injective one_ne_zero

end IdempotentEnlargement
end

noncomputable section

end

end OAI
