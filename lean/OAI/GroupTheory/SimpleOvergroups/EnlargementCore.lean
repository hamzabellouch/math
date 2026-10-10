import Mathlib

namespace OAI

noncomputable section
namespace SourceEnlargement

variable {D V Z : Type*} [Ring D] [Group V] [MulAction V Z]

def value (E : D) (g : V) : MonoidAlgebra D V :=
  MonoidAlgebra.single 1 (1 - E) + MonoidAlgebra.single g E

@[simp] lemma value_one (E : D) : value E (1 : V) = 1 := by
  simp only [value, ← MonoidAlgebra.single_add, sub_add_cancel]
  rfl

lemma value_mul (E : D) (hE : E * E = E) (g h : V) :
    value E g * value E h = value E (g * h) := by
  have ha : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have hb : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have hc : (1 - E) * (1 - E) = 1 - E := by
    rw [mul_sub, mul_one, ha, sub_zero]
  simp only [value, add_mul, mul_add, MonoidAlgebra.single_mul_single,
    one_mul, mul_one, ha, hb, hc, hE, MonoidAlgebra.single_zero, add_zero, zero_add]

def unitMap (E : D) (hE : E * E = E) : V →* (MonoidAlgebra D V)ˣ where
  toFun g :=
    { val := value E g
      inv := value E g⁻¹
      val_inv := by rw [value_mul E hE, mul_inv_cancel, value_one]
      inv_val := by rw [value_mul E hE, inv_mul_cancel, value_one] }
  map_one' := Units.ext (value_one E)
  map_mul' g h := Units.ext (value_mul E hE g h).symm

@[simp] lemma unitMap_val (E : D) (hE : E * E = E) (g : V) :
    (unitMap E hE g).val = value E g := rfl

@[simp] lemma value_identity (g : V) :
    value (1 : D) g = MonoidAlgebra.single g 1 := by simp [value]

lemma unitMap_identity_injective [Nontrivial D] :
    Function.Injective (unitMap (V := V) (1 : D) (one_mul 1)) := by
  intro g h hgh
  have he := congrArg Units.val hgh
  simp only [unitMap_val, value_identity] at he
  exact MonoidAlgebra.single_left_injective one_ne_zero he

lemma complement_product (E P : D) (hEP : E * P = 0) :
    (1 - E) * (1 - P) = 1 - (E + P) := by
  calc
    (1 - E) * (1 - P) = 1 - (E + P) + E * P := by noncomm_ring
    _ = 1 - (E + P) := by rw [hEP, add_zero]

lemma value_mul_orthogonal (E P : D) (hEP : E * P = 0) (g h : V) :
    value E g * value P h =
      MonoidAlgebra.single 1 (1 - (E + P)) +
        MonoidAlgebra.single h P + MonoidAlgebra.single g E := by
  have ha : (1 - E) * P = P := by rw [sub_mul, one_mul, hEP, sub_zero]
  have hb : E * (1 - P) = E := by rw [mul_sub, mul_one, hEP, sub_zero]
  simp only [value, add_mul, mul_add, MonoidAlgebra.single_mul_single,
    one_mul, mul_one, complement_product E P hEP, ha, hb, hEP,
    MonoidAlgebra.single_zero, add_zero]
  abel

lemma unitMap_commute (E P : D) (hE : E * E = E) (hP : P * P = P)
    (hEP : E * P = 0) (hPE : P * E = 0) (g h : V) :
    Commute (unitMap E hE g) (unitMap P hP h) := by
  apply Units.ext
  change value E g * value P h = value P h * value E g
  rw [value_mul_orthogonal E P hEP, value_mul_orthogonal P E hPE, add_comm P E]
  abel

lemma unitMap_add (E P : D) (hE : E * E = E) (hP : P * P = P)
    (hSum : (E + P) * (E + P) = E + P) (hEP : E * P = 0) (g : V) :
    unitMap (E + P) hSum g = unitMap E hE g * unitMap P hP g := by
  apply Units.ext
  change value (E + P) g = value E g * value P g
  rw [value_mul_orthogonal E P hEP, value, MonoidAlgebra.single_add]
  abel

def indexAction : V →* AddMonoid.End (Z →₀ D) where
  toFun g := Finsupp.mapDomain.addMonoidHom (fun z => g • z)
  map_one' := by
    apply AddMonoidHom.ext
    intro a
    change Finsupp.mapDomain (fun z : Z => (1 : V) • z) a = a
    simp only [one_smul]
    exact Finsupp.mapDomain_id
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro a
    change Finsupp.mapDomain (fun z : Z => (g * h) • z) a =
      Finsupp.mapDomain (fun z => g • z) (Finsupp.mapDomain (fun z => h • z) a)
    rw [← Finsupp.mapDomain_comp]
    simp only [mul_smul, Function.comp_def]

@[simp] lemma indexAction_single (g : V) (z : Z) (d : D) :
    indexAction g (Finsupp.single z d) = Finsupp.single (g • z) d :=
  Finsupp.mapDomain_single

lemma scalar_index_commute (d : D) (g : V) :
    Commute (Module.toAddMonoidEnd D (Z →₀ D) d) (indexAction g) := by
  apply Finsupp.addHom_ext
  intro z a
  change d • indexAction g (Finsupp.single z a) = indexAction g (d • Finsupp.single z a)
  simp only [indexAction_single, Finsupp.smul_single]

def ringAction : MonoidAlgebra D V →+* AddMonoid.End (Z →₀ D) :=
  MonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd D (Z →₀ D))
    indexAction scalar_index_commute

@[simp] lemma ringAction_single (g : V) (d : D) (z : Z) (a : D) :
    ringAction (MonoidAlgebra.single g d) (Finsupp.single z a) =
      Finsupp.single (g • z) (d * a) := by
  rw [ringAction, MonoidAlgebra.liftNCRingHom_single]
  change d • indexAction g (Finsupp.single z a) = _
  simp only [indexAction_single, Finsupp.smul_single, smul_eq_mul]

instance unitsAction : MulAction (MonoidAlgebra D V)ˣ (Z →₀ D) where
  smul w a := ringAction w.val a
  one_smul a := by change ringAction 1 a = a; rw [map_one]; rfl
  mul_smul w v a := by
    change ringAction (w.val * v.val) a = ringAction w.val (ringAction v.val a)
    rw [map_mul]; rfl

lemma unitMap_basis (E : D) (hE : E * E = E) (g : V) (z : Z) :
    unitMap E hE g • Finsupp.single z (1 : D) =
      Finsupp.single z (1 - E) + Finsupp.single (g • z) E := by
  change ringAction (value E g) (Finsupp.single z (1 : D)) = _
  rw [value, map_add]
  change ringAction (MonoidAlgebra.single 1 (1 - E)) (Finsupp.single z (1 : D)) +
      ringAction (MonoidAlgebra.single g E) (Finsupp.single z (1 : D)) = _
  simp only [ringAction_single, one_smul, mul_one]

lemma unitMap_fixes (E : D) (hE : E * E = E) (g : V) (z : Z)
    (hz : g • z = z) :
    unitMap E hE g • Finsupp.single z (1 : D) = Finsupp.single z 1 := by
  rw [unitMap_basis, hz, ← Finsupp.single_add, sub_add_cancel]

def group (P : Set D) (hP : ∀ E ∈ P, E * E = E) : Subgroup (MonoidAlgebra D V)ˣ :=
  Subgroup.closure {w | ∃ E : P, ∃ g : V, w = unitMap E.val (hP E.val E.property) g}

variable (P : Set D) (hP : ∀ E ∈ P, E * E = E)

def map (E : P) : V →* group (V := V) P hP :=
  (unitMap E.val (hP E.val E.property)).codRestrict _ fun g =>
    Subgroup.subset_closure ⟨E, g, rfl⟩

@[simp] lemma map_val (E : P) (g : V) :
    (map P hP E g).val = unitMap E.val (hP E.val E.property) g := rfl

lemma map_identity_injective [Nontrivial D] (h1 : 1 ∈ P) :
    Function.Injective (map (V := V) P hP ⟨1, h1⟩) := by
  intro g h he
  apply unitMap_identity_injective (D := D)
  exact congrArg Subtype.val he

lemma map_identity_basis (h1 : 1 ∈ P) (g : V) (z : Z) :
    map P hP ⟨1, h1⟩ g • Finsupp.single z (1 : D) = Finsupp.single (g • z) 1 := by
  change unitMap (1 : D) (hP 1 h1) g • Finsupp.single z (1 : D) = _
  simp [unitMap_basis]

lemma basis_injective [Nontrivial D] :
    Function.Injective (fun z : Z => Finsupp.single z (1 : D)) :=
  Finsupp.single_left_injective one_ne_zero

lemma map_fixes (E : P) (g : V) (z : Z) (hz : g • z = z) :
    map P hP E g • Finsupp.single z (1 : D) = Finsupp.single z 1 :=
  unitMap_fixes E.val (hP E.val E.property) g z hz

lemma map_commute (E E' : P) (hEP : E.val * E'.val = 0)
    (hPE : E'.val * E.val = 0) (g h : V) :
    Commute (map P hP E g) (map P hP E' h) := by
  apply Subtype.ext
  exact (unitMap_commute E.val E'.val (hP _ E.property) (hP _ E'.property) hEP hPE g h).eq

lemma map_add (E E' : P) (hSum : E.val + E'.val ∈ P)
    (hEP : E.val * E'.val = 0) (g : V) :
    map P hP ⟨E.val + E'.val, hSum⟩ g = map P hP E g * map P hP E' g := by
  apply Subtype.ext
  exact unitMap_add E.val E'.val (hP _ E.property) (hP _ E'.property) (hP _ hSum) hEP g

end SourceEnlargement
end

end OAI
