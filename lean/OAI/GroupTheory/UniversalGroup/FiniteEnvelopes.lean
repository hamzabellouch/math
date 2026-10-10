import OAI.GroupTheory.UniversalGroup.SimplicialProducts

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity

section

variable {K D V : Type*} [Field K] [Ring D] [Algebra K D] [Group V]

abbrev ModelAlgebra (K D V : Type*) [Field K] [Ring D] [Algebra K D] [Group V] :=
  D ⊗[K] MonoidAlgebra K V

noncomputable def diagramElement (e : D) (v : V) : ModelAlgebra K D V :=
  (1 - e) ⊗ₜ[K] (1 : MonoidAlgebra K V) + e ⊗ₜ[K] MonoidAlgebra.of K V v

lemma diagramElement_one (e : D) : diagramElement (K := K) e (1 : V) = 1 := by
  simp only [diagramElement, map_one, TensorProduct.sub_tmul]
  rw [sub_add_cancel, Algebra.TensorProduct.one_def]

lemma diagramElement_mul (e : D) (he : e * e = e) (v w : V) :
    diagramElement (K := K) e v * diagramElement (K := K) e w =
      diagramElement (K := K) e (v * w) := by
  have h₁ : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h₂ : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h₃ : (1 - e) * (1 - e) = 1 - e := by
    rw [mul_sub, mul_one, h₁, sub_zero]
  simp only [diagramElement, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    h₁, h₂, h₃, he, TensorProduct.zero_tmul, add_zero, zero_add, one_mul, map_mul]

lemma diagramElement_eq (e : D) (v : V) :
    diagramElement (K := K) e v =
      1 + e ⊗ₜ[K] (MonoidAlgebra.of K V v - 1) := by
  simp only [diagramElement, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  rw [← Algebra.TensorProduct.one_def]
  abel

lemma diagramElement_orthogonal_mul (e p : D) (hep : e * p = 0) (v w : V) :
    diagramElement (K := K) e v * diagramElement (K := K) p w =
      1 + e ⊗ₜ[K] (MonoidAlgebra.of K V v - 1) +
        p ⊗ₜ[K] (MonoidAlgebra.of K V w - 1) := by
  rw [diagramElement_eq, diagramElement_eq]
  simp only [add_mul, mul_add, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul,
    hep, TensorProduct.zero_tmul, add_zero]

lemma diagramElement_commute (e p : D) (hep : e * p = 0) (hpe : p * e = 0)
    (v w : V) :
    Commute (diagramElement (K := K) e v) (diagramElement (K := K) p w) := by
  show _ * _ = _ * _
  rw [diagramElement_orthogonal_mul e p hep, diagramElement_orthogonal_mul p e hpe]
  abel

lemma diagramElement_add (e p : D) (hep : e * p = 0) (v : V) :
    diagramElement (K := K) (e + p) v =
      diagramElement (K := K) e v * diagramElement (K := K) p v := by
  rw [diagramElement_orthogonal_mul e p hep, diagramElement_eq,
    TensorProduct.add_tmul, add_assoc]

noncomputable def diagramHom (e : D) (he : e * e = e) : V →* (ModelAlgebra K D V)ˣ where
  toFun v :=
    { val := diagramElement e v
      inv := diagramElement e v⁻¹
      val_inv := by rw [diagramElement_mul e he, mul_inv_cancel, diagramElement_one]
      inv_val := by rw [diagramElement_mul e he, inv_mul_cancel, diagramElement_one] }
  map_one' := Units.ext (diagramElement_one e)
  map_mul' v w := Units.ext (diagramElement_mul e he v w).symm

@[simp]
lemma diagramHom_val (e : D) (he : e * e = e) (v : V) :
    (diagramHom (K := K) e he v : ModelAlgebra K D V) = diagramElement e v := rfl

lemma diagramHom_commute (e p : D) (he : e * e = e) (hp : p * p = p)
    (hep : e * p = 0) (hpe : p * e = 0) (v w : V) :
    Commute (diagramHom (K := K) e he v) (diagramHom (K := K) p hp w) := by
  apply Units.ext
  exact diagramElement_commute e p hep hpe v w

lemma diagramHom_add (e p : D) (he : e * e = e) (hp : p * p = p)
    (hep : e * p = 0) (_hpe : p * e = 0)
    (hs : (e + p) * (e + p) = e + p) (v : V) :
    diagramHom (K := K) (e + p) hs v =
      diagramHom (K := K) e he v * diagramHom (K := K) p hp v := by
  apply Units.ext
  exact diagramElement_add e p hep v

@[simp]
lemma diagramHom_identity_val (v : V) :
    (diagramHom (K := K) (1 : D) (one_mul _) v : ModelAlgebra K D V) =
      Algebra.TensorProduct.includeRight (MonoidAlgebra.of K V v) := by
  simp [diagramElement]

lemma diagramHom_identity_injective [Nontrivial D] :
    Function.Injective (diagramHom (K := K) (1 : D) (one_mul _) :
      V →* (ModelAlgebra K D V)ˣ) := by
  intro v w h
  have h' := congrArg Units.val h
  simp only [diagramHom_identity_val] at h'
  have h'' := Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap K D)) h'
  exact MonoidAlgebra.of_injective h''

end

namespace FiniteEnvelope

variable {I X : Type*}

abbrev RelationIndex (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) :=
  (I × r) ⊕ (S × X) ⊕ (T × X × X) ⊕ (T × X)

def relationWord (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) : RelationIndex r S T → FreeGroup (I × X)
  | .inl (i, w) => FreeGroup.map (fun x => (i, x)) w.val
  | .inr (.inl (s, x)) => FreeGroup.of (s.val.1, x) * (FreeGroup.of (s.val.2, x))⁻¹
  | .inr (.inr (.inl (t, x, y))) =>
      (FreeGroup.of (t.val.1, x) * FreeGroup.of (t.val.2.1, y)) *
        (FreeGroup.of (t.val.2.1, y) * FreeGroup.of (t.val.1, x))⁻¹
  | .inr (.inr (.inr (t, x))) =>
      FreeGroup.of (t.val.2.2, x) *
        (FreeGroup.of (t.val.1, x) * FreeGroup.of (t.val.2.1, x))⁻¹

abbrev relators (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) := Set.range (relationWord r S T)

abbrev Envelope (r : Set (FreeGroup X)) (S : Set (I × I))
    (T : Set (I × I × I)) := PresentedGroup (relators r S T)

instance finiteRelators [Finite I] [Finite X] (r : Set (FreeGroup X))
    [Finite r] (S : Set (I × I)) (T : Set (I × I × I)) :
    Finite (relators r S T) := Set.finite_range (relationWord r S T)

instance finitelyPresented [Finite I] [Finite X] (r : Set (FreeGroup X))
    [Finite r] (S : Set (I × I)) (T : Set (I × I × I)) :
    Group.IsFinitelyPresented (Envelope r S T) := inferInstanceAs
      (Group.IsFinitelyPresented (PresentedGroup (relators r S T)))

variable (r : Set (FreeGroup X)) (S : Set (I × I)) (T : Set (I × I × I))

def copy (i : I) : PresentedGroup r →* Envelope r S T :=
  PresentedGroup.map (FreeGroup.map fun x => (i, x))
    (fun w hw => ⟨.inl (i, ⟨w, hw⟩), rfl⟩)

@[simp]
lemma copy_of (i : I) (x : X) :
    copy r S T i (PresentedGroup.of x) = PresentedGroup.of (i, x) := rfl

lemma copy_same (s : S) : copy r S T s.val.1 = copy r S T s.val.2 := by
  apply PresentedGroup.ext
  intro x
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨.inr (.inl (s, x)), rfl⟩

lemma copy_of_commute (t : T) (x y : X) :
    Commute (copy r S T t.val.1 (.of x)) (copy r S T t.val.2.1 (.of y)) := by
  change PresentedGroup.mk _ (_ * _) = PresentedGroup.mk _ (_ * _)
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨.inr (.inr (.inl (t, x, y))), rfl⟩

lemma copy_of_sum (t : T) (x : X) :
    copy r S T t.val.2.2 (.of x) =
      copy r S T t.val.1 (.of x) * copy r S T t.val.2.1 (.of x) := by
  change PresentedGroup.mk _ _ = PresentedGroup.mk _ (_ * _)
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨.inr (.inr (.inr (t, x))), rfl⟩

variable {r S T}

lemma commute_of_generators {G : Type*} [Group G]
    (f g : PresentedGroup r →* G)
    (h : ∀ x y : X, Commute (f (.of x)) (g (.of y)))
    (u v : PresentedGroup r) : Commute (f u) (g v) := by
  have h₁ (x : X) (v : PresentedGroup r) : Commute (f (.of x)) (g v) := by
    have hv := PresentedGroup.generated_by r
      ((Subgroup.centralizer {f (.of x)}).comap g)
      (fun y => Subgroup.mem_centralizer_singleton_iff.mpr (h x y).eq.symm) v
    exact (Subgroup.mem_centralizer_singleton_iff.mp hv).symm
  have hu := PresentedGroup.generated_by r
    ((Subgroup.centralizer {g v}).comap f)
    (fun x => Subgroup.mem_centralizer_singleton_iff.mpr (h₁ x v).eq) u
  exact Subgroup.mem_centralizer_singleton_iff.mp hu

lemma copy_commute (t : T) (u v : PresentedGroup r) :
    Commute (copy r S T t.val.1 u) (copy r S T t.val.2.1 v) :=
  commute_of_generators _ _ (copy_of_commute r S T t) u v

def commutingProduct {G H : Type*} [Group G] [Group H]
    (f g : G →* H) (h : ∀ u v, Commute (f u) (g v)) : G →* H where
  toFun u := f u * g u
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul]
    exact (h v u).mul_mul_mul_comm _ _

lemma copy_sum (t : T) (u : PresentedGroup r) :
    copy r S T t.val.2.2 u = copy r S T t.val.1 u * copy r S T t.val.2.1 u := by
  have h : copy r S T t.val.2.2 =
      commutingProduct (copy r S T t.val.1) (copy r S T t.val.2.1) (copy_commute t) := by
    apply PresentedGroup.ext
    exact copy_of_sum r S T t
  exact DFunLike.congr_fun h u

variable {G : Type*} [Group G]
variable (h : I → PresentedGroup r →* G)
variable (hsame : ∀ s : S, h s.val.1 = h s.val.2)
variable (hcomm : ∀ t : T, ∀ u v, Commute (h t.val.1 u) (h t.val.2.1 v))
variable (hsum : ∀ t : T, ∀ u, h t.val.2.2 u = h t.val.1 u * h t.val.2.1 u)

include hsame hcomm hsum

lemma model_satisfies_relations : ∀ w ∈ relators r S T,
    FreeGroup.lift (fun ix : I × X => h ix.1 (.of ix.2)) w = 1 := by
  have hc (i : I) :
      (FreeGroup.lift (fun ix : I × X => h ix.1 (.of ix.2))).comp
        (FreeGroup.map fun x => (i, x)) = (h i).comp (PresentedGroup.mk r) := by
    apply FreeGroup.ext_hom
    intro x
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]
    rfl
  rintro _ ⟨idx, rfl⟩
  rcases idx with ⟨i, w⟩ | ⟨s, x⟩ | ⟨t, x, y⟩ | ⟨t, x⟩
  · change ((FreeGroup.lift _).comp (FreeGroup.map fun x => (i, x))) w.val = 1
    rw [hc]
    simp only [MonoidHom.comp_apply, PresentedGroup.one_of_mem w.property, map_one]
  · simp only [relationWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hsame s, mul_inv_cancel]
  · simp only [relationWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact mul_inv_eq_one.mpr (hcomm t (.of x) (.of y)).eq
  · simp only [relationWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact mul_inv_eq_one.mpr (hsum t (.of x))

def modelMap : Envelope r S T →* G :=
  PresentedGroup.toGroup (model_satisfies_relations h hsame hcomm hsum)

@[simp]
lemma modelMap_copy (i : I) : (modelMap h hsame hcomm hsum).comp (copy r S T i) = h i := by
  apply PresentedGroup.ext
  intro x
  simp only [MonoidHom.comp_apply, copy_of, modelMap, PresentedGroup.toGroup.of]

lemma copy_injective_of_model (i : I) (hi : Function.Injective (h i)) :
    Function.Injective (copy r S T i) := by
  have hc := modelMap_copy h hsame hcomm hsum i
  intro u v huv
  apply hi
  have hv := congrArg (modelMap h hsame hcomm hsum) huv
  simpa only [← MonoidHom.comp_apply, hc] using hv

end FiniteEnvelope

structure FiniteIdempotentSystem (D : Type) [Ring D] where
  carrier : Set D
  finite : carrier.Finite
  one_mem : (1 : D) ∈ carrier
  idempotent : ∀ e ∈ carrier, e * e = e

namespace FiniteIdempotentSystem

variable {D : Type} [Ring D]

instance (P : FiniteIdempotentSystem D) : Finite P.carrier := P.finite

def identity (P : FiniteIdempotentSystem D) : P.carrier := ⟨1, P.one_mem⟩

lemma isIdempotent (P : FiniteIdempotentSystem D) (e : P.carrier) :
    (e : D) * e = e := P.idempotent e.val e.property

end FiniteIdempotentSystem

namespace TwoEnvelope

variable {K₂ K₃ D₂ D₃ : Type}
variable [Field K₂] [Field K₃] [Ring D₂] [Ring D₃]
variable [Algebra K₂ D₂] [Algebra K₃ D₃]
variable (P₂ : FiniteIdempotentSystem D₂) (P₃ : FiniteIdempotentSystem D₃)

abbrev Index := P₂.carrier ⊕ P₃.carrier

def common : Set (Index P₂ P₃ × Index P₂ P₃) :=
  {(.inl P₂.identity, .inr P₃.identity)}

def triples : Set (Index P₂ P₃ × Index P₂ P₃ × Index P₂ P₃) :=
  {t | match t with
    | (.inl e, .inl p, .inl s) =>
        e.val * p.val = 0 ∧ p.val * e.val = 0 ∧ s.val = e.val + p.val
    | (.inr e, .inr p, .inr s) =>
        e.val * p.val = 0 ∧ p.val * e.val = 0 ∧ s.val = e.val + p.val
    | _ => False}

variable (V : Type) [Group V]

abbrev ModelGroup := (ModelAlgebra K₃ D₃ (ModelAlgebra K₂ D₂ V)ˣ)ˣ

noncomputable def family : Index P₂ P₃ → V →* ModelGroup (K₂ := K₂) (K₃ := K₃)
    (D₂ := D₂) (D₃ := D₃) V
  | .inl e =>
      (diagramHom (K := K₃) (1 : D₃) (one_mul _)).comp
        (diagramHom (K := K₂) e.val (P₂.isIdempotent e))
  | .inr e =>
      (diagramHom (K := K₃) e.val (P₃.isIdempotent e)).comp
        (diagramHom (K := K₂) (1 : D₂) (one_mul _))

variable {P₂ P₃ V}

lemma family_common (s : common P₂ P₃) :
    family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V s.val.1 = family P₂ P₃ V s.val.2 := by
  rcases s with ⟨s, hs⟩
  have hs' : s = (.inl P₂.identity, .inr P₃.identity) := hs
  subst s
  rfl

lemma family_commute (t : triples P₂ P₃) (u v : V) :
    Commute (family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V t.val.1 u)
      (family P₂ P₃ V t.val.2.1 v) := by
  rcases t with ⟨⟨e, p, s⟩, ht⟩
  rcases e with e | e <;> rcases p with p | p <;> rcases s with s | s <;>
    simp only [triples, Set.mem_ofPred_eq] at ht
  · rcases ht with ⟨hep, hpe, _⟩
    exact (diagramHom_commute (K := K₂) e.val p.val (P₂.isIdempotent e)
      (P₂.isIdempotent p) hep hpe u v).map
      (diagramHom (K := K₃) (1 : D₃) (one_mul _))
  · rcases ht with ⟨hep, hpe, _⟩
    exact diagramHom_commute (K := K₃) e.val p.val (P₃.isIdempotent e)
      (P₃.isIdempotent p) hep hpe _ _

lemma family_sum (t : triples P₂ P₃) (u : V) :
    family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V t.val.2.2 u =
      family P₂ P₃ V t.val.1 u * family P₂ P₃ V t.val.2.1 u := by
  rcases t with ⟨⟨e, p, s⟩, ht⟩
  rcases e with e | e <;> rcases p with p | p <;> rcases s with s | s <;>
    simp only [triples, Set.mem_ofPred_eq] at ht
  · rcases ht with ⟨hep, _hpe, hs⟩
    change diagramHom (K := K₃) (1 : D₃) (one_mul _) (diagramHom s.val _ u) = _
    have heq : diagramHom (K := K₂) s.val (P₂.isIdempotent s) u =
        diagramHom e.val (P₂.isIdempotent e) u * diagramHom p.val (P₂.isIdempotent p) u := by
      apply Units.ext
      change diagramElement (K := K₂) s.val u = _
      rw [hs]
      exact diagramElement_add _ _ hep u
    rw [heq, map_mul]
    rfl
  · rcases ht with ⟨hep, _hpe, hs⟩
    apply Units.ext
    let w := diagramHom (K := K₂) (1 : D₂) (one_mul _) u
    change diagramElement (K := K₃) s.val w =
      diagramElement e.val w * diagramElement p.val w
    rw [hs]
    exact diagramElement_add _ _ hep _

lemma family_identity_injective [Nontrivial D₂] [Nontrivial D₃] :
    Function.Injective (family (K₂ := K₂) (K₃ := K₃) P₂ P₃ V (.inl P₂.identity)) :=
  (diagramHom_identity_injective (K := K₃) (D := D₃)).comp
    (diagramHom_identity_injective (K := K₂) (D := D₂))

variable (K₂ K₃ P₂ P₃ V)
include K₂ K₃

theorem finite_envelope [Nontrivial D₂] [Nontrivial D₃] [Group.IsFinitelyPresented V] :
    ∃ (W : Type) (_ : Group W), Group.IsFinitelyPresented W ∧
      ∃ k : Index P₂ P₃ → V →* W,
        k (.inl P₂.identity) = k (.inr P₃.identity) ∧
        Function.Injective (k (.inl P₂.identity)) ∧
        (∀ t : triples P₂ P₃, ∀ u v,
          Commute (k t.val.1 u) (k t.val.2.1 v)) ∧
        (∀ t : triples P₂ P₃, ∀ u,
          k t.val.2.2 u = k t.val.1 u * k t.val.2.1 u) := by
  obtain ⟨n, r, hr, ⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := V)
  let : Finite r := hr
  let k (i : Index P₂ P₃) :=
    (FiniteEnvelope.copy r (common P₂ P₃) (triples P₂ P₃) i).comp e.toMonoidHom
  refine ⟨FiniteEnvelope.Envelope r (common P₂ P₃) (triples P₂ P₃),
    inferInstance, inferInstance, k, ?_, ?_, ?_, ?_⟩
  · have hc := FiniteEnvelope.copy_same r (common P₂ P₃) (triples P₂ P₃)
      ⟨(.inl P₂.identity, .inr P₃.identity), rfl⟩
    exact congrArg (fun φ => φ.comp e.toMonoidHom) hc
  · have hi := FiniteEnvelope.copy_injective_of_model
      (family (K₂ := K₂) (K₃ := K₃) P₂ P₃ (PresentedGroup r))
      family_common family_commute family_sum (.inl P₂.identity) family_identity_injective
    exact hi.comp e.injective
  · intro t u v
    exact FiniteEnvelope.copy_commute t (e u) (e v)
  · intro t u
    exact FiniteEnvelope.copy_sum t (e u)

end TwoEnvelope
end UniversalFInfinity

end OAI
