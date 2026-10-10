import Mathlib
import OAI.GroupTheory.FiniteType.ListChainsShiftOrigin

namespace OAI

noncomputable section
namespace UniformProductSupport

variable {R I S M : Type*} [Ring R] [AddCommGroup M] [Module R M]

def evaluate (i : I) : (S →₀ (I → M)) →ₗ[R] (S →₀ M) :=
  Finsupp.mapRange.linearMap (LinearMap.proj i)

@[simp] lemma evaluate_apply (i : I) (c : S →₀ (I → M)) (s : S) :
    evaluate (R := R) (I := I) (S := S) (M := M) i c s = c s i := rfl

lemma evaluate_support_subset (i : I) (c : S →₀ (I → M)) :
    (evaluate (R := R) (I := I) (S := S) (M := M) i c).support ⊆ c.support := by
  change (Finsupp.mapRange (fun m : I → M => m i) rfl c).support ⊆ c.support
  exact Finsupp.support_mapRange

lemma evaluate_injective : Function.Injective
    (fun c : S →₀ (I → M) => fun i => evaluate (R := R) (I := I) (S := S) (M := M) i c) := by
  intro c d h
  ext s i
  exact congrArg (fun v : I → S →₀ M => v i s) h

theorem exists_lift_iff (z : I → S →₀ M) :
    (∃ c : S →₀ (I → M), ∀ i, evaluate (R := R) (I := I) (S := S) (M := M) i c = z i) ↔
      ∃ T : Finset S, ∀ i, (z i).support ⊆ T := by
  classical
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c.support,?_⟩
    intro i
    rw [← hc i]
    exact evaluate_support_subset i c
  · rintro ⟨T,hT⟩
    let c : S →₀ (I → M) := Finsupp.onFinset T (fun s i => z i s) (by
      intro s hs
      by_contra h
      apply hs
      funext i
      exact Finsupp.notMem_support_iff.mp (fun hz => h (hT i hz)))
    refine ⟨c,?_⟩
    intro i
    ext s
    rfl

def boundedFamily : Submodule R (I → S →₀ M) where
  carrier := {z | ∃ T : Finset S, ∀ i, (z i).support ⊆ T}
  zero_mem' := ⟨∅,by simp⟩
  add_mem' := by
    classical
    rintro z w ⟨T,hT⟩ ⟨U,hU⟩
    refine ⟨T ∪ U,?_⟩
    intro i s hs
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
    · exact Finset.mem_union_left _ (hT i h)
    · exact Finset.mem_union_right _ (hU i h)
  smul_mem' := by
    rintro r z ⟨T,hT⟩
    refine ⟨T,?_⟩
    intro i s hs
    exact hT i (Finsupp.support_smul hs)

def toFamily : (S →₀ (I → M)) →ₗ[R] boundedFamily (R := R) (I := I) (S := S) (M := M) :=
  (LinearMap.pi fun i => evaluate (R := R) (I := I) (S := S) (M := M) i).codRestrict _ fun c =>
    ⟨c.support,fun i => evaluate_support_subset i c⟩

lemma toFamily_bijective : Function.Bijective (toFamily (R := R) (I := I) (S := S) (M := M)) := by
  constructor
  · intro c d h
    exact evaluate_injective (R := R) (congrArg Subtype.val h)
  · intro z
    obtain ⟨c,hc⟩ := (exists_lift_iff (R := R) z.val).mpr z.property
    refine ⟨c,?_⟩
    apply Subtype.ext
    exact funext hc

def familyEquiv : (S →₀ (I → M)) ≃ₗ[R] boundedFamily (R := R) (I := I) (S := S) (M := M) :=
  LinearEquiv.ofBijective toFamily toFamily_bijective

end UniformProductSupport

namespace ListChains
section

variable (G I C : Type*) [Group G]

theorem product_chain_realization {n : ℕ} (z : I → C →₀ Chain G)
    (hd : ∀ i c, z i c ∈ degreeModule G n) :
    (∃ c : List G →₀ (I → (C × G →₀ ℤ)),
      ∀ i, UniformProductSupport.evaluate (R := ℤ) (S := List G) (I := I) (M := C × G →₀ ℤ) i c = shapeCoordinates G C (z i)) ↔
    (∃ A : Set G, IsBound G A ∧ ∀ i c, z i c ∈ controlledModule G A) := by
  classical
  rw [UniformProductSupport.exists_lift_iff]
  constructor
  · rintro ⟨T,hT⟩
    obtain ⟨B,hB,h⟩ := finite_shapes_bound G T.finite_toSet
    refine ⟨B,hB,?_⟩
    intro i c s hs
    apply h s
    exact (shapeCoordinates_support_iff G C (z i) (↑T)).mp (hT i) c s hs
  · rintro ⟨A,hA,hz⟩
    let T := (simplexTypes_finite G hA.finite n).toFinset
    refine ⟨T,?_⟩
    intro i
    apply (shapeCoordinates_support_iff G C (z i) (↑T)).mpr
    intro c s hs
    change relativeType G s ∈ (simplexTypes_finite G hA.finite n).toFinset
    rw [Set.Finite.mem_toFinset]
    have h := relativeType_mem G (hz i c hs)
    rwa [hd i c hs] at h

end

variable (G I C : Type*) [Group G]

abbrev Shape (n : ℕ) := {l : List G // l.length = n}
abbrev CoefficientProduct := I → (C × G →₀ ℤ)

def realizeShapes : (List G →₀ CoefficientProduct G I C) →ₗ[ℤ] ProductAmbient G I C :=
  LinearMap.pi (fun i => (shapeCoordinates G C).symm.toLinearMap.comp
    (UniformProductSupport.evaluate (R := ℤ) i))

@[simp] lemma shapeCoordinates_realize (a : List G →₀ CoefficientProduct G I C) (i : I) :
    shapeCoordinates G C (realizeShapes G I C a i) = UniformProductSupport.evaluate (R := ℤ) (S := List G) (M := C × G →₀ ℤ) i a := by
  exact (shapeCoordinates G C).apply_symm_apply _

lemma realizeShapes_apply_relative (a : List G →₀ CoefficientProduct G I C)
    (i : I) (c : C) (s : Simplex G) :
    realizeShapes G I C a i c s = a (relativeType G s) i (c,s.1) := by
  rw [← shapeCoordinates_at_relative,shapeCoordinates_realize]
  rfl

lemma realizeShapes_apply (a : List G →₀ CoefficientProduct G I C)
    (i : I) (c : C) (g : G) (l : List G) :
    realizeShapes G I C a i c (g,l.map (fun x => g*x)) = a l i (c,g) := by
  rw [realizeShapes_apply_relative,relativeType_translate]

lemma realizeShapes_injective : Function.Injective (realizeShapes G I C) := by
  intro a b h
  apply UniformProductSupport.evaluate_injective (R := ℤ)
  funext i
  change UniformProductSupport.evaluate (R := ℤ) (S := List G) (M := C × G →₀ ℤ) i a =
    UniformProductSupport.evaluate (R := ℤ) (S := List G) (M := C × G →₀ ℤ) i b
  rw [← shapeCoordinates_realize,← shapeCoordinates_realize]
  exact congrArg (shapeCoordinates G C) (congrFun h i)

lemma realizeShapes_bounded (a : List G →₀ CoefficientProduct G I C) :
    realizeShapes G I C a ∈ boundedProducts G I C := by
  classical
  obtain ⟨B,hB,h⟩ := finite_shapes_bound G a.support.finite_toSet
  refine ⟨B,hB,?_⟩
  intro i c s hs
  apply h s
  apply Finsupp.mem_support_iff.mpr
  intro hz
  apply Finsupp.mem_support_iff.mp hs
  rw [realizeShapes_apply_relative,hz]
  rfl

lemma realizeShapes_degree_iff (n : ℕ) (a : List G →₀ CoefficientProduct G I C) :
    realizeShapes G I C a ∈ degreeProducts G I C n ↔
      a ∈ Finsupp.supported (CoefficientProduct G I C) ℤ {l : List G | l.length = n} := by
  constructor
  · intro h l hl
    by_contra hn
    apply Finsupp.mem_support_iff.mp hl
    ext i ⟨c,g⟩
    rw [← realizeShapes_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have he := h i c hs
    exact hn (by simpa [degree] using he)
  · intro h i c s hs
    have hn : a (relativeType G s) ≠ 0 := by
      intro hz
      apply Finsupp.mem_support_iff.mp hs
      rw [realizeShapes_apply_relative,hz]
      rfl
    have he := h (Finsupp.mem_support_iff.mpr hn)
    simpa using he

def shapeDomain (n : ℕ) :=
  Finsupp.supported (CoefficientProduct G I C) ℤ {l : List G | l.length = n}

def realizeDegree (n : ℕ) : shapeDomain G I C n →ₗ[ℤ] productChains G I C n :=
  ((realizeShapes G I C).comp (shapeDomain G I C n).subtype).codRestrict _ fun a =>
    ⟨realizeShapes_bounded G I C a.val,(realizeShapes_degree_iff G I C n a.val).mpr a.property⟩

lemma realizeDegree_bijective (n : ℕ) : Function.Bijective (realizeDegree G I C n) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact realizeShapes_injective G I C (congrArg Subtype.val h)
  · intro z
    obtain ⟨a,ha⟩ := (product_chain_realization G I C z.val (fun i c => z.property.2 i c)).mpr z.property.1
    have he : realizeShapes G I C a = z.val := by
      funext i
      apply (shapeCoordinates G C).injective
      rw [shapeCoordinates_realize,ha i]
    have hd : a ∈ shapeDomain G I C n :=
      (realizeShapes_degree_iff G I C n a).mp (he ▸ z.property.2)
    exact ⟨⟨a,hd⟩,Subtype.ext he⟩

def productShapeEquiv (n : ℕ) : (Shape G n →₀ CoefficientProduct G I C) ≃ₗ[ℤ]
    productChains G I C n :=
  (Finsupp.supportedEquivFinsupp {l : List G | l.length = n}).symm.trans
    (LinearEquiv.ofBijective (realizeDegree G I C n) (realizeDegree_bijective G I C n))

def tupleShapeEquiv (n : ℕ) : (Fin n → G) ≃ Shape G n where
  toFun s := ⟨List.ofFn s,List.length_ofFn⟩
  invFun l := fun i => l.val.get ⟨i.val,by have h := l.property; omega⟩
  left_inv := by intro s;funext i;simp
  right_inv := by
    rintro ⟨l,hl⟩
    subst n
    apply Subtype.ext
    exact List.ofFn_getElem

def productTupleEquiv (n : ℕ) : ((Fin n → G) →₀ CoefficientProduct G I C) ≃ₗ[ℤ]
    productChains G I C n :=
  (Finsupp.lcongr (tupleShapeEquiv G n) (LinearEquiv.refl ℤ _)).trans (productShapeEquiv G I C n)

end ListChains

end

end OAI
