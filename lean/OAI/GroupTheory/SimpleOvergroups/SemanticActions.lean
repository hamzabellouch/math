import Mathlib
import OAI.GroupTheory.FiniteType.ClassifyingSpacesFiniteExtensionGeometricFromProducts
import OAI.GroupTheory.FiniteType.StageConstruction
import OAI.GroupTheory.SimpleOvergroups.MatrixEffective

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames

def globalCalculus {V Y K L : Type*} [Group V] [MulAction V Y]
    (kg : V → K) (kx : Y → L) (hg : Function.Injective kg) (hx : Function.Injective kx)
    (m : ℕ) : ActionCalculus V Y K L m where
  group := ⟨fun _ => Set.univ, fun _ _ _ => Set.Subset.refl _, kg⟩
  point := ⟨fun _ => Set.univ, fun _ _ _ => Set.Subset.refl _, kx⟩
  one_mem _ := Set.mem_univ _
  inv_mem _ := Set.mem_univ _
  mul_mem _ _ := Set.mem_univ _
  smul_mem _ _ := Set.mem_univ _
  inv_congr h := congrArg (fun v => kg v⁻¹) (hg h)
  mul_congr _ _ _ _ _ _ h h' := by rw [hg h,hg h']
  smul_congr _ _ _ _ _ _ h h' := by rw [hg h,hx h']

namespace SemanticMatrix
open StageConstruction MatrixNames
abbrev Raw (k A : Type*) [CommRing k] := MonoidAlgebra k (FreeMonoid A)

def seven : Fin 7 ≃ Seven := Fintype.equivOfCardEq (by simp [Seven])

variable {k A R : Type*} [CommRing k] [Ring R] [Algebra k R]
    (π : Raw k A →ₐ[k] R)

def matrixMap : Matrix (Fin 7) (Fin 7) (Raw k A) →+* Matrix Seven Seven R :=
  (Matrix.reindexRingEquiv R seven).toRingHom.comp π.toRingHom.mapMatrix

@[simp] theorem matrixMap_apply (a : Matrix (Fin 7) (Fin 7) (Raw k A)) (i j : Seven) :
    matrixMap π a i j = π (a (seven.symm i) (seven.symm j)) := rfl

def columnMap (x : Fin 7 → Raw k A) : Seven → R := fun i => π (x (seven.symm i))

 theorem matrixMap_mulVec (a : Matrix (Fin 7) (Fin 7) (Raw k A)) (x : Fin 7 → Raw k A) :
    (matrixMap π a).mulVec (columnMap π x) = columnMap π (a.mulVec x) := by
  funext i
  simp only [Matrix.mulVec,dotProduct,columnMap,matrixMap_apply,map_sum,map_mul]
  exact Equiv.sum_comp seven.symm (fun j => π (a (seven.symm i) j) * π (x j))

def rootValue (r : MatrixWords.Root k A 7) : Q R :=
  if h : r.1 ≠ r.2.1 then
    ⟨NoncommElementary.root (seven r.1) (seven r.2.1) (seven.injective.ne h) (π (Polynomial.value r.2.2)),
      NoncommElementary.root_mem _ _ _ _⟩
  else 1

def groupValue (w : MatrixWords.Word k A 7) : Q R := (w.map (rootValue π)).prod

def pointValue (x : MatrixWords.Point k A 7) : X R := groupValue π x.1 • columnMap π (columnValue x.2)

@[simp] theorem rootValue_inverse (r : MatrixWords.Root k A 7) :
    rootValue π (MatrixWords.rootInv r) = (rootValue π r)⁻¹ := by
  by_cases h : r.1 ≠ r.2.1
  · apply Subtype.ext
    simp [rootValue,MatrixWords.rootInv,h,NoncommElementary.root_inv]
  · simp [rootValue,MatrixWords.rootInv,h]

@[simp] theorem groupValue_nil : groupValue π [] = 1 := rfl
@[simp] theorem groupValue_append (a b : MatrixWords.Word k A 7) :
    groupValue π (a++b) = groupValue π a * groupValue π b := by simp [groupValue]
@[simp] theorem groupValue_cons (r : MatrixWords.Root k A 7) (w : MatrixWords.Word k A 7) :
    groupValue π (r::w) = rootValue π r * groupValue π w := rfl
@[simp] theorem groupValue_inverse (w : MatrixWords.Word k A 7) :
    groupValue π (MatrixWords.inverse w) = (groupValue π w)⁻¹ := by
  induction w with
  | nil => simp
  | cons r w ih => simp [ih,mul_inv_rev]

@[simp] theorem pointValue_act (w : MatrixWords.Word k A 7) (x : MatrixWords.Point k A 7) :
    pointValue π (w++x.1,x.2) = groupValue π w • pointValue π x := by
  simp only [pointValue,groupValue_append]
  exact mul_smul (groupValue π w) (groupValue π x.1)
    (show X R from columnMap π (columnValue x.2))

 theorem rootValue_matrix (r : MatrixWords.Root k A 7) :
    (rootValue π r).val.val = matrixMap π (MatrixWords.rootValue r).val := by
  by_cases h : r.1 ≠ r.2.1
  · ext i j
    simp only [rootValue,dite_eq_left h,NoncommElementary.root_val,MatrixWords.rootValue,
      FiniteAlgebraicEnvelopes.Steinberg.elementary_val,matrixMap_apply,map_add,
      Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]
    have hi : r.1 = seven.symm i ↔ seven r.1 = i := seven.eq_symm_apply
    have hj : r.2.1 = seven.symm j ↔ seven r.2.1 = j := seven.eq_symm_apply
    simp only [apply_ite,map_one,map_zero,seven.symm.injective.eq_iff,hi,hj]
    split <;> simp_all only
  · simp [rootValue,MatrixWords.rootValue,h]

 theorem groupValue_matrix (w : MatrixWords.Word k A 7) :
    (groupValue π w).val.val = matrixMap π (MatrixWords.groupValue w).val := by
  induction w with
  | nil => simp
  | cons r w ih => simp only [groupValue_cons,MatrixWords.groupValue_cons,Subgroup.coe_mul,
      Units.val_mul,map_mul,rootValue_matrix,ih]

attribute [local instance] WordCalculus.rawMatrixAction
 theorem pointValue_column (x : MatrixWords.Point k A 7) :
    pointValue π x = columnMap π (MatrixWords.pointValue x) := by
  change (groupValue π x.1).val.val.mulVec _ = _
  rw [groupValue_matrix,matrixMap_mulVec]
  rfl

 theorem groupValue_surjective (hπ : Function.Surjective π) : Function.Surjective (groupValue π) := by
  intro g
  have h : ∃ w, (groupValue π w).val = g.val := by
    apply Subgroup.closure_induction (p:=fun g _ => ∃ w, (groupValue π w).val = g) (hx:=g.property)
    · rintro g ⟨i,j,h,a,rfl⟩
      obtain ⟨a,ha⟩ := hπ a
      obtain ⟨p,rfl⟩ := Polynomial.value_surjective a
      refine ⟨[(seven.symm i,seven.symm j,p)],?_⟩
      simp only [groupValue_cons,groupValue_nil,mul_one,rootValue]
      rw [dite_eq_left (seven.symm.injective.ne h)]
      simp [ha]
    · exact ⟨[],rfl⟩
    · rintro a b ha hb ⟨u,rfl⟩ ⟨v,rfl⟩
      exact ⟨u++v,congrArg Subtype.val (groupValue_append π u v)⟩
    · rintro a ha ⟨u,rfl⟩
      exact ⟨MatrixWords.inverse u,congrArg Subtype.val (groupValue_inverse π u)⟩
  obtain ⟨w,hw⟩ := h
  exact ⟨w,Subtype.ext hw⟩

 theorem pointValue_surjective (hπ : Function.Surjective π) : Function.Surjective (pointValue π) := by
  intro x
  have h : ∀ i : Fin 7, ∃ p : Polynomial.Name k A, π (Polynomial.value p) = x (seven i) :=
    fun i => by
      obtain ⟨a,ha⟩ := hπ (x (seven i))
      obtain ⟨p,rfl⟩ := Polynomial.value_surjective a
      exact ⟨p,ha⟩
  choose p hp using h
  refine ⟨([],p),?_⟩
  simp only [pointValue,groupValue_nil]
  refine (one_smul (Q R) (show X R from columnMap π (columnValue p))).trans ?_
  funext i
  exact (hp (seven.symm i)).trans (congrArg x (seven.apply_symm_apply i))

variable [Primcodable A] [Primcodable k] [Finite k]
variable (σ : R → Raw k A) (hσ : Function.Injective σ)

def groupKey (g : Q R) : (Fin 7 → Fin 7 → ℕ) × (Fin 7 → Fin 7 → ℕ) :=
  MatrixWords.pairedKey (fun i j => σ (g.val.val (seven i) (seven j)),
    fun i j => σ (g.val.inv (seven i) (seven j)))

def pointKey (x : X R) : Fin 7 → ℕ := columnKey (fun i => σ (x (seven i)))

omit [Algebra k R] in
 include hσ in
 theorem groupKey_injective [Algebra k R] : Function.Injective (groupKey σ) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  funext i j
  have hh := congrFun (congrFun (congrArg Prod.fst (MatrixWords.pairedKey_injective he)) (seven.symm i)) (seven.symm j)
  exact hσ (by simpa only [seven.apply_symm_apply] using hh)

omit [Ring R] [Algebra k R] [Finite k] in
 include hσ in
 theorem pointKey_injective [Ring R] [Algebra k R] [Finite k] :
    Function.Injective (pointKey σ) := by
  intro x y he
  funext i
  have hh := congrFun (columnKey_injective he) (seven.symm i)
  exact hσ (by simpa only [seven.apply_symm_apply] using hh)

def calculus (m : ℕ) := globalCalculus (groupKey σ) (pointKey σ)
  (groupKey_injective σ hσ) (pointKey_injective σ hσ) m

def interpretation (grade : List A → ℕ) (m : ℕ) :
    NamedAction.Interpretation (MatrixWords.nameOperations (k:=k) (n:=7) grade) (calculus σ hσ m) where
  group w := ⟨groupValue π w,MatrixWords.gcost grade w,Set.mem_univ _⟩
  point x := ⟨pointValue π x,MatrixWords.xcost grade x,Set.mem_univ _⟩
  group_cost _ := rfl
  point_cost _ := rfl
  one := WithBound.ext' (groupValue_nil π) rfl
  mul a b := WithBound.ext' (groupValue_append π a b) (MatrixWords.gcost_append grade a b)
  inv w := WithBound.ext' (groupValue_inverse π w) (MatrixWords.gcost_inverse grade w)
  act g x := WithBound.ext' (pointValue_act π g x)
    (by change MatrixWords.gcost _ (g++x.1) + columnCost _ x.2 =
          MatrixWords.gcost grade g + MatrixWords.xcost grade x
        simp [MatrixWords.gcost_append,MatrixWords.xcost,Nat.add_assoc])

 theorem gkey_eq {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (w : MatrixWords.Word k A 7) :
    (interpretation π σ hσ (MatrixWords.grade C) m).gkey w =
      (MatrixWords.interpretation C).gkey w := by
  change MatrixWords.pairedKey _ = MatrixWords.pairedKey _
  congr 1
  apply Prod.ext
  · funext i j
    change σ ((groupValue π w).val.val (seven i) (seven j)) =
      C.collect k ((MatrixWords.groupValue w).val i j)
    rw [groupValue_matrix, matrixMap_apply]
    simpa only [seven.symm_apply_apply] using hs ((MatrixWords.groupValue w).val i j)
  · funext i j
    change σ (((groupValue π w)⁻¹).val.val (seven i) (seven j)) =
      C.collect k ((MatrixWords.groupValue w).inv i j)
    rw [← groupValue_inverse,groupValue_matrix,matrixMap_apply]
    simpa only [seven.symm_apply_apply,MatrixWords.groupValue_inverse, ← Units.inv_eq_val_inv] using
      hs ((MatrixWords.groupValue w).inv i j)

 theorem xkey_eq {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (x : MatrixWords.Point k A 7) :
    (interpretation π σ hσ (MatrixWords.grade C) m).xkey x =
      (MatrixWords.interpretation C).xkey x := by
  change columnKey _ = columnKey _
  congr 1
  funext i
  change σ (pointValue π x (seven i)) = C.collect k (MatrixWords.pointValue x i)
  rw [pointValue_column]
  simpa only [columnMap,seven.symm_apply_apply] using hs (MatrixWords.pointValue x i)

 theorem partialGroupKey_full {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (f : List A → Part (List A))
    (w : MatrixWords.Word k A 7) {d : ℕ} (hw : MatrixWords.gcost (MatrixWords.grade C) w ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation π σ hσ (MatrixWords.grade C) m).gkey w ∈
      MatrixWords.partialGroupKey C.omega.toList f w := by
  rw [gkey_eq π σ hσ C hs]
  exact MatrixWords.partialGroupKey_full C f w hw hf

 theorem partialPointKey_full {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (f : List A → Part (List A))
    (x : MatrixWords.Point k A 7) {d : ℕ} (hx : MatrixWords.xcost (MatrixWords.grade C) x ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation π σ hσ (MatrixWords.grade C) m).xkey x ∈
      MatrixWords.partialPointKey C.omega.toList f x := by
  rw [xkey_eq π σ hσ C hs]
  exact MatrixWords.partialPointKey_full C f x hx hf

end SemanticMatrix
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
