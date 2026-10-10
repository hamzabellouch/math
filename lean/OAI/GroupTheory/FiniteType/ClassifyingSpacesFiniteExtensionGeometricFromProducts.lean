import Mathlib
import OAI.GroupTheory.FiniteType.FiniteIndexRegular

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups

theorem finite_extension_geometric_from_products {L : Type} [Group L]
    (K : Subgroup L) [K.Normal] [Finite (L ⧸ K)] [Group.IsFinitelyPresented K]
    (hn : ∀ (I : Type) (n : ℕ), 2 ≤ n → CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ K I) n)) : HasTypeFInfty L := by
  classical
  let := Fintype.ofFinite (FiniteExtension.Q K)
  let := FiniteExtension.finitelyPresented K
  exact geometric_product_criterion L (FiniteIndexRegular.product_vanishing K · hn)

theorem finite_extension_of_ascending_torus
    {U P L : Type} [Group U] [Group P] [Group L]
    [Group.IsFinitelyPresented P]
    (a : U →* P) (b : P →* U) (hf : Function.Injective (b.comp a))
    (F₂ : ListChains.IdempotentSplittings U (ZMod 2) (b.comp a))
    (F₃ : ListChains.IdempotentSplittings U (ZMod 3) (b.comp a))
    (K : Subgroup L) [K.Normal] [Finite (L ⧸ K)]
    (e : AscendingHNN.Torus (b.comp a) hf ≃* K) : HasTypeFInfty L := by
  have := AscendingHNN.finitelyPresented_of_factorization (b.comp a) hf a b rfl
  have : Group.IsFinitelyPresented K := Group.IsFinitelyPresented.equiv e
  have : Group.FG P := by
    obtain ⟨n,φ,hφ,_⟩ := (inferInstance : Group.IsFinitelyPresented P).out
    exact Group.fg_of_surjective hφ
  apply finite_extension_geometric_from_products K
  intro I n hn
  apply RegularProductR.vanishing_relabel e I _ n hn
  intro J m hm
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 2 r]
  change CategoryTheory.Limits.IsZero
    (groupHomology (RegularProduct.rep (AscendingHNN.Torus (b.comp a) hf) J) (r+2))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (AscendingHNN.regular_product_homology_vanishes a b hf F₂ F₃ J r x).trans
    (AscendingHNN.regular_product_homology_vanishes a b hf F₂ F₃ J r y).symm⟩

end SimpleFInftyOvergroups

open scoped Pointwise
namespace SetwiseRestriction
variable {G X : Type} [Group G] [MulAction G X]

def perm (s : Set X) (g : MulAction.stabilizer G s) : Equiv.Perm s where
  toFun x := ⟨(g : G) • x.val, by
    have hg : (g : G) • s = s := MulAction.mem_stabilizer_iff.mp g.property
    exact hg.subset (Set.smul_mem_smul_set x.property)⟩
  invFun x := ⟨((g : G)⁻¹) • x.val, by
    have hg : (g : G)⁻¹ • s = s := MulAction.mem_stabilizer_iff.mp g⁻¹.property
    exact hg.subset (Set.smul_mem_smul_set x.property)⟩
  left_inv x := Subtype.ext (inv_smul_smul (g : G) x.val)
  right_inv x := Subtype.ext (smul_inv_smul (g : G) x.val)

def hom (s : Set X) : MulAction.stabilizer G s →* Equiv.Perm s where
  toFun := perm s
  map_one' := by ext x; exact one_smul G x.val
  map_mul' g h := by ext x; exact mul_smul (g : G) (h : G) x.val

lemma ker_iff (s : Set X) (g : MulAction.stabilizer G s) :
    g ∈ (hom s).ker ↔ ∀ x ∈ s, (g : G) • x = x := by
  constructor
  · intro h x hx
    have hh : hom s g = 1 := h
    exact congrArg Subtype.val (Equiv.congr_fun hh ⟨x,hx⟩)
  · intro h
    show hom s g = 1
    ext x
    exact h x.val x.property

def kernelEquiv (s : Set X) : (hom (G := G) s).ker ≃* fixingSubgroup G s where
  toFun g := ⟨g.val.val, (mem_fixingSubgroup_iff G).mpr ((ker_iff s g.val).mp g.property)⟩
  invFun g := ⟨⟨g.val, MulAction.fixingSubgroup_le_stabilizer G s g.property⟩,
    (ker_iff s _).mpr ((mem_fixingSubgroup_iff G).mp g.property)⟩
  left_inv g := by rfl
  right_inv g := by rfl
  map_mul' _ _ := rfl

lemma quotient_finite (s : Set X) (hs : s.Finite) :
    Finite ((MulAction.stabilizer G s) ⧸ (hom (G := G) s).ker) := by
  let : Finite s := hs.to_subtype
  exact Finite.of_injective (QuotientGroup.quotientKerEquivRange (hom (G := G) s))
    (QuotientGroup.quotientKerEquivRange (hom (G := G) s)).injective
end SetwiseRestriction

namespace SimpleFInftyOvergroups

theorem setwise_stabilizer_of_ascending_torus
    {G X U P : Type} [Group G] [MulAction G X] [Group U] [Group P]
    [Group.IsFinitelyPresented P]
    (a : U →* P) (b : P →* U) (hf : Function.Injective (b.comp a))
    (F₂ : ListChains.IdempotentSplittings U (ZMod 2) (b.comp a))
    (F₃ : ListChains.IdempotentSplittings U (ZMod 3) (b.comp a))
    (s : Set X) (hs : s.Finite)
    (e : AscendingHNN.Torus (b.comp a) hf ≃* fixingSubgroup G s) :
    HasTypeFInfty (MulAction.stabilizer G s) := by
  let := SetwiseRestriction.quotient_finite (G := G) s hs
  exact finite_extension_of_ascending_torus a b hf F₂ F₃
    (SetwiseRestriction.hom (G := G) s).ker
    (e.trans (SetwiseRestriction.kernelEquiv s).symm)
end SimpleFInftyOvergroups

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma single_sub (i j : n) (a b : R) :
    Matrix.single i j (a-b)=Matrix.single i j a-Matrix.single i j b := by
  rw [sub_eq_add_neg,Matrix.single_add,← Matrix.single_neg,sub_eq_add_neg]

def root (i j : n) (h : i≠j) (a : R) : (Matrix n n R)ˣ where
  val := 1+Matrix.single i j a
  inv := 1+Matrix.single i j (-a)
  val_inv := by
    simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,
      ← Matrix.single_neg,add_assoc]
  inv_val := by
    simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,
      ← Matrix.single_neg,add_assoc]

@[simp] lemma root_val (i j : n) (h : i≠j) (a : R) :
    (root i j h a).val=1+Matrix.single i j a := rfl

@[simp] lemma root_zero (i j : n) (h : i≠j) : root i j h (0:R)=1 := by
  apply Units.ext; simp

lemma root_add (i j : n) (h : i≠j) (a b : R) :
    root i j h (a+b)=root i j h a*root i j h b := by
  apply Units.ext
  simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,
    Matrix.single_add,add_comm,add_left_comm,add_assoc]

@[simp] lemma root_inv (i j : n) (h : i≠j) (a : R) :
    (root i j h a)⁻¹=root i j h (-a) := by apply Units.ext; rfl

def elementary : Subgroup (Matrix n n R)ˣ :=
  Subgroup.closure {g | ∃ (i j : n) (h : i≠j) (a : R), g=root i j h a}

lemma root_mem (i j : n) (h : i≠j) (a : R) : root i j h a∈elementary :=
  Subgroup.subset_closure ⟨i,j,h,a,rfl⟩

def diagonal : (n → Rˣ) →* (Matrix n n R)ˣ where
  toFun d := {
    val := Matrix.diagonal (fun i => (d i).val)
    inv := Matrix.diagonal (fun i => (d i).inv)
    val_inv := by rw [Matrix.diagonal_mul_diagonal']; simp
    inv_val := by rw [Matrix.diagonal_mul_diagonal']; simp }
  map_one' := Units.ext (by simp)
  map_mul' d e := Units.ext (by simp)

@[simp] lemma diagonal_val (d : n → Rˣ) :
    (diagonal d).val=Matrix.diagonal (fun i => (d i).val) := rfl

def position (i : n) : Rˣ →* (Matrix n n R)ˣ where
  toFun u := diagonal (fun k => if k=i then u else 1)
  map_one' := by simp only [ite_self]; exact map_one diagonal
  map_mul' u v := by
    rw [← map_mul]; congr 1; funext k; by_cases h : k=i <;> simp [h]

lemma position_val (i : n) (u : Rˣ) :
    (position i u).val=1+Matrix.single i i (u.val-1) := by
  change Matrix.diagonal (fun k => ((if k=i then u else 1) : Rˣ).val)=_
  ext k l
  by_cases hki : k=i
  · subst k
    by_cases hli : l=i
    · subst l; simp [Matrix.single]
    · simp [Matrix.single,Ne.symm hli]
  · by_cases hkl : k=l
    · subst l; simp [Matrix.single,hki,Ne.symm hki]
    · simp [Matrix.single,Ne.symm hki,hkl]

lemma diagonal_single (d : n → R) (i j : n) (a : R) :
    Matrix.diagonal d*Matrix.single i j a=Matrix.single i j (d i*a) := by
  ext k l
  by_cases hki : i=k <;> by_cases hjl : j=l <;>
    simp [Matrix.diagonal_mul,Matrix.single,hki,hjl]

lemma single_diagonal (d : n → R) (i j : n) (a : R) :
    Matrix.single i j a*Matrix.diagonal d=Matrix.single i j (a*d j) := by
  ext k l
  by_cases hki : i=k <;> by_cases hjl : j=l <;>
    simp [Matrix.mul_diagonal,Matrix.single,hki,hjl]

lemma diagonal_conjugate_root (d : n → Rˣ) (i j : n) (h : i≠j) (a : R) :
    diagonal d*root i j h a*(diagonal d)⁻¹=
      root i j h ((d i).val*a*(d j).inv) := by
  apply Units.ext
  change Matrix.diagonal (fun k => (d k).val)*(1+Matrix.single i j a)*
    Matrix.diagonal (fun k => (d k).inv)=1+_
  rw [mul_add,mul_one,add_mul,Matrix.diagonal_mul_diagonal',diagonal_single,single_diagonal]
  simp

lemma diagonal_normalizes (d : n → Rˣ) : diagonal d∈Subgroup.normalizer (elementary (R:=R) (n:=n) : Set (Matrix n n R)ˣ) := by
  have hn : (diagonal (R:=R) (n:=n)).range≤Subgroup.normalizer (elementary (R:=R) (n:=n) : Set (Matrix n n R)ˣ) := by
    apply Subgroup.le_normalizer_closure_iff.mpr
    rintro x ⟨d,rfl⟩ g ⟨i,j,h,a,rfl⟩
    rw [diagonal_conjugate_root]
    exact root_mem _ _ _ _
  exact hn ⟨d,rfl⟩

def swapWord (i j : n) (h : i≠j) (u : Rˣ) : (Matrix n n R)ˣ :=
  root i j h u.val*root j i h.symm (-u.inv)*root i j h u.val

lemma swapWord_mem (i j : n) (h : i≠j) (u : Rˣ) : swapWord i j h u∈elementary :=
  (elementary (R:=R)).mul_mem ((elementary (R:=R)).mul_mem
    (root_mem _ _ _ _) (root_mem _ _ _ _)) (root_mem _ _ _ _)

lemma swapWord_val (i j : n) (h : i≠j) (u : Rˣ) :
    (swapWord i j h u).val=1-Matrix.single i i 1-Matrix.single j j 1+
      Matrix.single i j u.val-Matrix.single j i u.inv := by
  simp only [swapWord,Units.val_mul,root_val]
  simp [mul_add,add_mul,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,Matrix.single_mul_single_same,
    ← Matrix.single_neg]
  abel

lemma balanced (i j : n) (h : i≠j) (u : Rˣ) :
    swapWord i j h u*swapWord i j h (-1)=position i u*position j u⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul,swapWord_val,position_val]
  simp [mul_add,add_mul,sub_mul,mul_sub,Matrix.single_mul_single_of_ne _ _ _ _ h,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,Matrix.single_mul_single_same,
    ← Matrix.single_neg, single_sub]
  abel

lemma balanced_mem (i j : n) (h : i≠j) (u : Rˣ) :
    position i u*position j u⁻¹∈elementary := by
  rw [← balanced i j h u]
  exact (elementary (R:=R)).mul_mem (swapWord_mem _ _ _ _) (swapWord_mem _ _ _ _)

end NoncommElementary

open scoped commutatorElement
namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma root_commute (i j k l : n) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) (a b : R) :
    Commute (root i j hij a) (root k l hkl b) := by
  apply Units.ext
  change (1+Matrix.single i j a)*(1+Matrix.single k l b)=
    (1+Matrix.single k l b)*(1+Matrix.single i j a)
  simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hil.symm,add_comm,add_left_comm]

lemma root_commutator (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (a b : R) : ⁅root i j hij a,root j k hjk b⁆=root i k hik (a*b) := by
  apply Units.ext
  change ((1+Matrix.single i j a)*(1+Matrix.single j k b))*
    (1+Matrix.single i j (-a))*(1+Matrix.single j k (-b))=1+Matrix.single i k (a*b)
  simp only [add_mul,mul_add,one_mul,mul_one,Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm,
    mul_neg,neg_mul,add_zero]
  simp only [← Matrix.single_neg]
  abel
end NoncommElementary

end

end OAI
