import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ForwardChartMutation

namespace OAI

section
namespace ElementaryPositivity.LatticeRealization
open scoped BigOperators
open TriangularDynamics
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cast : (V → ℤ) →+ (V → ℝ) where
  toFun x i := x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [Fintype V] [DecidableEq V] in
@[simp] lemma cast_apply (x : V → ℤ) (i : V) : cast x i=(x i:ℝ) := rfl
omit [Fintype V] [DecidableEq V] in
lemma cast_injective : Function.Injective (cast (V:=V)) := by
  intro a b h
  ext i
  have H := congrFun h i
  change (a i : ℝ)=(b i : ℝ) at H
  exact_mod_cast H

variable (A : Matrix V V ℤ)
noncomputable def realPairing : (V → ℝ) →ₗ[ℝ] (V → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toBilin' (fun i j => (A i j:ℝ))

lemma realPairing_apply (x y : V → ℝ) :
    realPairing A x y=∑i,∑j,x i*(A i j:ℝ)*y j := Matrix.toBilin'_apply _ _ _

lemma realPairing_cast (x y : V → ℤ) :
    realPairing A (cast x) (cast y)=(matrixPairing A x y:ℝ) := by
  simp only [realPairing_apply,matrixPairing_apply,cast_apply,Int.cast_sum,Int.cast_mul]

lemma realPairing_skew (hA : ∀i j,A i j= -A j i) (x y : V → ℝ) :
    realPairing A x y= -realPairing A y x := by
  rw [realPairing_apply,realPairing_apply,Finset.sum_comm]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i,Int.cast_neg]
  ring

lemma realPairing_self (hA : ∀i j,A i j= -A j i) (x : V → ℝ) :
    realPairing A x x=0 := by
  have H:=realPairing_skew A hA x x
  linarith

noncomputable def realDot : (V → ℝ) →ₗ[ℝ] (V → ℝ) →ₗ[ℝ] ℝ := Matrix.toBilin' (1 : Matrix V V ℝ)

lemma realDot_apply (x y : V → ℝ) : realDot x y=∑i,x i*y i := by
  simp [realDot,Matrix.toBilin'_apply,Matrix.one_apply]
lemma realDot_comm (x y : V → ℝ) : realDot x y=realDot y x := by
  simp only [realDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma realDot_cast (x y : V → ℤ) :
    realDot (cast x) (cast y)=(LatticeExtension.dot x y:ℝ) := by
  simp only [realDot_apply,LatticeExtension.dot_apply,cast_apply,Int.cast_sum,Int.cast_mul]

noncomputable def extendedCast : LatticeExtension.Extended V →+ ((V → ℝ) × (V → ℝ)) :=
  (cast.comp (AddMonoidHom.fst _ _)).prod (cast.comp (AddMonoidHom.snd _ _))
omit [Fintype V] [DecidableEq V] in
lemma extendedCast_apply (x : LatticeExtension.Extended V) :
    extendedCast x=(cast x.1,cast x.2) := rfl
omit [Fintype V] [DecidableEq V] in
lemma extendedCast_injective : Function.Injective (extendedCast (V:=V)) := by
  intro a b h
  apply Prod.ext
  · exact cast_injective (congrArg Prod.fst h)
  · exact cast_injective (congrArg Prod.snd h)

noncomputable def extendedRealForm : ((V → ℝ) × (V → ℝ)) →ₗ[ℝ]
    ((V → ℝ) × (V → ℝ)) →ₗ[ℝ] ℝ :=
  ((realPairing A).compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _)) +
    (realDot.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.fst ℝ _ _)) -
    (realDot.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.snd ℝ _ _))

lemma extendedRealForm_apply (x y : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x y=realPairing A x.1 y.1+realDot x.2 y.1-realDot x.1 y.2 := rfl

lemma extendedRealForm_self (hA : ∀i j,A i j= -A j i) (x : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x x=0 := by
  rw [extendedRealForm_apply,realPairing_self A hA,zero_add,realDot_comm x.2 x.1,sub_self]

lemma extendedRealForm_cast (x y : LatticeExtension.Extended V) :
    extendedRealForm A (extendedCast x) (extendedCast y)=
      (LatticeExtension.form (matrixPairing A) x y:ℝ) := by
  simp only [extendedRealForm_apply,extendedCast_apply,realPairing_cast,realDot_cast,
    LatticeExtension.form_apply,Int.cast_sub,Int.cast_add]

end ElementaryPositivity.LatticeRealization

end
section
namespace ElementaryPositivity.ForwardChain
variable {M M':Type*} [AddCommGroup M] [AddCommGroup M']
lemma gaps_map (a:M →+ M') (x y:M) (bs:List M) :
    gaps (a x) (bs.map a) (a y)=(gaps x bs y).map a := by
  induction bs generalizing x with
  | nil => simp [gaps,map_sub]
  | cons b bs ih => simp only [gaps,List.map_cons,map_sub,ih]
end ElementaryPositivity.ForwardChain

namespace ElementaryPositivity.TriangularDynamics
variable {n:ℕ} {M M':Type*} [AddCommGroup M] [AddCommGroup M']
lemma forwardInventory_map (a:M →+ M') (d:Fin (n+1) → M) (w:Cell n → M) (q:List (Cell n)) :
    forwardInventory (a ∘ d) (a ∘ w) q=(forwardInventory d w q).map a := by
  unfold forwardInventory
  rw [List.map_flatMap]
  congr 1
  funext i
  simp only [levelGaps,Function.comp_apply,←List.map_map,ForwardChain.gaps_map]
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma cast_single {V:Type*} [Fintype V] [DecidableEq V] (i:V) (z:ℤ) :
    LatticeRealization.cast (Pi.single i z)=Pi.single i (z:ℝ) := by
  ext j
  simp only [LatticeRealization.cast_apply,Pi.single_apply]
  split_ifs <;> simp
lemma cast_forwardGap (g:GapIndex n) :
    LatticeRealization.cast (forwardGap (R:=ℤ) g)=forwardGap (R:=ℝ) g := by
  simp only [forwardGap,map_sub,cast_single,Int.cast_one]

def extendedRoots (n:ℕ) : (GapIndex n → ℤ) →+ Extended (Vertex n (Cell n)) :=
  includeVertices.comp (forwardRoots (R:=ℤ)).toAddMonoidHom

def extendedCoord (n:ℕ) : Extended (Vertex n (Cell n)) →+ (GapIndex n → ℤ) :=
  (forwardCoord (R:=ℤ)).toAddMonoidHom.comp (AddMonoidHom.fst _ _)

lemma extendedCoord_roots (c:GapIndex n → ℤ) : extendedCoord n (extendedRoots n c)=c := by
  exact forwardCoord_roots c
lemma extendedRoot_eq (g:GapIndex n) : simpleRoot (extendedRoots n) g=includeVertices (forwardGap g) := by
  change includeVertices (simpleRoot (forwardRoots (R:=ℤ)).toAddMonoidHom g)=_
  rw [simpleRoot_forwardRoots]
lemma extendedRoots_realIndependent :
    LinearIndependent ℝ (fun i:GapIndex n=>extendedCast (simpleRoot (extendedRoots n) i)) := by
  let incl : (Vertex n (Cell n) → ℝ) →ₗ[ℝ]
      ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ)) := LinearMap.inl ℝ _ _
  have hincl : Function.Injective incl := by
    intro x y h
    exact congrArg Prod.fst h
  have hk : LinearMap.ker incl = ⊥ := LinearMap.ker_eq_bot.mpr hincl
  have Hi : LinearIndependent ℝ (incl ∘ (forwardGap (R:=ℝ) (n:=n))) :=
    (forwardGap_independent (R:=ℝ) (n:=n)).map' incl hk
  convert Hi using 1
  funext i
  rw [extendedRoot_eq]
  change (LatticeRealization.cast (forwardGap (R:=ℤ) i),LatticeRealization.cast 0)=(forwardGap i,0)
  rw [cast_forwardGap,map_zero]

def initialFreeChart (n:ℕ) : FreeChart (I:=GapIndex n) (extendedCast (V:=Vertex n (Cell n))) where
  roots := extendedRoots n
  coord := extendedCoord n
  retract := extendedCoord_roots
  independent := extendedRoots_realIndependent

lemma initialFreeChart_inventory :
    ((gapIndices n).map (simpleRoot (initialFreeChart n).roots)).Perm
      (forwardInventory (includeVertices ∘ anchor) (includeVertices ∘ bridge) (phaseCycle n)) := by
  apply List.Perm.of_eq
  rw [forwardInventory_map,initial_forwardInventory,List.map_map]
  apply List.map_congr_left
  intro g _
  exact extendedRoot_eq g

def extendedOmega (n:ℕ) := LatticeExtension.form (triangularOmega n)
lemma extendedOmega_self : ∀m,extendedOmega n m m=0 := form_self _ triangularOmega_self
lemma extendedOmega_nondegenerate : ∀r≠0,∃m,extendedOmega n r m≠0 := form_nondegenerate _
lemma extendedOmega_original (m m':Lattice n (Cell n)) :
    extendedOmega n (includeVertices m) (includeVertices m')=triangularOmega n m m' := form_original _ _ _
def triangularRealForm (n:ℕ) := extendedRealForm (chartMatrix (@cellLevel n) (@triangularBB n))
lemma triangularRealForm_self : ∀m, triangularRealForm n m m=0 :=
  extendedRealForm_self _ (chartMatrix_skew cellLevel triangularBB triangularBB_skew)
lemma triangularRealForm_compatible (m m':Extended (Vertex n (Cell n))) :
    triangularRealForm n (extendedCast m) (extendedCast m')=(extendedOmega n m m':ℝ) :=
  extendedRealForm_cast _ _ _
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
