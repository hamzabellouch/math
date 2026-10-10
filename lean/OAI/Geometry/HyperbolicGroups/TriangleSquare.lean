import Mathlib

namespace OAI

section


/-! A literal closed triangle is the compact quotient of a square collapsing
only its upper edge. Continuous face homotopies therefore descend with their
three prescribed edge tracks. -/
noncomputable section
open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.TriangleSquare
abbrev Triangle := { coords : Fin 3 → ℝ | (∀ index, 0 ≤ coords index) ∧ ∑ index, coords index = 1 }

lemma sum_coords (z : Triangle) : z.val 0 + z.val 1 + z.val 2 = 1 := by
  simpa [Fin.sum_univ_succ,add_assoc] using z.property.2
lemma coord_le_one (z : Triangle) (i : Fin 3) : z.val i ≤ 1 := by
  have h := sum_coords z
  have h0 := z.property.1 0
  have h1 := z.property.1 1
  have h2 := z.property.1 2
  fin_cases i <;> dsimp <;> linarith

instance : CompactSpace Triangle := by
  refine isCompact_iff_compactSpace.mp
    (IsCompact.of_isClosed_subset
      (isCompact_Icc : IsCompact (Set.Icc (0 : Fin 3 → ℝ) 1)) ?_ ?_)
  · change IsClosed ({ coords : Fin 3 → ℝ | ∀ index, 0 ≤ coords index } ∩
      { coords | ∑ index, coords index = 1 })
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter (fun index => isClosed_le continuous_const (continuous_apply index))
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro coords property
    exact ⟨property.1, fun index => coord_le_one ⟨coords, property⟩ index⟩

def quotient : C(I × I,Triangle) where
  toFun z := ⟨![(1-(z.2:ℝ))*(1-(z.1:ℝ)),(1-(z.2:ℝ))*(z.1:ℝ),(z.2:ℝ)],by
    constructor
    · intro i; fin_cases i <;> dsimp
      · exact mul_nonneg (sub_nonneg.mpr z.2.property.2) (sub_nonneg.mpr z.1.property.2)
      · exact mul_nonneg (sub_nonneg.mpr z.2.property.2) z.1.property.1
      · exact z.2.property.1
    · simp [Fin.sum_univ_succ]; ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] lemma quotient_zero (x : I) : (quotient (x,0)).val = ![1-(x:ℝ),(x:ℝ),0] := by
  ext i; fin_cases i <;> simp [quotient]
@[simp] lemma quotient_left (y : I) : (quotient (0,y)).val = ![1-(y:ℝ),0,(y:ℝ)] := by
  ext i; fin_cases i <;> simp [quotient]
@[simp] lemma quotient_right (y : I) : (quotient (1,y)).val = ![0,1-(y:ℝ),(y:ℝ)] := by
  ext i; fin_cases i <;> simp [quotient]
@[simp] lemma quotient_one (x : I) : quotient (x,1) = quotient (0,1) := by
  apply Subtype.ext; ext i; fin_cases i <;> simp [quotient]

lemma quotient_surjective : Function.Surjective quotient := by
  intro z
  let y : I := ⟨z.val 2,z.property.1 2,coord_le_one z 2⟩
  have hs := sum_coords z
  by_cases hy : z.val 2 = 1
  · have hz0 : z.val 0 = 0 := by linarith [z.property.1 0,z.property.1 1]
    have hz1 : z.val 1 = 0 := by linarith [z.property.1 0,z.property.1 1]
    refine ⟨(0,1),?_⟩
    apply Subtype.ext; ext i; fin_cases i <;> simp [quotient,hz0,hz1,hy]
  · have hp : 0 < 1-z.val 2 := sub_pos.mpr (lt_of_le_of_ne (coord_le_one z 2) hy)
    let x : I := ⟨z.val 1/(1-z.val 2),div_nonneg (z.property.1 1) hp.le,
      (div_le_one hp).mpr (by linarith [z.property.1 0])⟩
    have hx : (1-z.val 2)*(x:ℝ) = z.val 1 := by
      dsimp [x]; field_simp
    refine ⟨(x,y),?_⟩
    apply Subtype.ext
    ext i; fin_cases i <;> dsimp [quotient,y]
    · nlinarith
    · exact hx

lemma quotient_fiber {z z' : I × I} (h : quotient z = quotient z') :
    z.2 = z'.2 ∧ (z.1 = z'.1 ∨ z.2 = 1) := by
  have hy : z.2 = z'.2 := Subtype.ext (congrArg (fun p : Triangle => p.val 2) h)
  refine ⟨hy,?_⟩
  by_cases h1 : z.2 = 1
  · exact Or.inr h1
  left
  have hh := congrArg (fun p : Triangle => p.val 1) h
  change (1-(z.2:ℝ))*(z.1:ℝ) = (1-(z'.2:ℝ))*(z'.1:ℝ) at hh
  rw [←hy] at hh
  apply Subtype.ext
  exact (mul_left_cancel₀ (by intro he; exact h1 (Subtype.ext (by change (z.2:ℝ) = 1; linarith)))) hh

lemma quotient_isQuotientMap : IsQuotientMap quotient :=
  quotient.continuous.isClosedMap.isQuotientMap quotient.continuous quotient_surjective

variable {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
def paramQuotient : C(T × (I × I),T × Triangle) := (ContinuousMap.id T).prodMap quotient
lemma paramQuotient_surjective : Function.Surjective (paramQuotient (T := T)) := by
  rintro ⟨t,z⟩
  obtain ⟨w,rfl⟩ := quotient_surjective z
  exact ⟨(t,w),rfl⟩
lemma paramQuotient_isQuotientMap [CompactSpace T] [T2Space T] :
    IsQuotientMap (paramQuotient (T := T)) :=
  paramQuotient.continuous.isClosedMap.isQuotientMap paramQuotient.continuous paramQuotient_surjective

variable (F : C(T × (I × I),X)) (ht : ∀ t x, F (t,(x,1)) = F (t,(0,1)))
include ht in
lemma fiber_constant (t : T) {z z' : I × I} (h : quotient z = quotient z') : F (t,z) = F (t,z') := by
  obtain ⟨hy,hx|h1⟩ := quotient_fiber h
  · exact congrArg F (Prod.ext rfl (Prod.ext hx hy))
  · have h1' : z'.2 = 1 := hy.symm.trans h1
    calc F (t,z) = F (t,(z.1,1)) := by rw [←h1]
         _ = F (t,(0,1)) := ht _ _
         _ = F (t,(z'.1,1)) := (ht _ _).symm
         _ = F (t,z') := by rw [←h1']

variable [CompactSpace T] [T2Space T]

def descend : C(T × Triangle,X) where
  toFun tz := F (tz.1,(quotient_surjective tz.2).choose)
  continuous_toFun := by
    apply paramQuotient_isQuotientMap.continuous_iff.mpr
    convert F.continuous using 1
    funext tz
    exact fiber_constant F ht tz.1 (quotient_surjective (quotient tz.2)).choose_spec

@[simp] lemma descend_quotient (t : T) (z : I × I) : descend F ht (t,quotient z) = F (t,z) :=
  fiber_constant F ht t (quotient_surjective (quotient z)).choose_spec

end HyperbolicObstruction.TriangleSquare
end
end

section

end

end OAI
