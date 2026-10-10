import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootHolonomy

namespace OAI

/-! # Coordinates with the processed roots before the remaining subgroup

These coordinates keep the remaining subgroup on the right, so its
fibers are actual right orbits at every step of the product induction.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

structure RootPrefixCoordinates (n : ℕ) (P : Finset (Fin n × Fin n))
    (T : Type*) [TopologicalSpace T] where
  base : T → G n
  equiv : (T × positiveRootGeneratedGroup (allPositiveRoots n \ P)) ≃ₜ
    positiveRootGeneratedGroup (allPositiveRoots n)
  param_eq_mul : ∀ t w, (equiv (t,w)).val = base t * w.val

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {T : Type*} [TopologicalSpace T]

def empty (n : ℕ) : RootPrefixCoordinates n ∅ PUnit where
  base _ := 1
  equiv := {
    toFun z := ⟨z.2.val, by simpa only [Finset.sdiff_empty] using z.2.prop⟩
    invFun w := (PUnit.unit, ⟨w.val, by simpa only [Finset.sdiff_empty] using w.prop⟩)
    left_inv z := Prod.ext (Subsingleton.elim _ _) (Subtype.ext rfl)
    right_inv w := Subtype.ext rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_snd).subtype_mk _
    continuous_invFun := continuous_const.prodMk (continuous_subtype_val.subtype_mk _) }
  param_eq_mul _ _ := (one_mul _).symm

def extend (C : RootPrefixCoordinates n P T) (hP : InitialRootPattern P)
    (p : Fin n × Fin n) (hp : p ∈ allPositiveRoots n \ P)
    (hmin : ∀ q ∈ allPositiveRoots n \ P, toLex p ≤ toLex q) :
    RootPrefixCoordinates n (insert p P) (T × ℝ) := by
  let S := allPositiveRoots n \ P
  have hpos : ∀ q ∈ S, q.1 < q.2 :=
    fun _ hq => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
  have hab : p.1 ≠ p.2 := ne_of_lt (hpos p hp)
  have hclosed := initialRemaining_roots_closed P hP
  have herase : ∀ a b c : Fin n, (a,b) ∈ S.erase p →
      (b,c) ∈ S.erase p → (a,c) ∈ S.erase p := by
    rw [initialRemaining_erase]
    exact initialRemaining_roots_closed (insert p P) (initialRootPattern_insert_min hP p hp hmin)
  let e : positiveRootGeneratedGroup (allPositiveRoots n \ insert p P) ≃ₜ
      positiveRootGeneratedGroup (S.erase p) :=
    Homeomorph.setCongr (by rw [show S.erase p = allPositiveRoots n \ insert p P from
      initialRemaining_erase P p])
  let F := positiveRootFactorHomeomorph S hpos hclosed hab hp herase
  let H := ((Homeomorph.refl ℝ).prodCongr e).trans F
  refine {
    base := fun z => C.base z.1 * Matrix.SpecialLinearGroup.transvection hab z.2
    equiv := (Homeomorph.prodAssoc T ℝ _).trans
      (((Homeomorph.refl T).prodCongr H).trans C.equiv)
    param_eq_mul := ?_ }
  intro z w
  change (C.equiv (z.1, F (z.2, e w))).val = _
  rw [C.param_eq_mul]
  change C.base z.1 * (Matrix.SpecialLinearGroup.transvection hab z.2 * w.val) = _
  exact (mul_assoc _ _ _).symm

def groupParam (C : RootPrefixCoordinates n P T)
    (z : UpperRootTransverse n × (T × positiveRootGeneratedGroup (allPositiveRoots n \ P))) : G n :=
  upperRootParam n (z.1, (upperRootWordHomeomorph n).symm (C.equiv z.2))

lemma groupParam_eq_mul (C : RootPrefixCoordinates n P T)
    (z : UpperRootTransverse n × (T × positiveRootGeneratedGroup (allPositiveRoots n \ P))) :
    C.groupParam z = z.1.val * (C.base z.2.1 * z.2.2.val) := by
  rw [groupParam, upperRootParam_eq_mul]
  have H := congrArg Subtype.val ((upperRootWordHomeomorph n).apply_symm_apply (C.equiv z.2))
  rw [← C.param_eq_mul]
  exact congrArg (z.1.val * ·) H

theorem groupParam_isOpenEmbedding (C : RootPrefixCoordinates n P T) :
    Topology.IsOpenEmbedding C.groupParam := by
  let E := (Homeomorph.refl (UpperRootTransverse n)).prodCongr
    (C.equiv.trans (upperRootWordHomeomorph n).symm)
  exact (upperRootParam_isOpenEmbedding n).comp E.isOpenEmbedding

def quotientParam (C : RootPrefixCoordinates n P T) (g : G n)
    (z : UpperRootTransverse n × (T × positiveRootGeneratedGroup (allPositiveRoots n \ P))) : X n :=
  Quotient.mk _ (g * C.groupParam z)

lemma quotientParam_eq_action (C : RootPrefixCoordinates n P T) (g : G n)
    (s : UpperRootTransverse n) (t : T)
    (w : positiveRootGeneratedGroup (allPositiveRoots n \ P)) :
    C.quotientParam g (s,(t,w)) =
      rightAction (Quotient.mk _ ((g * s.val) * C.base t)) w.val := by
  change Quotient.mk _ (g * C.groupParam (s,(t,w))) = _
  rw [C.groupParam_eq_mul]
  change Quotient.mk _ (g * (s.val * (C.base t * w.val))) =
    Quotient.mk _ (((g * s.val) * C.base t) * w.val)
  simp only [mul_assoc]

theorem quotientParam_localHomeomorph (C : RootPrefixCoordinates n P T) (g : G n) :
    IsLocalHomeomorph (C.quotientParam g) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp C.groupParam_isOpenEmbedding.isLocalHomeomorph)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
