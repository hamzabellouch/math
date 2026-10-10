import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma exists_finiteType_matrix_ring [Group.FG G] (ρ : G →* GL n R) :
    ∃ D : Subalgebra ℤ R, Algebra.FiniteType ℤ D ∧ ∀ g i j, ρ g i j∈D := by
  obtain ⟨S,hS,hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let T := hSf.toFinset ∪ hSf.toFinset⁻¹
  let E := T.biUnion (fun g => Finset.univ.biUnion (fun i => Finset.univ.image (fun j => ρ g i j)))
  let D := Algebra.adjoin ℤ (E : Set R)
  have hD : Algebra.FiniteType ℤ D := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset E)
  have hgen (g : G) (hg : g∈T) (i j : n) : ρ g i j∈D := by
    apply Algebra.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩
  refine ⟨D,hD,?_⟩
  intro g
  have hg : g∈Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction'' with
  | mem a ha => exact hgen a (Finset.mem_union_left _ (hSf.mem_toFinset.mpr ha))
  | inv_mem a ha =>
    apply hgen a⁻¹
    apply Finset.mem_union_right
    simpa using hSf.mem_toFinset.mpr ha
  | one =>
    intro i j
    rw [map_one]
    by_cases h : i=j <;> simp [h,D.zero_mem,D.one_mem]
  | mul a b ha hb iha ihb =>
    intro i j
    rw [map_mul]
    change (∑ l, ρ a i l*ρ b l j)∈D
    exact D.sum_mem (fun l _ => D.mul_mem (iha i l) (ihb l j))

variable (ρ : G →* GL n R) (D : Subalgebra ℤ R) (hD : ∀ g i j, ρ g i j∈D)

def liftMatrix (g : G) : Matrix n n D := fun i j => ⟨ρ g i j,hD g i j⟩

@[simp] lemma liftMatrix_map (g : G) :
    (D.val.toRingHom.mapMatrix) (liftMatrix ρ D hD g)=(ρ g).val := rfl

lemma liftMatrix_one : liftMatrix ρ D hD 1=1 := by
  apply Matrix.map_injective (f := D.val) Subtype.val_injective
  change D.val.toRingHom.mapMatrix (liftMatrix ρ D hD 1)=D.val.toRingHom.mapMatrix 1
  rw [map_one]
  change (ρ 1).val=1
  rw [map_one]
  rfl

lemma liftMatrix_mul (g h : G) : liftMatrix ρ D hD (g*h)=liftMatrix ρ D hD g*liftMatrix ρ D hD h := by
  apply Matrix.map_injective (f := D.val) Subtype.val_injective
  change D.val.toRingHom.mapMatrix (liftMatrix ρ D hD (g*h))=D.val.toRingHom.mapMatrix _
  rw [map_mul]
  change (ρ (g*h)).val=(ρ g).val*(ρ h).val
  rw [map_mul]
  rfl

def liftMatrixGroup : G →* GL n D where
  toFun g := ⟨liftMatrix ρ D hD g,liftMatrix ρ D hD g⁻¹,
    by rw [←liftMatrix_mul,mul_inv_cancel,liftMatrix_one],
    by rw [←liftMatrix_mul,inv_mul_cancel,liftMatrix_one]⟩
  map_one' := Units.ext (liftMatrix_one ρ D hD)
  map_mul' g h := Units.ext (liftMatrix_mul ρ D hD g h)

@[simp] lemma liftMatrixGroup_map (g : G) :
    Matrix.GeneralLinearGroup.map D.val.toRingHom (liftMatrixGroup ρ D hD g)=ρ g := by
  apply Units.ext
  rfl

lemma liftMatrixGroup_injective (hρ : Injective ρ) : Injective (liftMatrixGroup ρ D hD) := by
  intro x y he
  apply hρ
  apply Units.ext
  ext i j
  exact congrArg (fun M : GL n D => ((M i j : D) : R)) he

end CriticalPercolation.LinearGrowth
end
end

end OAI
