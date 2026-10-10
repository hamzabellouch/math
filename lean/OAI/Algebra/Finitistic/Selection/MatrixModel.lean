import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.CharP.Algebra
import OAI.Algebra.Finitistic.Selection.FiniteQuotient
import OAI.Algebra.Finitistic.Selection.GroupSelection

namespace OAI
open scoped commutatorElement

namespace LittleFinitistic

def internalIndex (i : Fin 3) : Fin 5 := ⟨i.val+1,by omega⟩

@[simp] theorem internalIndex_ne_zero (i : Fin 3) : internalIndex i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+1=0 at hv
  omega
@[simp] theorem internalIndex_ne_four (i : Fin 3) : internalIndex i ≠ 4 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+1=4 at hv
  omega
@[simp] theorem internalIndex_inj (i j : Fin 3) : internalIndex i = internalIndex j ↔ i=j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change i.val+1=j.val+1 at hv
    omega
  · rintro rfl
    rfl

section MatrixRepresentation

variable {R : Type*} [CommRing R]


def matrixU (r : Rˣ) (i : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  transvectionUnit 0 (internalIndex i) (Ne.symm (internalIndex_ne_zero i)) (↑(r^a) : R)

def matrixV (r : Rˣ) (i : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  transvectionUnit (internalIndex i) 4 (internalIndex_ne_four i) (↑(r^a) : R)

def matrixW (r : Rˣ) (i j : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  if h : i=j then 1 else
    transvectionUnit (internalIndex i) (internalIndex j) (by simpa using h) (↑(r^a) : R)

def matrixT (r : Rˣ) (i : Fin 3) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  diagonalUnit (fun j => if j=internalIndex i then r else 1)

theorem matrixU_square [CharP R 2] (r : Rˣ) (i : Fin 3) (a : ℤ) : matrixU r i a * matrixU r i a = 1 := by
  apply Units.ext
  change transvection 0 (internalIndex i) (↑(r^a) : R) *
      transvection 0 (internalIndex i) (↑(r^a) : R) = 1
  rw [transvection_same 0 (internalIndex i) (Ne.symm (internalIndex_ne_zero i))]
  simp [CharTwo.add_self_eq_zero,transvection]

theorem matrix_UU_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) :
    Commute (matrixU r i a) (matrixU r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _
    (internalIndex_ne_zero i) (internalIndex_ne_zero j) _ _

theorem matrix_VV_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) :
    Commute (matrixV r i a) (matrixV r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _
    (Ne.symm (internalIndex_ne_four j)) (Ne.symm (internalIndex_ne_four i)) _ _

theorem matrix_UV_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    Commute (matrixU r i a) (matrixV r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _ (by simpa using hij) (by decide) _ _

theorem matrix_WU_commute (r : Rˣ) (i j h : Fin 3) (a b : ℤ) (hhi : h≠i) :
    Commute (matrixW r i j a) (matrixU r h b) := by
  unfold matrixW
  split_ifs with hij
  · exact Commute.one_left _
  · exact transvectionUnit_commute _ _ _ _ _ _
      (internalIndex_ne_zero j) (by simpa using hhi) _ _

theorem matrix_WV_commute (r : Rˣ) (i j h : Fin 3) (a b : ℤ) (hhj : h≠j) :
    Commute (matrixW r i j a) (matrixV r h b) := by
  unfold matrixW
  split_ifs with hij
  · exact Commute.one_left _
  · exact transvectionUnit_commute _ _ _ _ _ _
      (by simpa using hhj.symm) (Ne.symm (internalIndex_ne_four i)) _ _

theorem matrix_UW_commutator (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    ⁅matrixU r i a,matrixW r i j b⁆ = matrixU r j (a+b) := by
  unfold matrixW matrixU
  rw [dite_eq_right hij]
  simpa only [zpow_add,Units.val_mul] using
    transvectionUnit_commutator (R := R) 0 (internalIndex i) (internalIndex j)
      (Ne.symm (internalIndex_ne_zero i)) (by simpa using hij)
      (Ne.symm (internalIndex_ne_zero j)) (↑(r^a) : R) (↑(r^b) : R)

theorem matrix_WV_commutator (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    ⁅matrixW r i j a,matrixV r j b⁆ = matrixV r i (a+b) := by
  unfold matrixW matrixV
  rw [dite_eq_right hij]
  simpa only [zpow_add,Units.val_mul] using
    transvectionUnit_commutator (R := R) (internalIndex i) (internalIndex j) 4
      (by simpa using hij) (internalIndex_ne_four j)
      (internalIndex_ne_four i) (↑(r^a) : R) (↑(r^b) : R)

theorem matrix_TT_commute (r : Rˣ) (i j : Fin 3) : Commute (matrixT r i) (matrixT r j) :=
  diagonalUnit_commute _ _

theorem matrix_W_diagonal (r : Rˣ) (i : Fin 3) (a : ℤ) : matrixW r i i a = 1 := by
  simp [matrixW]

theorem matrix_TU_conjugation (r : Rˣ) (l i : Fin 3) (a : ℤ) :
    matrixT r l * matrixU r i a * (matrixT r l)⁻¹ =
      matrixU r i (a-if l=i then 1 else 0) := by
  unfold matrixT matrixU
  rw [transvectionUnit_conjugation]
  have h0 : (0 : Fin 5) ≠ internalIndex l := (internalIndex_ne_zero l).symm
  by_cases h : l=i
  · subst l
    simp [h0,zpow_sub]
  · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm h
    simp [h0,hi,h]

theorem matrix_TV_conjugation (r : Rˣ) (l i : Fin 3) (a : ℤ) :
    matrixT r l * matrixV r i a * (matrixT r l)⁻¹ =
      matrixV r i (a+if l=i then 1 else 0) := by
  unfold matrixT matrixV
  rw [transvectionUnit_conjugation]
  have h4 : (4 : Fin 5) ≠ internalIndex l := (internalIndex_ne_four l).symm
  by_cases h : l=i
  · subst l
    simp [h4,zpow_add,mul_comm]
  · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm h
    simp [h4,hi,h]

theorem matrix_TW_conjugation (r : Rˣ) (l i j : Fin 3) (a : ℤ) :
    matrixT r l * matrixW r i j a * (matrixT r l)⁻¹ =
      matrixW r i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0) := by
  by_cases hij : i=j
  · subst j
    simp [matrix_W_diagonal]
  · simp only [matrixW,dite_eq_right hij,matrixT]
    rw [transvectionUnit_conjugation]
    by_cases hli : l=i <;> by_cases hlj : l=j
    · exact False.elim (hij (hli.symm.trans hlj))
    · subst l
      have hji : internalIndex j ≠ internalIndex i := by simpa using Ne.symm hij
      simp [hji,hlj,zpow_add,mul_comm]
    · subst l
      have hij' : internalIndex i ≠ internalIndex j := by simpa using hij
      simp [hij',hli,zpow_sub]
    · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm hli
      have hj : internalIndex j ≠ internalIndex l := by simpa using Ne.symm hlj
      simp [hi,hj,hli,hlj]

def matrixData [CharP R 2] (r : Rˣ) : SelectionGroupData (Matrix (Fin 5) (Fin 5) R)ˣ where
  T := matrixT r
  U := matrixU r
  V := matrixV r
  W := matrixW r
  square_U := matrixU_square r
  commute_UU i j a b _ := matrix_UU_commute r i j a b
  commute_VV i j a b _ := matrix_VV_commute r i j a b
  commute_UV := matrix_UV_commute r
  commute_WU := matrix_WU_commute r
  commute_WV := matrix_WV_commute r
  commutator_UW := matrix_UW_commutator r
  commutator_WV := matrix_WV_commutator r
  commute_TT := matrix_TT_commute r
  conj_TU := matrix_TU_conjugation r
  conj_TV := matrix_TV_conjugation r
  conj_TW := matrix_TW_conjugation r
  diagonal_W := matrix_W_diagonal r

def matrixRepresentation [CharP R 2] (r : Rˣ) : Presentation.AuxiliaryGroup →*
    (Matrix (Fin 5) (Fin 5) R)ˣ := Presentation.ofData (matrixData r)

theorem matrixRepresentation_z [CharP R 2] (r : Rˣ) (N : ℤ) :
    matrixRepresentation r (Presentation.z N) = transvectionUnit 0 4 (by decide) (↑(r^N) : R) := by
  change Presentation.ofData (matrixData r)
    ⁅PresentedGroup.of (Presentation.Generator.U 0 0),PresentedGroup.of (Presentation.Generator.V 0 N)⁆ = _
  rw [map_commutatorElement,Presentation.ofData_of,Presentation.ofData_of]
  change ⁅matrixU r 0 0,matrixV r 0 N⁆ = _
  unfold matrixU matrixV
  rw [transvectionUnit_commutator 0 (internalIndex 0) 4 _ _ (by decide)]
  simp only [zpow_zero,Units.val_one,one_mul]


end MatrixRepresentation

instance cyclicRing_nontrivial (m : ℕ) [NeZero m] : Nontrivial (CyclicRing m) := by
  let i : Fin m := ⟨0,Nat.pos_of_ne_zero (NeZero.ne m)⟩
  exact ⟨⟨cyclicBasis m (NeZero.ne m) i,0,(cyclicBasis m (NeZero.ne m)).ne_zero i⟩⟩

instance cyclicRing_finiteInst (m : ℕ) [NeZero m] : Finite (CyclicRing m) :=
  cyclicRing_finite m (NeZero.ne m)

instance cyclicRing_charTwo (m : ℕ) [NeZero m] : CharP (CyclicRing m) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (CyclicRing m)).injective 2

noncomputable def cyclicUnit (m : ℕ) [NeZero m] : (CyclicRing m)ˣ :=
  (cyclic_root_isUnit m (Nat.pos_of_ne_zero (NeZero.ne m))).unit

@[simp] theorem cyclicUnit_val (m : ℕ) [NeZero m] :
    (cyclicUnit m : CyclicRing m) = AdjoinRoot.root (cyclicPolynomial m) :=
  IsUnit.unit_spec _

noncomputable def cyclicRepresentation (m : ℕ) [NeZero m] : Presentation.AuxiliaryGroup →*
    (Matrix (Fin 5) (Fin 5) (CyclicRing m))ˣ := matrixRepresentation (cyclicUnit m)

theorem cyclicRepresentation_z (m : ℕ) [NeZero m] (i : ℕ) :
    cyclicRepresentation m (Presentation.z i) = transvectionUnit 0 4 (by decide)
      (AdjoinRoot.root (cyclicPolynomial m)^i) := by
  unfold cyclicRepresentation
  rw [matrixRepresentation_z]
  simp only [zpow_natCast,Units.val_pow_eq_pow_val,cyclicUnit_val]

theorem centralEmbedding_basis (m : ℕ) [NeZero m] (i : Fin m) :
    centralEmbedding m (Multiplicative.ofAdd (Pi.single i 1)) =
      cyclicRepresentation m (Presentation.z i.val) := by
  rw [cyclicRepresentation_z]
  apply Units.ext
  change transvection (R := CyclicRing m) (0 : Fin 5) 4 (∑ j : Fin m, (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j •
      AdjoinRoot.root (cyclicPolynomial m) ^ (j : ℕ)) = _
  simp [Pi.single_apply, transvectionUnit]

noncomputable abbrev FiniteQuotientGroup (m : ℕ) [NeZero m] := (cyclicRepresentation m).range

instance finiteQuotientGroup_finite (m : ℕ) [NeZero m] : Finite (FiniteQuotientGroup m) :=
  inferInstance

noncomputable def finiteQuotientMap (m : ℕ) [NeZero m] :
    Presentation.AuxiliaryGroup →* FiniteQuotientGroup m := (cyclicRepresentation m).rangeRestrict

theorem finiteQuotientMap_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (finiteQuotientMap m) := (cyclicRepresentation m).rangeRestrict_surjective

theorem centralEmbedding_mem_center_map (m : ℕ) [NeZero m]
    (c : Fin m → ZMod 2) : centralEmbedding m (Multiplicative.ofAdd c) ∈
      (Subgroup.center Presentation.AuxiliaryGroup).map (cyclicRepresentation m) := by
  classical
  let S := (Subgroup.center Presentation.AuxiliaryGroup).map (cyclicRepresentation m)
  apply Pi.single_induction (fun c => centralEmbedding m (Multiplicative.ofAdd c) ∈ S) c
  · simp
  · intro f g hf hg
    change centralEmbedding m (Multiplicative.ofAdd f * Multiplicative.ofAdd g) ∈ S
    rw [map_mul]
    exact S.mul_mem hf hg
  · intro i a
    fin_cases a
    · change centralEmbedding m (Multiplicative.ofAdd (Pi.single i (0 : ZMod 2))) ∈ S
      simpa only [Pi.single_zero,ofAdd_zero,map_one] using S.one_mem
    · change centralEmbedding m (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) ∈ S
      rw [centralEmbedding_basis]
      apply Subgroup.mem_map_of_mem
      exact Subgroup.mem_center_iff.mpr (fun g => (Presentation.z_central i.val g).eq.symm)

theorem centralEmbedding_mem_range (m : ℕ) [NeZero m]
    (c : Multiplicative (Fin m → ZMod 2)) :
    centralEmbedding m c ∈ (cyclicRepresentation m).range := by
  obtain ⟨g, _, hg⟩ := centralEmbedding_mem_center_map m c.toAdd
  exact ⟨g,hg⟩

noncomputable def quotientCentralEmbedding (m : ℕ) [NeZero m] :
    Multiplicative (Fin m → ZMod 2) →* FiniteQuotientGroup m where
  toFun c := ⟨centralEmbedding m c, centralEmbedding_mem_range m c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem quotientCentralEmbedding_injective (m : ℕ) [NeZero m] :
    Function.Injective (quotientCentralEmbedding m) := by
  intro a b h
  exact centralEmbedding_injective m (NeZero.ne m) (congrArg Subtype.val h)

theorem quotientCentralEmbedding_basis (m : ℕ) [NeZero m] (i : Fin m) :
    quotientCentralEmbedding m (Multiplicative.ofAdd (Pi.single i 1)) =
      finiteQuotientMap m (Presentation.z i.val) :=
  Subtype.ext (centralEmbedding_basis m i)

theorem quotientCentralEmbedding_central (m : ℕ) [NeZero m]
    (c : Multiplicative (Fin m → ZMod 2)) (g : FiniteQuotientGroup m) :
    Commute (quotientCentralEmbedding m c) g := by
  obtain ⟨x, hx, hxval⟩ := centralEmbedding_mem_center_map m c.toAdd
  obtain ⟨y, hy⟩ := finiteQuotientMap_surjective m g
  subst g
  apply Subtype.ext
  change centralEmbedding m c * cyclicRepresentation m y =
    cyclicRepresentation m y * centralEmbedding m c
  change cyclicRepresentation m x = centralEmbedding m c at hxval
  rw [← hxval, ← map_mul, ← map_mul]
  exact congrArg (cyclicRepresentation m) (Subgroup.mem_center_iff.mp hx y).symm

/-- The actual finite quotient in the manuscript, including the embedded elementary
abelian central subgroup and the prescribed images of all its basis elements. -/
theorem finite_central_quotient (m : ℕ) [NeZero m] :
    Function.Surjective (finiteQuotientMap m) ∧
    Function.Injective (quotientCentralEmbedding m) ∧
    (∀ c g, Commute (quotientCentralEmbedding m c) g) ∧
    (∀ i : Fin m, quotientCentralEmbedding m (Multiplicative.ofAdd (Pi.single i 1)) =
      finiteQuotientMap m (Presentation.z i.val)) :=
  ⟨finiteQuotientMap_surjective m,quotientCentralEmbedding_injective m,
    quotientCentralEmbedding_central m,quotientCentralEmbedding_basis m⟩

end LittleFinitistic

end OAI
