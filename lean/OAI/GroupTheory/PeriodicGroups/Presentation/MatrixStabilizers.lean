import Mathlib
import OAI.GroupTheory.PeriodicGroups.Presentation.FinitePresentation

namespace OAI

section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rectangleLower : (κ × ι → Multiplicative R) →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun A :=
    { val := Matrix.fromBlocks 1 0 (Matrix.of (fun i j => (A (i,j)).toAdd)) 1
      inv := Matrix.fromBlocks 1 0 (Matrix.of (fun i j => -(A (i,j)).toAdd)) 1
      val_inv := by
        rw [Matrix.fromBlocks_multiply]
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
      inv_val := by
        rw [Matrix.fromBlocks_multiply]
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply] }
  map_one' := by
    apply Units.ext
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.one_mul,
      Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
    congr 1

@[simp] lemma rectangleLower_single (i : κ) (j : ι) (a : R) :
    rectangleLower (Pi.mulSingle (i,j) (Multiplicative.ofAdd a)) =
      elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [rectangleLower,Pi.mulSingle,Function.update,Matrix.add_apply,
      Matrix.one_apply,Matrix.single_apply,Matrix.fromBlocks,eq_comm,and_comm]
  split_ifs <;> rfl

lemma rectangleLower_mem {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (hP : ∀i j a, elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a ∈ P)
    (A : κ × ι → Multiplicative R) : rectangleLower A ∈ P := by
  change A ∈ P.comap rectangleLower
  apply Subgroup.pi_mem_of_mulSingle_mem
  rintro ⟨i,j⟩
  change rectangleLower (Pi.mulSingle (i,j) (A (i,j))) ∈ P
  change rectangleLower (Pi.mulSingle (i,j) (Multiplicative.ofAdd ((A (i,j)).toAdd))) ∈ P
  rw [rectangleLower_single]
  exact hP _ _ _

def rightFixer : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  ⨅ k : κ, MulAction.stabilizer (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ (Pi.single (Sum.inr k) (1 : R) : ι ⊕ κ → R)

lemma mem_rightFixer_iff (U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
    U ∈ rightFixer ↔ ∀ i k, U.val i (Sum.inr k) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) i (Sum.inr k) := by
  simp only [rightFixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
  constructor
  · intro h i k
    have hh := congrFun (h k) i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh
  · intro h k
    ext i
    have hh := h i k
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh

lemma rightFixer_shape (U : rightFixer (ι := ι) (κ := κ) (R := R)) :
    U.val.val = Matrix.fromBlocks (U.val.val.submatrix Sum.inl Sum.inl) 0
      (U.val.val.submatrix Sum.inr Sum.inl) 1 := by
  ext i j
  cases j with
  | inl j => cases i <;> rfl
  | inr j =>
    have hh := (mem_rightFixer_iff U.val).mp U.property i j
    cases i <;> simpa [Matrix.fromBlocks,Matrix.one_apply] using hh

def rightProjection : rightFixer (ι := ι) (κ := κ) (R := R) →* (Matrix ι ι R)ˣ where
  toFun U :=
    { val := U.val.val.submatrix Sum.inl Sum.inl
      inv := U.val.inv.submatrix Sum.inl Sum.inl
      val_inv := by
        have he : U.val.val * (U⁻¹).val.val = 1 := U.val.val_inv
        rw [rightFixer_shape U,rightFixer_shape U⁻¹,Matrix.fromBlocks_multiply] at he
        ext i j
        have hh := congrArg (fun A : Matrix (ι ⊕ κ) (ι ⊕ κ) R => A (Sum.inl i) (Sum.inl j)) he
        simpa [Matrix.fromBlocks,Matrix.one_apply] using hh
      inv_val := by
        have he : (U⁻¹).val.val * U.val.val = 1 := U.val.inv_val
        rw [rightFixer_shape U⁻¹,rightFixer_shape U,Matrix.fromBlocks_multiply] at he
        ext i j
        have hh := congrArg (fun A : Matrix (ι ⊕ κ) (ι ⊕ κ) R => A (Sum.inl i) (Sum.inl j)) he
        simpa [Matrix.fromBlocks,Matrix.one_apply] using hh }
  map_one' := by apply Units.ext; ext i j; simp [Matrix.one_apply]
  map_mul' U V := by
    apply Units.ext
    change (U.val.val*V.val.val).submatrix Sum.inl Sum.inl =
      U.val.val.submatrix Sum.inl Sum.inl * V.val.val.submatrix Sum.inl Sum.inl
    ext i j
    change (U.val.val*V.val.val) (Sum.inl i) (Sum.inl j) = _
    conv_lhs => rw [rightFixer_shape U,rightFixer_shape V,Matrix.fromBlocks_multiply]
    simp

lemma rightFixer_decomposition (U : rightFixer (ι := ι) (κ := κ) (R := R)) :
    U.val = blockInclusion (rightProjection U) *
      rectangleLower (fun p : κ × ι => Multiplicative.ofAdd (U.val.val (Sum.inr p.1) (Sum.inl p.2))) := by
  apply Units.ext
  rw [Units.val_mul,blockInclusion_val]
  change U.val.val = Matrix.fromBlocks _ 0 0 1 * Matrix.fromBlocks 1 0 _ 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
  exact rightFixer_shape U

lemma block_mem_of_generators [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (he : ∀i j h a, elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne h) a ∈ P)
    (hd : ∀i u, singleDiagonal (Sum.inl i) u ∈ P) (U : (Matrix ι ι R)ˣ) :
    blockInclusion U ∈ P := by
  have hU := LinearAlgebra.all_matrix_generated ε hI U
  apply (show generated ≤ P.comap blockInclusion from ?_) hU
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨i,j,h,a,rfl⟩ | ⟨i,u,rfl⟩)
  · change blockInclusion (elementary i j h a) ∈ P
    rw [blockInclusion_elementary]
    exact he i j h a
  · change blockInclusion (singleDiagonal i u) ∈ P
    rw [blockInclusion_singleDiagonal]
    exact hd _ _

lemma rightFixer_generated [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (he : ∀i j h a, elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne h) a ∈ P)
    (hd : ∀i u, singleDiagonal (Sum.inl i) u ∈ P)
    (hr : ∀i j a, elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a ∈ P) :
    rightFixer ≤ P := by
  intro U hU
  change (⟨U,hU⟩ : rightFixer).val ∈ P
  rw [rightFixer_decomposition]
  exact P.mul_mem (block_mem_of_generators ε hI he hd _) (rectangleLower_mem hr _)

def fixer (S : Finset ι) : Subgroup (Matrix ι ι R)ˣ :=
  ⨅ k : {k // k ∈ S}, MulAction.stabilizer (Matrix ι ι R)ˣ (Pi.single k.val (1 : R) : ι → R)

lemma mem_fixer_iff (S : Finset ι) (U : (Matrix ι ι R)ˣ) :
    U ∈ fixer S ↔ ∀ k ∈ S, ∀ i, U.val i k = (1 : Matrix ι ι R) i k := by
  simp only [fixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
  constructor
  · intro h k hk i
    have hh := congrFun (h ⟨k,hk⟩) i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh
  · intro h k
    ext i
    have hh := h k.val k.property i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh

def splitEquiv (S : Finset ι) : {i // i ∉ S} ⊕ {i // i ∈ S} ≃ ι :=
  (Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (S : Set ι))

omit [Fintype ι] in
@[simp] lemma splitEquiv_inl (S : Finset ι) (i : {i // i ∉ S}) : splitEquiv S (.inl i) = i.val := rfl
omit [Fintype ι] in
@[simp] lemma splitEquiv_inr (S : Finset ι) (i : {i // i ∈ S}) : splitEquiv S (.inr i) = i.val := rfl

lemma relabel_fixer_right (S : Finset ι) {U : (Matrix ι ι R)ˣ} (hU : U ∈ fixer S) :
    relabel (splitEquiv S).symm U ∈ rightFixer := by
  apply (mem_rightFixer_iff _).mpr
  intro i k
  have he := (mem_fixer_iff S U).mp hU k.val k.property (splitEquiv S i)
  change U.val (splitEquiv S i) k.val = (1 : Matrix _ _ R) i (Sum.inr k)
  rw [he]
  change (if splitEquiv S i = splitEquiv S (Sum.inr k) then (1 : R) else 0) =
    if i = Sum.inr k then 1 else 0
  congr 1
  exact propext (splitEquiv S).injective.eq_iff

lemma fixer_generated [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (S : Finset ι) {P : Subgroup (Matrix ι ι R)ˣ}
    (he : ∀i j h a, j ∉ S → elementary i j h a ∈ P)
    (hd : ∀i u, i ∉ S → singleDiagonal i u ∈ P) : fixer S ≤ P := by
  intro U hU
  have hh : relabel (splitEquiv S) (relabel (splitEquiv S).symm U) ∈ P := by
    apply (rightFixer_generated ε hI (P := P.comap (relabel (splitEquiv S))) ?_ ?_ ?_)
      (relabel_fixer_right S hU)
    · intro i j h a
      change relabel (splitEquiv S) (elementary (Sum.inl i) (Sum.inl j) _ a) ∈ P
      rw [relabel_elementary]
      exact he i.val j.val (Subtype.coe_injective.ne h) a j.property
    · intro i u
      change relabel (splitEquiv S) (singleDiagonal (Sum.inl i) u) ∈ P
      rw [relabel_singleDiagonal]
      exact hd i.val u i.property
    · intro i j a
      change relabel (splitEquiv S) (elementary (Sum.inr i) (Sum.inl j) _ a) ∈ P
      rw [relabel_elementary]
      exact he i.val j.val (fun h => j.property (h ▸ i.property)) a j.property
  simpa only [LinearAlgebra.relabel_symm_apply] using hh

lemma elementary_mem_fixer (S : Finset ι) (i j : ι) (h : i ≠ j) (a : R) (hj : j ∉ S) :
    elementary i j h a ∈ fixer S := by
  apply (mem_fixer_iff S _).mpr
  intro k hk l
  have hjk : j ≠ k := fun he => hj (he ▸ hk)
  simp [elementary,Matrix.add_apply,hjk]

lemma singleDiagonal_mem_fixer (S : Finset ι) (i : ι) (u : Rˣ) (hi : i ∉ S) :
    singleDiagonal i u ∈ fixer S := by
  apply (mem_fixer_iff S _).mpr
  intro k hk l
  have hki : k ≠ i := fun he => hi (he ▸ hk)
  by_cases hl : l = k
  · subst l; simp [singleDiagonal,diagonal,hki]
  · simp [singleDiagonal,diagonal,hl]

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma card_triple_le (i j k : ι) : ({i,j,k} : Finset ι).card ≤ 5 := by
  have h1 := Finset.card_insert_le i ({j,k} : Finset ι)
  have h2 := Finset.card_insert_le j ({k} : Finset ι)
  simp only [Finset.card_singleton] at h2
  omega

lemma root_conjugate_reverse (t i j : ι) (hti : t≠i) (htj : t≠j) (hij : i≠j) (a b : R) :
    root i j hij a * root t i hti b * (root i j hij a)⁻¹ =
      root t j htj (-(b*a)) * root t i hti b := by
  let S : Finset ι := {t,i,j}
  have h1 := root_mem_local S i j hij a (by simp [S]) (by simp [S])
  have h2 := root_mem_local S t i hti b (by simp [S]) (by simp [S])
  have h3 := root_mem_local S t j htj (-(b*a)) (by simp [S]) (by simp [S])
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem h1 h2) ((localGroup S).inv_mem h1))
    ((localGroup S).mul_mem h3 h2)
  simp only [map_mul,map_inv,evaluate_root]
  apply Units.ext
  change (1+Matrix.single i j a) * (1+Matrix.single t i b) * (1+Matrix.single i j (-a)) =
    (1+Matrix.single t j (-(b*a))) * (1+Matrix.single t i b)
  simp [add_mul,mul_add,htj.symm,hij.symm,←Matrix.single_neg]
  abel

lemma root_conjugate_row_mem (t i j : ι) (hij : i≠j) (_hit : i≠t) (hjt : j≠t)
    (a : R) (k : ι) (htk : t≠k) (b : R) :
    root i j hij a * root t k htk b * (root i j hij a)⁻¹ ∈ rowGroup t := by
  by_cases hk : k=i
  · subst k
    rw [root_conjugate_reverse t i j htk hjt.symm hij]
    exact (rowGroup t).mul_mem (root_mem_row _ _ _ _) (root_mem_row _ _ _ _)
  · rw [(root_commute i j t k hij htk hjt (Ne.symm hk) a b).eq,mul_inv_cancel_right]
    exact root_mem_row _ _ _ _

lemma diag_conjugate_root_matrix (i t j : ι) (htj : t≠j) (u : Rˣ) (b : R) :
    singleDiagonal i u * elementary t j htj b * (singleDiagonal i u)⁻¹ =
    elementary t j htj ((if t=i then (u:R) else 1)*b*(if j=i then (u⁻¹:Rˣ).val else 1)) := by
  apply Units.ext
  ext k l
  change ((Matrix.diagonal (fun k => (if k=i then u else 1).val) *
    (1+Matrix.single t j b)) * Matrix.diagonal (fun k => (if k=i then u else 1).inv)) k l = _
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,elementary_val,Matrix.add_apply,
    Matrix.one_apply,Matrix.single_apply]
  by_cases hkl : k=l
  · subst l
    have hn : ¬(t=k ∧ j=k) := by rintro ⟨rfl,rfl⟩; exact htj rfl
    simp only [ite_eq_right hn,add_zero]
    by_cases hk : k=i <;> simp [hk]
  · by_cases hkt : t=k
    · subst k
      by_cases hjl : j=l
      · subst l; by_cases hti : t=i <;> by_cases hji : j=i <;> simp_all
      · simp [hkl,hjl]
    · simp [hkl,hkt]

lemma diag_conjugate_root (i t j : ι) (htj : t≠j) (u : Rˣ) (b : R) :
    diag i u * root t j htj b * (diag i u)⁻¹ =
    root t j htj ((if t=i then (u:R) else 1)*b*(if j=i then (u⁻¹:Rˣ).val else 1)) := by
  let S : Finset ι := {i,t,j}
  have h1 := diag_mem_local S i u (by simp [S])
  have h2 := root_mem_local S t j htj b (by simp [S]) (by simp [S])
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem h1 h2) ((localGroup S).inv_mem h1))
    (root_mem_local S _ _ _ _ (by simp [S]) (by simp [S]))
  simpa only [map_mul,map_inv,evaluate_root,evaluate_diag] using diag_conjugate_root_matrix i t j htj u b

lemma root_normalizes_row (t i j : ι) (hij : i≠j) (hit : i≠t) (hjt : j≠t) (a : R) :
    root i j hij a ∈ Subgroup.normalizer (rowGroup (R := R) t : Set _) := by
  have hh (a : R) : rowGroup t ≤ (rowGroup t).comap (MulAut.conj (root i j hij a)).toMonoidHom := by
    apply rowGroup_le
    intro k htk b
    exact root_conjugate_row_mem t i j hij hit hjt a k htk b
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx; exact hh a hx
  · intro hx
    have he := hh (-a) hx
    change root i j hij (-a) * (root i j hij a * x * (root i j hij a)⁻¹) * (root i j hij (-a))⁻¹ ∈ rowGroup t at he
    simpa only [MulAut.conj_apply,root_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

lemma diag_normalizes_row (t i : ι) (u : Rˣ) :
    diag i u ∈ Subgroup.normalizer (rowGroup (R := R) t : Set _) := by
  have hh (u : Rˣ) : rowGroup t ≤ (rowGroup t).comap (MulAut.conj (diag i u)).toMonoidHom := by
    apply rowGroup_le
    intro j htj b
    change diag i u * root t j htj b * (diag i u)⁻¹ ∈ rowGroup t
    rw [diag_conjugate_root]
    exact root_mem_row _ _ _ _
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx; exact hh u hx
  · intro hx
    have he := hh u⁻¹ hx
    change diag i u⁻¹ * (diag i u * x * (diag i u)⁻¹) * (diag i u⁻¹)⁻¹ ∈ rowGroup t at he
    simpa only [MulAut.conj_apply,diag_inv,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he

def complementary (t : ι) : Subgroup (Group (ι := ι) (R := R)) := localGroup (Finset.univ.erase t)
def parabolic (t : ι) : Subgroup (Group (ι := ι) (R := R)) := complementary t ⊔ rowGroup t

lemma complementary_normalizes_row (t : ι) :
    complementary (R := R) t ≤ Subgroup.normalizer (rowGroup (R := R) t : Set (Group (ι := ι) (R := R))) := by
  rw [complementary,localGroup_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,hg,rfl⟩
  cases g with
  | root i j h a =>
    obtain ⟨hi,hj⟩ := Finset.insert_subset_iff.mp hg
    have hi' : i≠t := (Finset.mem_erase.mp hi).1
    have hj' : j≠t := (Finset.mem_erase.mp (Finset.singleton_subset_iff.mp hj)).1
    exact root_normalizes_row t i j h hi' hj' a
  | diag i u => exact diag_normalizes_row t i u

lemma parabolic_decomposition (t : ι) {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) :
    ∃l∈complementary t, ∃r∈rowGroup t, g=l*r := by
  have he := Subgroup.coe_mul_of_left_le_normalizer_right (complementary (R := R) t) (rowGroup t)
    (complementary_normalizes_row t)
  change g∈(↑(complementary (R := R) t ⊔ rowGroup t) : Set (Group (ι := ι) (R := R))) at hg
  rw [he] at hg
  obtain ⟨l,hl,r,hr,hg⟩ := hg
  exact ⟨l,hl,r,hr,hg.symm⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma embedded_row_eq_one (S : Finset ι) (t : ι) (ht : t∉S)
    (U : (Matrix {i // i∈S} {i // i∈S} R)ˣ)
    (A : {j : ι // j≠t} → Multiplicative R)
    (h : embed (Function.Embedding.subtype (·∈S)) U * rowUnits t A =1) : U=1 := by
  have hx : embed (Function.Embedding.subtype (·∈S)) U = rowUnits t A⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  apply Units.ext
  ext i j
  have hh := congrArg (fun V : (Matrix ι ι R)ˣ => V.val i.val j.val) hx
  have hh : U.val i j = (rowUnits t A⁻¹).val i.val j.val :=
    (embed_entry (R := R) (Function.Embedding.subtype (·∈S)) U i j).symm.trans hh
  have hi : i.val≠t := fun he => ht (he ▸ i.property)
  change U.val i j = (1+rowMatrix t A⁻¹) i.val j.val at hh
  simpa only [Matrix.add_apply,rowMatrix,ite_eq_right hi,add_zero,Units.val_one,Matrix.one_apply,Subtype.coe_inj] using hh

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma root_mem_parabolic (t i j : ι) (h : i≠j) (a : R) (hj : j≠t) :
    root i j h a ∈ parabolic t := by
  by_cases hi : i=t
  · subst i
    exact (show rowGroup t ≤ parabolic (R := R) t from le_sup_right) (root_mem_row _ _ _ _)
  · apply (show complementary t ≤ parabolic (R := R) t from le_sup_left)
    exact root_mem_local _ _ _ _ _ (by simp [hi]) (by simp [hj])

lemma diag_mem_parabolic (t i : ι) (u : Rˣ) (hi : i≠t) : diag i u ∈ parabolic t := by
  apply (show complementary t ≤ parabolic (R := R) t from le_sup_left)
  exact diag_mem_local _ _ _ (by simp [hi])

lemma parabolic_le {t : ι} {P : Subgroup (Group (ι := ι) (R := R))}
    (he : ∀ i j h a, j≠t → root i j h a∈P)
    (hd : ∀ i u, i≠t → diag i u∈P) : parabolic t ≤ P := by
  apply sup_le
  · rw [complementary,localGroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨g,hg,rfl⟩
    cases g with
    | root i j h a =>
      exact he _ _ _ _ (Finset.mem_erase.mp (Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp hg).2)).1
    | diag i u => exact hd _ _ (Finset.mem_erase.mp (Finset.singleton_subset_iff.mp hg)).1
  · apply rowGroup_le
    intro j h a
    exact he _ _ _ _ h.symm

lemma evaluate_parabolic_le (t : ι) : (parabolic (R := R) t).map evaluate ≤ fixer {t} := by
  rw [Subgroup.map_le_iff_le_comap]
  apply parabolic_le
  · intro i j h a hj
    change evaluate (root i j h a) ∈ fixer {t}
    rw [evaluate_root]
    exact elementary_mem_fixer _ _ _ _ _ (by simpa using hj)
  · intro i u hi
    change evaluate (diag i u) ∈ fixer {t}
    rw [evaluate_diag]
    exact singleDiagonal_mem_fixer _ _ _ (by simpa using hi)

lemma evaluate_parabolic [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (t : ι) : (parabolic (R := R) t).map evaluate = fixer {t} := by
  apply le_antisymm (evaluate_parabolic_le t)
  apply fixer_generated ε hI
  · intro i j h a hj
    exact ⟨root i j h a,root_mem_parabolic t i j h a (by simpa using hj),evaluate_root _ _ _ _⟩
  · intro i u hi
    exact ⟨diag i u,diag_mem_parabolic t i u (by simpa using hi),evaluate_diag _ _⟩

lemma parabolic_product_kernel (t : ι)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    (l : Group (ι := {i // i∈Finset.univ.erase t}) (R := R))
    (A : {j : ι // j≠t} → Multiplicative R)
    (he : evaluate (inclusion (Function.Embedding.subtype (·∈Finset.univ.erase t)) l * rowHom t A)=1) :
    inclusion (Function.Embedding.subtype (·∈Finset.univ.erase t)) l * rowHom t A=1 := by
  have hmap : embed (Function.Embedding.subtype (·∈Finset.univ.erase t)) (evaluate l) * rowUnits t A = 1 := by
    simpa only [map_mul,evaluate_inclusion_apply,evaluate_rowHom_apply] using he
  have hl1 : evaluate l=1 := embedded_row_eq_one (Finset.univ.erase t) t
    (Finset.notMem_erase t Finset.univ) (evaluate l) A hmap
  have hl0 : l=1 := ih (hl1.trans (evaluate.map_one).symm)
  simp only [hl0,map_one,one_mul] at he ⊢
  exact row_faithful (R := R) t (g := rowHom t A) (h := 1) ⟨A,rfl⟩ (rowGroup t).one_mem (he.trans (evaluate.map_one).symm)

lemma parabolic_kernel_trivial (t : ι)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) (he : evaluate g=1) : g=1 := by
  obtain ⟨l,hl,r,hr,rfl⟩ := parabolic_decomposition t hg
  rw [complementary,←range_inclusion] at hl
  obtain ⟨l,rfl⟩ := hl
  obtain ⟨A,rfl⟩ := hr
  exact parabolic_product_kernel t ih l A he

lemma parabolic_faithful (t : ι)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    {g h : Group (ι := ι) (R := R)} (hg : g∈parabolic t) (hh : h∈parabolic t)
    (he : evaluate g=evaluate h) : g=h := by
  apply mul_inv_eq_one.mp
  apply parabolic_kernel_trivial t ih ((parabolic t).mul_mem hg ((parabolic t).inv_mem hh))
  simp [he]

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def permutation : Equiv.Perm ι →* (Matrix ι ι R)ˣ := Matrix.permMatrixHom.toHomUnits

@[simp] lemma permutation_val (p : Equiv.Perm ι) :
    (permutation (R := R) p).val = p⁻¹.permMatrix R := rfl

lemma permutation_entry (p : Equiv.Perm ι) (i j : ι) :
    (permutation (R := R) p).val i j = if i=p j then 1 else 0 := by
  simp only [permutation_val,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_some_iff]
  congr 1
  exact propext (p.symm_apply_eq)

lemma permutation_mul (p : Equiv.Perm ι) (A : Matrix ι ι R) :
    (permutation p).val * A = A.submatrix p.symm id := by
  exact PEquiv.toMatrix_toPEquiv_mul p.symm A

lemma mul_permutation (A : Matrix ι ι R) (p : Equiv.Perm ι) :
    A * (permutation p).val = A.submatrix id p := by
  exact PEquiv.mul_toMatrix_toPEquiv A p.symm

lemma permutation_conjugate (p : Equiv.Perm ι) (U : (Matrix ι ι R)ˣ) :
    permutation p * U * (permutation p)⁻¹ = relabel p U := by
  apply Units.ext
  rw [Units.val_mul,Units.val_mul,←map_inv,permutation_mul,mul_permutation]
  rfl

lemma permutation_conjugate_elementary (p : Equiv.Perm ι) (i j : ι) (h : i≠j) (a : R) :
    permutation p * elementary i j h a * (permutation p)⁻¹ =
      elementary (p i) (p j) (p.injective.ne h) a := by
  rw [permutation_conjugate,relabel_elementary]

lemma permutation_conjugate_diagonal (p : Equiv.Perm ι) (i : ι) (u : Rˣ) :
    permutation p * singleDiagonal i u * (permutation p)⁻¹ = singleDiagonal (p i) u := by
  rw [permutation_conjugate,relabel_singleDiagonal]

lemma permutation_smul (p : Equiv.Perm ι) (v : ι → R) :
    permutation (R := R) p • v = v ∘ p.symm := by
  ext i
  change ∑ j, (permutation p).val i j * v j = v (p.symm i)
  simp only [permutation_entry,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_eq_single (p.symm i)]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    intro he
    exact hj ((p.injective (by simpa using he.symm)))
  · simp

@[simp] lemma permutation_smul_single (p : Equiv.Perm ι) (i : ι) :
    permutation (R := R) p • (Pi.single i 1 : ι → R) = Pi.single (p i) 1 := by
  rw [permutation_smul]
  ext j
  simp [Pi.single_apply,Function.comp_apply,Equiv.symm_apply_eq]

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def swap (i j : ι) (h : i≠j) : Group (ι := ι) (R := R) :=
  root i j h 1 * root j i h.symm (-1) * root i j h 1 * diag i (-1)

lemma swap_mem_local (S : Finset ι) (i j : ι) (h : i≠j) (hi : i∈S) (hj : j∈S) :
    swap (R := R) i j h ∈ localGroup S :=
  (localGroup S).mul_mem ((localGroup S).mul_mem
    ((localGroup S).mul_mem (root_mem_local S i j h 1 hi hj) (root_mem_local S j i h.symm (-1) hj hi))
    (root_mem_local S i j h 1 hi hj)) (diag_mem_local S i (-1) hi)

lemma evaluate_swap (i j : ι) (h : i≠j) : evaluate (swap (R := R) i j h) = permutation (Equiv.swap i j) := by
  simp only [swap,map_mul,evaluate_root,evaluate_diag]
  apply Units.ext
  ext k l
  change (((1+Matrix.single i j (1:R)) * (1+Matrix.single j i (-1:R)) *
    (1+Matrix.single i j (1:R))) * Matrix.diagonal (fun k => (if k=i then (-1:Rˣ) else 1).val)) k l = _
  rw [Matrix.mul_diagonal,permutation_entry]
  simp only [add_mul,mul_add,one_mul,mul_one]
  simp only [Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,mul_one,mul_neg]
  simp only [Matrix.add_apply,Matrix.single_apply,Matrix.one_apply,add_zero]
  by_cases hki : k=i <;> by_cases hkj : k=j <;> by_cases hli : l=i <;> by_cases hlj : l=j <;>
    simp_all [Equiv.swap_apply_def,eq_comm]

lemma swap_square (i j : ι) (h : i≠j) : swap (R := R) i j h * swap i j h =1 := by
  have hm := swap_mem_local (R := R) {i,j} i j h (by simp) (by simp)
  apply local_faithful {i,j} (by have := Finset.card_insert_le i ({j}:Finset ι); simp only [Finset.card_singleton] at this; omega)
    ((localGroup _).mul_mem hm hm) (localGroup _).one_mem
  rw [map_mul,evaluate_swap,←map_mul,Equiv.swap_mul_self,map_one,map_one]

lemma swap_braid (i j k : ι) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    swap (R := R) i j hij * swap j k hjk * swap i j hij = swap j k hjk * swap i j hij * swap j k hjk := by
  let S : Finset ι := {i,j,k}
  have hs := swap_mem_local (R := R) S i j hij (by simp [S]) (by simp [S])
  have ht := swap_mem_local (R := R) S j k hjk (by simp [S]) (by simp [S])
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem hs ht) hs)
    ((localGroup S).mul_mem ((localGroup S).mul_mem ht hs) ht)
  simp only [map_mul,evaluate_swap]
  rw [←map_mul,←map_mul,←map_mul,←map_mul]
  congr 1
  rw [Equiv.swap_mul_swap_mul_swap hij hik]
  rw [Equiv.swap_comm i j,Equiv.swap_comm j k,Equiv.swap_mul_swap_mul_swap hjk.symm hik.symm,Equiv.swap_comm]

end
end SourceBurnside.Stability.SmallPresentation

end
section
end

end OAI
