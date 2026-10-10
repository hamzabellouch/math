import Mathlib
import OAI.Analysis.LaughlinFock.GramCompression
import OAI.Analysis.LaughlinFock.PairNormalization
import OAI.Analysis.LaughlinFock.RelativePerturbation

namespace OAI

/-! Normal Ordering. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker
open scoped Matrix ComplexOrder Kronecker BigOperators

 

def annihilatorList (Q : ℕ) : List (Orbital Q) → FockMatrix Q
  | [] => 1
  | j :: js => annihilatorList Q js * annihilator Q j

@[simp] theorem annihilatorList_nil (Q : ℕ) : annihilatorList Q [] = 1 := rfl

@[simp] theorem annihilatorList_cons (Q : ℕ) (j : Orbital Q) (js : List (Orbital Q)) :
    annihilatorList Q (j :: js) = annihilatorList Q js * annihilator Q j := rfl

 
def basisAnnihilator (Q : ℕ) (A : Occupation Q) : FockMatrix Q :=
  annihilatorList Q (A.sort (· ≤ ·))

theorem annihilatorList_entry_eq_zero (Q : ℕ) (js : List (Orbital Q))
    (A B : Occupation Q) (h : A.card + js.length ≠ B.card) :
    annihilatorList Q js A B = 0 := by
  induction js generalizing A B with
  | nil =>
    have hAB : A ≠ B := by intro hh; subst B; simp at h
    simp [hAB]
  | cons j js ih =>
    rw [annihilatorList_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro C _
    by_cases hCB : C.card + 1 = B.card
    · have hAC : A.card + js.length ≠ C.card := by simp only [List.length_cons] at h; omega
      rw [ih A C hAC, zero_mul]
    · rw [annihilator_entry_eq_zero _ _ _ hCB, mul_zero]

theorem basisAnnihilator_entry_eq_zero (Q : ℕ) (S A B : Occupation Q)
    (h : A.card + S.card ≠ B.card) : basisAnnihilator Q S A B = 0 := by
  apply annihilatorList_entry_eq_zero
  simpa only [Finset.length_sort] using h

theorem annihilatorList_vacuum (Q : ℕ) (js : List (Orbital Q))
    (hs : js.Pairwise (· ≤ ·)) (hd : js.Nodup) (A : Occupation Q) :
    annihilatorList Q js ∅ A = if js.toFinset = A then 1 else 0 := by
  induction js generalizing A with
  | nil => simp only [annihilatorList, Matrix.one_apply, List.toFinset_nil]; rfl
  | cons j js ih =>
    obtain ⟨hjs, hs⟩ := List.pairwise_cons.mp hs
    obtain ⟨hjn, hd⟩ := List.nodup_cons.mp hd
    rw [annihilatorList_cons, mul_annihilator_apply]
    by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA, ih hs hd]
      by_cases he : js.toFinset = A.erase j
      · have heA : insert j js.toFinset = A := by rw [he, Finset.insert_erase hjA]
        have hfilter : A.filter (fun x => x < j) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          rw [← heA, Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact lt_irrefl _
          · exact not_lt_of_ge (hjs x (List.mem_toFinset.mp hx))
        simp only [ite_eq_left he, one_mul, fermionSign, hfilter, Finset.card_empty,
          pow_zero, List.toFinset_cons, ite_eq_left heA]
      · have hneA : insert j js.toFinset ≠ A := by
          intro h
          have hjnot : j ∉ js.toFinset := by simpa using hjn
          apply he
          rw [← h, Finset.erase_insert hjnot]
        simp only [ite_eq_right he, zero_mul, List.toFinset_cons, ite_eq_right hneA]
    · have hneA : insert j js.toFinset ≠ A := by
        intro h; apply hjA; rw [← h]; exact Finset.mem_insert_self _ _
      simp only [ite_eq_right hjA, List.toFinset_cons, ite_eq_right hneA]

 

theorem basisAnnihilator_vacuum (Q : ℕ) (S A : Occupation Q) :
    basisAnnihilator Q S ∅ A = if S=A then 1 else 0 := by
  simpa only [basisAnnihilator, Finset.sort_toFinset] using
    annihilatorList_vacuum Q (S.sort (· ≤ ·)) (S.pairwise_sort _) (S.sort_nodup _) A

theorem basisAnnihilator_same_sector (Q k : ℕ) (S A : SectorOccupation Q k)
    (R : Occupation Q) :
    basisAnnihilator Q S.val R A.val = if R=∅ then if S=A then 1 else 0 else 0 := by
  by_cases hR : R=∅
  · subst R
    rw [basisAnnihilator_vacuum]
    simp only [Subtype.val_inj, ite_true]
  · rw [ite_eq_right hR]
    apply basisAnnihilator_entry_eq_zero
    rw [S.property, A.property]
    have hcard : R.card ≠ 0 := fun h => hR (Finset.card_eq_zero.mp h)
    omega

 
def wedgeAnnihilator (Q k : ℕ) (v : SectorOccupation Q k → ℂ) : FockMatrix Q :=
  ∑ A, star (v A) • basisAnnihilator Q A.val

 
def exteriorLift (Q k : ℕ) (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    FockMatrix Q :=
  ∑ A, ∑ B, M A B • ((basisAnnihilator Q A.val)ᴴ * basisAnnihilator Q B.val)

 

theorem exteriorLift_posSemidef (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) (hM : M.PosSemidef) :
    (exteriorLift Q k M).PosSemidef := by
  let A : SectorOccupation Q k → FockMatrix Q := fun S => basisAnnihilator Q S.val
  have hK : (M ⊗ₖ (1 : FockMatrix Q)).PosSemidef := hM.kronecker Matrix.PosSemidef.one
  have h := hK.conjTranspose_mul_mul_same (stackFamily A)
  simpa only [stackFamily_kronecker, Matrix.mul_one, exteriorLift, A] using h

 

theorem exteriorLift_rankOne (Q k : ℕ) (v w : SectorOccupation Q k → ℂ) :
    exteriorLift Q k (Matrix.vecMulVec v (star w)) =
      (wedgeAnnihilator Q k v)ᴴ * wedgeAnnihilator Q k w := by
  unfold exteriorLift wedgeAnnihilator
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_apply, Pi.star_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  rw [mul_comm]

theorem basisAnnihilator_gram_same_sector (Q k : ℕ) (S T A B : SectorOccupation Q k) :
    ((basisAnnihilator Q S.val)ᴴ * basisAnnihilator Q T.val) A.val B.val =
      (if S=A then (1 : ℂ) else 0) * (if T=B then (1 : ℂ) else 0) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, basisAnnihilator_same_sector]
  rw [Finset.sum_eq_single ∅]
  · simp only [ite_true, apply_ite star, star_one, star_zero]
  · intro R _ hR
    simp only [ite_eq_right hR, star_zero, zero_mul]
  · simp

 
theorem exteriorLift_same_sector (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    (exteriorLift Q k M).submatrix Subtype.val Subtype.val = M := by
  classical
  apply Matrix.ext
  intro A B
  change exteriorLift Q k M A.val B.val = M A B
  simp only [exteriorLift, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    basisAnnihilator_gram_same_sector]
  simp [mul_ite]

 
theorem exteriorLift_below_sector (Q k n : ℕ) (hn : n < k)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    (exteriorLift Q k M).submatrix
      (Subtype.val : SectorOccupation Q n → Occupation Q)
      (Subtype.val : SectorOccupation Q n → Occupation Q) = 0 := by
  classical
  ext A B
  simp only [Matrix.submatrix_apply, exteriorLift, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro S _
  apply Finset.sum_eq_zero
  intro T _
  suffices hzero : (∑ R, star (basisAnnihilator Q S.val R A.val) *
      basisAnnihilator Q T.val R B.val) = 0 by rw [hzero, mul_zero]
  apply Finset.sum_eq_zero
  intro R _
  have h : basisAnnihilator Q T.val R B.val = 0 :=
    basisAnnihilator_entry_eq_zero Q _ _ _ (by rw [T.property, B.property]; omega)
  rw [h, mul_zero]

 

theorem annihilator_swap (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * annihilator Q j = -(annihilator Q j * annihilator Q i) :=
  eq_neg_of_add_eq_zero_left (annihilator_anticommute Q i j)

theorem annihilatorList_append (Q : ℕ) (is js : List (Orbital Q)) :
    annihilatorList Q (is ++ js) = annihilatorList Q js * annihilatorList Q is := by
  induction is with
  | nil => simp
  | cons i is ih => simp only [List.cons_append, annihilatorList_cons, ih, Matrix.mul_assoc]

 

theorem annihilatorList_perm (Q : ℕ) {is js : List (Orbital Q)} (h : is.Perm js) :
    ∃ c : ℂ, annihilatorList Q is = c • annihilatorList Q js := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons i h ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c, by simp only [annihilatorList_cons, hc, Matrix.smul_mul]⟩
  | swap i j js =>
    refine ⟨-1, ?_⟩
    simp only [annihilatorList_cons, Matrix.mul_assoc, neg_one_smul]
    rw [annihilator_swap Q i j, Matrix.mul_neg]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨c, hc⟩ := ih₁
    obtain ⟨d, hd⟩ := ih₂
    exact ⟨c*d, by rw [hc, hd, smul_smul]⟩

theorem annihilatorList_mul_of_mem (Q : ℕ) (js : List (Orbital Q)) (i : Orbital Q)
    (hi : i ∈ js) : annihilatorList Q js * annihilator Q i = 0 := by
  induction js with
  | nil => simp at hi
  | cons j js ih =>
    rw [annihilatorList_cons, Matrix.mul_assoc]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [annihilator_square, Matrix.mul_zero]
    · rw [annihilator_swap Q j i, Matrix.mul_neg, ← Matrix.mul_assoc,
        ih hi, Matrix.zero_mul, neg_zero]

theorem annihilatorList_eq_zero_of_not_nodup (Q : ℕ) (js : List (Orbital Q))
    (h : ¬ js.Nodup) : annihilatorList Q js = 0 := by
  induction js with
  | nil => simp at h
  | cons i js ih =>
    rw [annihilatorList_cons]
    by_cases hi : i ∈ js
    · exact annihilatorList_mul_of_mem Q js i hi
    · have hjs : ¬ js.Nodup := by intro hj; exact h (List.nodup_cons.mpr ⟨hi,hj⟩)
      rw [ih hjs, Matrix.zero_mul]

 

theorem annihilatorList_expansion (Q : ℕ) (js : List (Orbital Q)) (k : ℕ)
    (hk : js.length=k) :
    annihilatorList Q js = ∑ S : SectorOccupation Q k,
      annihilatorList Q js ∅ S.val • basisAnnihilator Q S.val := by
  classical
  by_cases hd : js.Nodup
  · let T : SectorOccupation Q k := ⟨js.toFinset, by rw [List.toFinset_card_of_nodup hd, hk]⟩
    have hperm : js.Perm (js.toFinset.sort (· ≤ ·)) := by
      apply (List.perm_ext_iff_of_nodup hd (js.toFinset.sort_nodup _)).mpr
      intro i
      simp only [Finset.mem_sort, List.mem_toFinset]
    obtain ⟨c, hc⟩ := annihilatorList_perm Q hperm
    change annihilatorList Q js = c • basisAnnihilator Q T.val at hc
    rw [hc, Finset.sum_eq_single T]
    · simp only [Matrix.smul_apply, basisAnnihilator_vacuum, ite_true, smul_eq_mul, mul_one]
    · intro S _ hST
      have hne : T.val ≠ S.val := by
        intro hh; exact hST (Subtype.ext hh.symm)
      simp only [Matrix.smul_apply, basisAnnihilator_vacuum, ite_eq_right hne, smul_eq_mul,
        mul_zero, zero_smul]
    · simp
  · rw [annihilatorList_eq_zero_of_not_nodup Q js hd]
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

 

theorem exteriorLift_congruence {α : Type*} [Fintype α] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) α ℂ) (C : Matrix α α ℂ) :
    exteriorLift Q k (W * C * Wᴴ) =
      ∑ r, ∑ s, C r s •
        ((wedgeAnnihilator Q k (fun A => W A r))ᴴ *
          wedgeAnnihilator Q k (fun A => W A s)) := by
  classical
  have h := quadratic_family_mix (fun A : SectorOccupation Q k => basisAnnihilator Q A.val)
    Wᴴ C
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply,
    exteriorLift, wedgeAnnihilator] using h.symm

 

theorem exteriorLift_of_gram_certificate {α : Type*} [Fintype α] (Q k : ℕ)
    (W : Matrix (SectorOccupation Q k) α ℂ) (C : Matrix α α ℂ) (hC : C.IsHermitian)
    (hG : ((Wᴴ*W) * C * (Wᴴ*W)).PosSemidef) :
    (∑ r, ∑ s, C r s •
        ((wedgeAnnihilator Q k (fun A => W A r))ᴴ *
          wedgeAnnihilator Q k (fun A => W A s))).PosSemidef := by
  rw [← exteriorLift_congruence]
  apply exteriorLift_posSemidef
  exact (gram_compression_posSemidef_iff W C hC).mp hG

 

def AnnihilationSpace (Q k : ℕ) : Submodule ℂ (FockMatrix Q) :=
  Submodule.span ℂ (Set.range (fun S : SectorOccupation Q k => basisAnnihilator Q S.val))

theorem basisAnnihilator_mem (Q k : ℕ) (S : SectorOccupation Q k) :
    basisAnnihilator Q S.val ∈ AnnihilationSpace Q k :=
  Submodule.subset_span ⟨S,rfl⟩

theorem annihilatorList_mem (Q : ℕ) (js : List (Orbital Q)) (k : ℕ) (hk : js.length=k) :
    annihilatorList Q js ∈ AnnihilationSpace Q k := by
  rw [annihilatorList_expansion Q js k hk]
  exact Submodule.sum_mem _ (fun S _ => Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S))

theorem annihilationSpace_normal_form (Q k : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    M = ∑ S : SectorOccupation Q k, M ∅ S.val • basisAnnihilator Q S.val := by
  classical
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨T,rfl⟩ := hM
    rw [Finset.sum_eq_single T]
    · simp only [basisAnnihilator_vacuum, ite_true, one_smul]
    · intro S _ hST
      have hne : T.val ≠ S.val := by intro h; exact hST (Subtype.ext h.symm)
      simp only [basisAnnihilator_vacuum, ite_eq_right hne, zero_smul]
    · simp
  | zero => simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero]
  | add M N hM hN ihM ihN =>
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← ihM, ← ihN]
  | smul r M hM ihM =>
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← ihM]

 
theorem annihilationSpace_ext (Q k : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q k)
    (h : ∀ S : SectorOccupation Q k, M ∅ S.val = N ∅ S.val) : M=N := by
  rw [annihilationSpace_normal_form Q k M hM, annihilationSpace_normal_form Q k N hN]
  simp only [h]

 

theorem annihilationSpace_mul (Q k l : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q l) :
    N * M ∈ AnnihilationSpace Q (k+l) := by
  classical
  rw [annihilationSpace_normal_form Q k M hM, annihilationSpace_normal_form Q l N hN]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  apply Submodule.sum_mem
  intro T _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  rw [basisAnnihilator, basisAnnihilator, ← annihilatorList_append]
  apply annihilatorList_mem
  simp only [List.length_append, Finset.length_sort, S.property, T.property]

theorem annihilator_mem (Q : ℕ) (j : Orbital Q) :
    annihilator Q j ∈ AnnihilationSpace Q 1 := by
  simpa only [annihilatorList_cons, annihilatorList_nil, Matrix.one_mul] using
    annihilatorList_mem Q [j] 1 rfl

theorem coefficientPairAnnihilator_mem (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a ∈ AnnihilationSpace Q 2 := by
  classical
  unfold coefficientPairAnnihilator
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  split_ifs
  · apply Submodule.smul_mem
    exact annihilationSpace_mul Q 1 1 (annihilator_mem Q i) (annihilator_mem Q j)
  · exact Submodule.zero_mem _

theorem pairAnnihilator_mem (Q p : ℕ) :
    pairAnnihilator Q p ∈ AnnihilationSpace Q 2 :=
  coefficientPairAnnihilator_mem Q _

theorem limitPairAnnihilator_mem (L p : ℕ) :
    limitPairAnnihilator L p ∈ AnnihilationSpace L 2 :=
  coefficientPairAnnihilator_mem L _

theorem localPairAnnihilator_mem (L Q p : ℕ) :
    localPairAnnihilator L Q p ∈ AnnihilationSpace L 2 :=
  coefficientPairAnnihilator_mem L _

 

def annihilatorVector (Q k : ℕ) (M : FockMatrix Q) : SectorOccupation Q k → ℂ :=
  fun S => star (M ∅ S.val)

theorem wedgeAnnihilator_mem (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k v ∈ AnnihilationSpace Q k := by
  exact Submodule.sum_mem _ (fun S _ =>
    Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S))

theorem wedgeAnnihilator_annihilatorVector (Q k : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    wedgeAnnihilator Q k (annihilatorVector Q k M) = M := by
  have h := annihilationSpace_normal_form Q k M hM
  simpa only [wedgeAnnihilator, annihilatorVector, star_star] using h.symm

 

theorem exteriorLift_annihilator_product (Q k : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q k) :
    exteriorLift Q k (Matrix.vecMulVec (annihilatorVector Q k M)
      (star (annihilatorVector Q k N))) = Mᴴ * N := by
  rw [exteriorLift_rankOne, wedgeAnnihilator_annihilatorVector Q k M hM,
    wedgeAnnihilator_annihilatorVector Q k N hN]

 
def exteriorLiftLinear (Q k : ℕ) :
    Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ →ₗ[ℂ] FockMatrix Q where
  toFun := exteriorLift Q k
  map_add' M N := by
    simp only [exteriorLift, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [exteriorLift, Matrix.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, RingHom.id_apply]

@[simp] theorem exteriorLift_add (Q k : ℕ)
    (M N : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    exteriorLift Q k (M+N) = exteriorLift Q k M + exteriorLift Q k N :=
  (exteriorLiftLinear Q k).map_add M N

@[simp] theorem exteriorLift_sub (Q k : ℕ)
    (M N : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    exteriorLift Q k (M-N) = exteriorLift Q k M - exteriorLift Q k N :=
  (exteriorLiftLinear Q k).map_sub M N

@[simp] theorem exteriorLift_sum {α : Type*} (Q k : ℕ) (s : Finset α)
    (M : α → Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    exteriorLift Q k (∑ a ∈ s, M a) = ∑ a ∈ s, exteriorLift Q k (M a) :=
  map_sum (exteriorLiftLinear Q k) M s

 

def BodySpace (Q k : ℕ) : Submodule ℂ (FockMatrix Q) :=
  LinearMap.range (exteriorLiftLinear Q k)

theorem bodySpace_product (Q k : ℕ) {M N : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q k) (hN : N ∈ AnnihilationSpace Q k) :
    Mᴴ*N ∈ BodySpace Q k :=
  ⟨_, exteriorLift_annihilator_product Q k hM hN⟩

theorem bodySpace_reconstruct (Q k : ℕ) {M : FockMatrix Q} (hM : M ∈ BodySpace Q k) :
    exteriorLift Q k (M.submatrix
      (Subtype.val : SectorOccupation Q k → Occupation Q) Subtype.val) = M := by
  obtain ⟨A,rfl⟩ := hM
  exact congrArg (exteriorLift Q k) (exteriorLift_same_sector Q k A)

theorem bodySpace_below_sector (Q k n : ℕ) (hn : n < k)
    {M : FockMatrix Q} (hM : M ∈ BodySpace Q k) :
    M.submatrix (Subtype.val : SectorOccupation Q n → Occupation Q)
      (Subtype.val : SectorOccupation Q n → Occupation Q) = 0 := by
  obtain ⟨A,rfl⟩ := hM
  exact exteriorLift_below_sector Q k n hn A

 

theorem bodySpace_two_decomposition (Q k l : ℕ) (hkl : k<l)
    (M A B : FockMatrix Q) (hM : M=A+B)
    (hA : A ∈ BodySpace Q k) (hB : B ∈ BodySpace Q l) :
    M = exteriorLift Q k (M.submatrix
        (Subtype.val : SectorOccupation Q k → Occupation Q) Subtype.val) +
      exteriorLift Q l ((M-A).submatrix
        (Subtype.val : SectorOccupation Q l → Occupation Q) Subtype.val) := by
  rw [hM]
  simp only [Matrix.submatrix_add, Pi.add_apply, bodySpace_below_sector Q l k hkl hB,
    add_zero, add_sub_cancel_left, bodySpace_reconstruct Q k hA,
    bodySpace_reconstruct Q l hB]

 

theorem annihilator_commutes_pair (Q : ℕ) (i j k : Orbital Q) :
    annihilator Q k * (annihilator Q j * annihilator Q i) =
      (annihilator Q j * annihilator Q i) * annihilator Q k := by
  rw [← Matrix.mul_assoc, annihilator_swap Q k j, Matrix.neg_mul,
    Matrix.mul_assoc, annihilator_swap Q k i, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc]

theorem annihilator_commutes_coefficientPair (Q : ℕ)
    (a : Orbital Q → Orbital Q → ℂ) (k : Orbital Q) :
    annihilator Q k * coefficientPairAnnihilator Q a =
      coefficientPairAnnihilator Q a * annihilator Q k := by
  classical
  unfold coefficientPairAnnihilator
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [Matrix.mul_smul, Matrix.smul_mul, annihilator_commutes_pair]
  · simp

theorem coefficientPairs_commute (Q : ℕ) (a b : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a * coefficientPairAnnihilator Q b =
      coefficientPairAnnihilator Q b * coefficientPairAnnihilator Q a := by
  classical
  conv_lhs => lhs; unfold coefficientPairAnnihilator
  conv_rhs => rhs; unfold coefficientPairAnnihilator
  simp only [Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_assoc, annihilator_commutes_coefficientPair,
      ← Matrix.mul_assoc, annihilator_commutes_coefficientPair, Matrix.mul_assoc]
  · simp

theorem pairAnnihilators_commute (Q p r : ℕ) :
    pairAnnihilator Q p * pairAnnihilator Q r =
      pairAnnihilator Q r * pairAnnihilator Q p :=
  coefficientPairs_commute Q _ _

 

theorem annihilationSpace_two_induction (Q : ℕ) (P : FockMatrix Q → Prop)
    (hzero : P 0)
    (hadd : ∀ M N, P M → P N → P (M+N))
    (hsmul : ∀ (c : ℂ) M, P M → P (c • M))
    (hpair : ∀ i j : Orbital Q, P (annihilator Q j * annihilator Q i))
    {M : FockMatrix Q} (hM : M ∈ AnnihilationSpace Q 2) : P M := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨S,rfl⟩ := hM
    have hlen : (S.val.sort (· ≤ ·)).length = 2 := by rw [Finset.length_sort, S.property]
    obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hlen
    simpa only [basisAnnihilator, hij, annihilatorList_cons, annihilatorList_nil,
      Matrix.one_mul] using hpair i j
  | zero => exact hzero
  | add M N _ _ ihM ihN => exact hadd M N ihM ihN
  | smul c M _ ihM => exact hsmul c M ihM

 

theorem pair_monomial_commutator_bodies (Q : ℕ) (i j k l : Orbital Q)
    {M N : FockMatrix Q} (hM : M ∈ AnnihilationSpace Q 2)
    (hN : N ∈ AnnihilationSpace Q 2) :
    Mᴴ * ((annihilator Q j * annihilator Q i) *
        (annihilator Q l * annihilator Q k)ᴴ -
      (annihilator Q l * annihilator Q k)ᴴ *
        (annihilator Q j * annihilator Q i)) * N ∈
      BodySpace Q 2 ⊔ BodySpace Q 3 := by
  let S := BodySpace Q 2 ⊔ BodySpace Q 3
  have htwo : Mᴴ * N ∈ S := Submodule.mem_sup_left (bodySpace_product Q 2 hM hN)
  have hthree (a b : Orbital Q) : Mᴴ * creator Q a * annihilator Q b * N ∈ S := by
    have h := bodySpace_product Q 3
      (annihilationSpace_mul Q 2 1 hM (annihilator_mem Q a))
      (annihilationSpace_mul Q 2 1 hN (annihilator_mem Q b))
    apply Submodule.mem_sup_right
    simpa only [Matrix.conjTranspose_mul, ← creator_eq_adjoint, Matrix.mul_assoc] using h
  have hδtwo (a b c d : Orbital Q) :
      Mᴴ * (orbitalDelta Q a b * orbitalDelta Q c d) * N ∈ S := by
    classical
    by_cases hab : a=b
    · by_cases hcd : c=d
      · simpa only [orbitalDelta, ite_eq_left hab, ite_eq_left hcd, Matrix.one_mul,
          Matrix.mul_one] using htwo
      · simp [orbitalDelta, hab, hcd, S]
    · simp [orbitalDelta, hab, S]
  have hδthree (a b c d : Orbital Q) :
      Mᴴ * (orbitalDelta Q a b * creator Q c * annihilator Q d) * N ∈ S := by
    classical
    by_cases hab : a=b
    · simpa only [orbitalDelta, ite_eq_left hab, Matrix.one_mul, Matrix.mul_assoc] using hthree c d
    · simp only [orbitalDelta, ite_eq_right hab, Matrix.zero_mul, Matrix.mul_zero]
      exact Submodule.zero_mem _
  have hmiddle := pair_normal_order Q i j k l
  have heq : Mᴴ * ((annihilator Q j * annihilator Q i) *
        (annihilator Q l * annihilator Q k)ᴴ -
      (annihilator Q l * annihilator Q k)ᴴ *
        (annihilator Q j * annihilator Q i)) * N =
      (Mᴴ * (orbitalDelta Q i k * orbitalDelta Q j l) * N -
        Mᴴ * (orbitalDelta Q j k * orbitalDelta Q i l) * N) -
        Mᴴ * (orbitalDelta Q i k * creator Q l * annihilator Q j) * N +
        Mᴴ * (orbitalDelta Q j k * creator Q l * annihilator Q i) * N +
        Mᴴ * (orbitalDelta Q i l * creator Q k * annihilator Q j) * N -
        Mᴴ * (orbitalDelta Q j l * creator Q k * annihilator Q i) * N := by
    rw [Matrix.conjTranspose_mul, ← creator_eq_adjoint, ← creator_eq_adjoint, hmiddle]
    noncomm_ring
  rw [heq]
  exact S.sub_mem (S.add_mem (S.add_mem
    (S.sub_mem (S.sub_mem (hδtwo _ _ _ _) (hδtwo _ _ _ _)) (hδthree _ _ _ _))
      (hδthree _ _ _ _)) (hδthree _ _ _ _)) (hδthree _ _ _ _)

 

theorem pair_commutator_bodies (Q : ℕ) {M N P R : FockMatrix Q}
    (hM : M ∈ AnnihilationSpace Q 2) (hN : N ∈ AnnihilationSpace Q 2)
    (hP : P ∈ AnnihilationSpace Q 2) (hR : R ∈ AnnihilationSpace Q 2) :
    Mᴴ * (P*Rᴴ-Rᴴ*P) * N ∈ BodySpace Q 2 ⊔ BodySpace Q 3 := by
  let S := BodySpace Q 2 ⊔ BodySpace Q 3
  refine annihilationSpace_two_induction Q
    (fun P => ∀ R, R ∈ AnnihilationSpace Q 2 → Mᴴ * (P*Rᴴ-Rᴴ*P) * N ∈ S)
    ?_ ?_ ?_ ?_ hP R hR
  · intro R _
    simpa only [Matrix.zero_mul, Matrix.mul_zero, sub_self] using S.zero_mem
  · intro P P' hP hP' R hR
    have heq : Mᴴ * ((P+P')*Rᴴ-Rᴴ*(P+P')) * N =
        Mᴴ*(P*Rᴴ-Rᴴ*P)*N + Mᴴ*(P'*Rᴴ-Rᴴ*P')*N := by noncomm_ring
    rw [heq]
    exact S.add_mem (hP R hR) (hP' R hR)
  · intro c P hP R hR
    simpa only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub] using
      S.smul_mem c (hP R hR)
  · intro i j R hR
    refine annihilationSpace_two_induction Q
      (fun R => Mᴴ * ((annihilator Q j * annihilator Q i)*Rᴴ -
        Rᴴ*(annihilator Q j * annihilator Q i)) * N ∈ S) ?_ ?_ ?_ ?_ hR
    · simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
        sub_self] using S.zero_mem
    · intro R R' hR hR'
      rw [Matrix.conjTranspose_add]
      have heq : Mᴴ * ((annihilator Q j * annihilator Q i)*(Rᴴ+R'ᴴ) -
          (Rᴴ+R'ᴴ)*(annihilator Q j * annihilator Q i)) * N =
          Mᴴ*((annihilator Q j * annihilator Q i)*Rᴴ-Rᴴ*(annihilator Q j * annihilator Q i))*N +
          Mᴴ*((annihilator Q j * annihilator Q i)*R'ᴴ-R'ᴴ*(annihilator Q j * annihilator Q i))*N :=
        by noncomm_ring
      rw [heq]
      exact S.add_mem hR hR'
    · intro c R hR
      simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_sub] using S.smul_mem (star c) hR
    · intro k l
      exact pair_monomial_commutator_bodies Q i j k l hM hN

 

def fourBodyTerm (Q : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range (2*Q-1), ∑ r ∈ Finset.range (2*Q-1),
    (pairAnnihilator Q p * pairAnnihilator Q r)ᴴ *
      (pairAnnihilator Q p * pairAnnihilator Q r)

theorem fourBodyTerm_posSemidef (Q : ℕ) : (fourBodyTerm Q).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro p _
  apply Matrix.posSemidef_sum
  intro r _
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem hamiltonian_mem_bodySpace (Q : ℕ) : hamiltonian Q ∈ BodySpace Q 2 :=
  Submodule.sum_mem _ (fun p _ => bodySpace_product Q 2
    (pairAnnihilator_mem Q p) (pairAnnihilator_mem Q p))

theorem fourBodyTerm_mem_bodySpace (Q : ℕ) : fourBodyTerm Q ∈ BodySpace Q 4 := by
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro r _
  have h := annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q r) (pairAnnihilator_mem Q p)
  exact bodySpace_product Q 4 h h

theorem square_remainder_commutators (Q : ℕ) :
    hamiltonian Q * hamiltonian Q - fourBodyTerm Q =
      ∑ p ∈ Finset.range (2*Q-1), ∑ r ∈ Finset.range (2*Q-1),
        (pairAnnihilator Q p)ᴴ *
          (pairAnnihilator Q p * (pairAnnihilator Q r)ᴴ -
            (pairAnnihilator Q r)ᴴ * pairAnnihilator Q p) * pairAnnihilator Q r := by
  classical
  have hsquare : hamiltonian Q * hamiltonian Q =
      ∑ p ∈ Finset.range (2*Q-1), ∑ r ∈ Finset.range (2*Q-1),
        ((pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) *
          ((pairAnnihilator Q r)ᴴ * pairAnnihilator Q r) := by
    simp only [hamiltonian, Matrix.sum_mul, Matrix.mul_sum]
    exact Finset.sum_comm
  rw [hsquare, fourBodyTerm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [pairAnnihilators_commute Q p r, Matrix.conjTranspose_mul]
  have hc := pairAnnihilators_commute Q r p
  rw [hc]
  noncomm_ring

theorem square_remainder_mem_bodies (Q : ℕ) :
    hamiltonian Q * hamiltonian Q - fourBodyTerm Q ∈ BodySpace Q 2 ⊔ BodySpace Q 3 := by
  rw [square_remainder_commutators]
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro r _
  exact pair_commutator_bodies Q (pairAnnihilator_mem Q p) (pairAnnihilator_mem Q r)
    (pairAnnihilator_mem Q p) (pairAnnihilator_mem Q r)

 

theorem normal_square_of_pair_projection (Q : ℕ)
    (hproj : sectorHamiltonian Q 2 * sectorHamiltonian Q 2 = sectorHamiltonian Q 2) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3) +
        fourBodyTerm Q := by
  obtain ⟨A,hA,B,hB,hAB⟩ := Submodule.mem_sup.mp (square_remainder_mem_bodies Q)
  have hF2 := bodySpace_below_sector Q 4 2 (by omega) (fourBodyTerm_mem_bodySpace Q)
  have hF3 := bodySpace_below_sector Q 4 3 (by omega) (fourBodyTerm_mem_bodySpace Q)
  have hB2 := bodySpace_below_sector Q 3 2 (by omega) hB
  have hA2 : A.submatrix (Subtype.val : SectorOccupation Q 2 → Occupation Q) Subtype.val =
      sectorHamiltonian Q 2 := by
    have h := congrArg (fun X : FockMatrix Q => X.submatrix
      (Subtype.val : SectorOccupation Q 2 → Occupation Q)
      (Subtype.val : SectorOccupation Q 2 → Occupation Q)) hAB
    simp only [Matrix.submatrix_add, Matrix.submatrix_sub, Pi.add_apply, Pi.sub_apply,
      hB2, hF2, add_zero, sub_zero, sectorHamiltonian_square, hproj] at h
    exact h
  have hAH : A=hamiltonian Q := by
    rw [← bodySpace_reconstruct Q 2 hA, hA2]
    exact bodySpace_reconstruct Q 2 (hamiltonian_mem_bodySpace Q)
  have hB3 : B.submatrix (Subtype.val : SectorOccupation Q 3 → Occupation Q) Subtype.val =
      sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3 := by
    have h := congrArg (fun X : FockMatrix Q => X.submatrix
      (Subtype.val : SectorOccupation Q 3 → Occupation Q)
      (Subtype.val : SectorOccupation Q 3 → Occupation Q)) hAB
    simp only [hAH, Matrix.submatrix_add, Matrix.submatrix_sub, Pi.add_apply, Pi.sub_apply,
      hF3, sub_zero, sectorHamiltonian_square] at h
    change sectorHamiltonian Q 3 + _ = _ at h
    exact eq_sub_of_add_eq' h
  have hBform : B = exteriorLift Q 3
      (sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3) := by
    rw [← hB3]
    exact (bodySpace_reconstruct Q 3 hB).symm
  rw [hAH,hBform] at hAB
  exact (eq_sub_iff_add_eq.mp hAB).symm

 
abbrev IncreasingPair (Q : ℕ) := {ij : Orbital Q × Orbital Q // ij.1 < ij.2}

theorem sort_pair {Q : ℕ} (i j : Orbital Q) (hij : i<j) :
    ( {i,j} : Occupation Q).sort (· ≤ ·) = [i,j] := by
  have hd : ([i,j] : List (Orbital Q)).Nodup := by simp [ne_of_lt hij]
  have hs : ([i,j] : List (Orbital Q)).Pairwise (· ≤ ·) := by simp [hij.le]
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
    (List.toFinset_sort (r := (· ≤ ·)) hd).mpr hs

def increasingPairSector (Q : ℕ) (ij : IncreasingPair Q) : SectorOccupation Q 2 :=
  ⟨{ij.val.1,ij.val.2}, by simp [ne_of_lt ij.property]⟩

theorem increasingPairSector_injective (Q : ℕ) : Function.Injective (increasingPairSector Q) := by
  intro ij kl h
  have hs := congrArg (fun S : SectorOccupation Q 2 => S.val.sort (· ≤ ·)) h
  simp only [increasingPairSector, sort_pair _ _ ij.property, sort_pair _ _ kl.property,
    List.cons.injEq, and_true] at hs
  exact Subtype.ext (Prod.ext hs.1 hs.2)

theorem increasingPairSector_surjective (Q : ℕ) : Function.Surjective (increasingPairSector Q) := by
  intro S
  have hlen : (S.val.sort (· ≤ ·)).length = 2 := by rw [Finset.length_sort, S.property]
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hlen
  have hlt : i<j := by
    have hs := S.val.sortedLT_sort
    rw [hij] at hs
    simpa using hs.pairwise
  refine ⟨⟨(i,j),hlt⟩,?_⟩
  apply Subtype.ext
  have h := Finset.sort_toFinset S.val (· ≤ ·)
  rw [hij] at h
  simpa only [increasingPairSector, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] using h

def increasingPairEquiv (Q : ℕ) : IncreasingPair Q ≃ SectorOccupation Q 2 :=
  Equiv.ofBijective (increasingPairSector Q)
    ⟨increasingPairSector_injective Q, increasingPairSector_surjective Q⟩

@[simp] theorem increasingPairEquiv_apply (Q : ℕ) (ij : IncreasingPair Q) :
    increasingPairEquiv Q ij = increasingPairSector Q ij := rfl

theorem increasingPair_sum {X : Type*} [AddCommMonoid X] (Q : ℕ)
    (f : Orbital Q → Orbital Q → X) :
    (∑ ij : IncreasingPair Q, f ij.val.1 ij.val.2) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, if i<j then f i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun ij : Orbital Q × Orbital Q => ij.1 < ij.2)) (by intro ij; simp)
      (fun ij : Orbital Q × Orbital Q => f ij.1 ij.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem basisAnnihilator_pair {Q : ℕ} (i j : Orbital Q) (hij : i<j) :
    basisAnnihilator Q {i,j} = annihilator Q j * annihilator Q i := by
  simp only [basisAnnihilator, sort_pair i j hij, annihilatorList_cons,
    annihilatorList_nil, Matrix.one_mul]

theorem coefficientPair_basis_expansion (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) :
    coefficientPairAnnihilator Q a = ∑ ij : IncreasingPair Q,
      a ij.val.1 ij.val.2 • basisAnnihilator Q (increasingPairSector Q ij).val := by
  change coefficientPairAnnihilator Q a = ∑ ij : IncreasingPair Q,
    a ij.val.1 ij.val.2 • basisAnnihilator Q {ij.val.1,ij.val.2}
  rw [increasingPair_sum Q (fun i j => a i j • basisAnnihilator Q {i,j})]
  unfold coefficientPairAnnihilator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [basisAnnihilator_pair i j hij]
  · rfl

theorem coefficientPair_vacuum (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ)
    (ij : IncreasingPair Q) :
    coefficientPairAnnihilator Q a ∅ (increasingPairSector Q ij).val = a ij.val.1 ij.val.2 := by
  classical
  rw [coefficientPair_basis_expansion]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, basisAnnihilator_vacuum,
    Subtype.val_inj, (increasingPairSector_injective Q).eq_iff]
  simp

 

def pairVector (Q p : ℕ) : SectorOccupation Q 2 → ℂ :=
  annihilatorVector Q 2 (pairAnnihilator Q p)

theorem pairVector_increasing (Q p : ℕ) (ij : IncreasingPair Q) :
    pairVector Q p (increasingPairSector Q ij) = pairCoefficient Q p ij.val.1 ij.val.2 := by
  unfold pairVector annihilatorVector
  change star (coefficientPairAnnihilator Q
    (fun i j => (pairCoefficient Q p i j : ℂ)) ∅ (increasingPairSector Q ij).val) = _
  rw [coefficientPair_vacuum]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem pairVector_orthonormal (Q p r : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ S : SectorOccupation Q 2, star (pairVector Q p S) * pairVector Q r S) =
      if p=r then 1 else 0 := by
  classical
  have hs : (∑ S : SectorOccupation Q 2, star (pairVector Q p S) * pairVector Q r S) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, if i<j then
        (pairCoefficient Q p i j : ℂ) * (pairCoefficient Q r i j : ℂ) else 0 := by
    rw [← (increasingPairEquiv Q).sum_comp
      (fun S => star (pairVector Q p S) * pairVector Q r S)]
    simp only [increasingPairEquiv_apply, pairVector_increasing,
      Complex.star_def, Complex.conj_ofReal]
    exact increasingPair_sum Q (fun i j =>
      (pairCoefficient Q p i j : ℂ) * (pairCoefficient Q r i j : ℂ))
  rw [hs]
  by_cases hpr : p=r
  · subst r
    simp only [ite_true]
    have h := congrArg (fun x : ℝ => (x : ℂ)) (pairCoefficient_norm Q p hQ hp)
    simpa only [Complex.ofReal_sum, Complex.ofReal_one, Complex.ofReal_pow,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero, pow_two, Complex.ofReal_mul] using h
  · rw [ite_eq_right hpr]
    have h := congrArg (fun x : ℝ => (x : ℂ)) (pairCoefficient_orthogonal Q p r hpr)
    simpa only [Complex.ofReal_sum, Complex.ofReal_zero, Complex.ofReal_mul,
      apply_ite (fun x : ℝ => (x : ℂ))] using h

abbrev PairLabel (Q : ℕ) := Fin (2*Q-1)

 
def pairWedgeMatrix (Q : ℕ) : Matrix (SectorOccupation Q 2) (PairLabel Q) ℂ :=
  fun S p => pairVector Q p.val S

theorem pairWedgeMatrix_gram (Q : ℕ) (hQ : 1 ≤ Q) :
    (pairWedgeMatrix Q)ᴴ * pairWedgeMatrix Q = 1 := by
  classical
  ext p r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pairWedgeMatrix,
    pairVector_orthonormal Q p.val r.val hQ (by have := p.isLt; omega), Matrix.one_apply,
    Fin.val_inj]

theorem hamiltonian_exteriorLift (Q : ℕ) :
    exteriorLift Q 2 (pairWedgeMatrix Q * (pairWedgeMatrix Q)ᴴ) = hamiltonian Q := by
  have h := exteriorLift_congruence Q 2 (pairWedgeMatrix Q) 1
  simp only [Matrix.mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  rw [h]
  simp only [pairWedgeMatrix, pairVector,
    wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _)]
  exact Fin.sum_univ_eq_sum_range (fun p => (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) _

theorem sectorHamiltonian_two (Q : ℕ) :
    sectorHamiltonian Q 2 = pairWedgeMatrix Q * (pairWedgeMatrix Q)ᴴ := by
  rw [sectorHamiltonian, ← hamiltonian_exteriorLift]
  exact exteriorLift_same_sector Q 2 _

 

theorem sectorHamiltonian_two_projection (Q : ℕ) (hQ : 1 ≤ Q) :
    sectorHamiltonian Q 2 * sectorHamiltonian Q 2 = sectorHamiltonian Q 2 := by
  rw [sectorHamiltonian_two]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (pairWedgeMatrix Q)ᴴ,
    pairWedgeMatrix_gram Q hQ, Matrix.one_mul]

 

theorem normal_square (Q : ℕ) (hQ : 1 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (sectorHamiltonian Q 3 * sectorHamiltonian Q 3 - sectorHamiltonian Q 3) +
        fourBodyTerm Q :=
  normal_square_of_pair_projection Q (sectorHamiltonian_two_projection Q hQ)

 
def threeWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 3) (PairLabel Q × Orbital Q) ℂ :=
  fun S pj => annihilatorVector Q 3
    (annihilator Q pj.2 * pairAnnihilator Q pj.1.val) S

 
def fourWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 4) (PairLabel Q × PairLabel Q) ℂ :=
  fun S pr => annihilatorVector Q 4
    (pairAnnihilator Q pr.2.val * pairAnnihilator Q pr.1.val) S

theorem basisAnnihilator_singleton (Q : ℕ) (j : Orbital Q) :
    basisAnnihilator Q {j} = annihilator Q j := by
  simp only [basisAnnihilator, Finset.sort_singleton, annihilatorList_cons,
    annihilatorList_nil, Matrix.one_mul]

theorem annihilator_vacuum (Q : ℕ) (j : Orbital Q) (A : Occupation Q) :
    annihilator Q j ∅ A = if {j}=A then 1 else 0 := by
  rw [← basisAnnihilator_singleton, basisAnnihilator_vacuum]

theorem annihilator_mul_vacuum (Q : ℕ) (j : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (annihilator Q j * M) ∅ A = M {j} A := by
  classical
  simp only [Matrix.mul_apply, annihilator_vacuum, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def singletonSectorEquiv (Q : ℕ) : Orbital Q ≃ SectorOccupation Q 1 :=
  Equiv.ofBijective (fun j => ⟨{j}, Finset.card_singleton j⟩)
    ⟨by intro i j h; simpa only [Subtype.mk.injEq, Finset.singleton_inj] using h,
      by intro S; obtain ⟨j,hj⟩ := Finset.card_eq_one.mp S.property
         exact ⟨j, Subtype.ext hj.symm⟩⟩

theorem sum_singleton_support {X : Type*} [AddCommMonoid X] (Q : ℕ)
    (f : Occupation Q → X) (hf : ∀ A, A.card ≠ 1 → f A=0) :
    ∑ A, f A = ∑ j : Orbital Q, f {j} := by
  classical
  calc
    _ = ∑ A ∈ Finset.univ.filter (fun A : Occupation Q => A.card=1), f A := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      exact hf A (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hA)
    _ = ∑ A : SectorOccupation Q 1, f A.val := Finset.sum_subtype _ (by intro A; simp) _
    _ = _ := (singletonSectorEquiv Q).sum_comp (fun A => f A.val) |>.symm

theorem threeWedgeMatrix_apply (Q : ℕ) (S : SectorOccupation Q 3)
    (pj : PairLabel Q × Orbital Q) :
    threeWedgeMatrix Q S pj = star (pairAnnihilator Q pj.1.val {pj.2} S.val) := by
  exact congrArg star (annihilator_mul_vacuum Q pj.2 (pairAnnihilator Q pj.1.val) S.val)

 

theorem sectorHamiltonian_three (Q : ℕ) :
    sectorHamiltonian Q 3 = threeWedgeMatrix Q * (threeWedgeMatrix Q)ᴴ := by
  classical
  ext A B
  change hamiltonian Q A.val B.val = _
  simp only [hamiltonian, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    threeWedgeMatrix_apply, star_star, Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun p => ∑ j : Orbital Q,
    star (pairAnnihilator Q p {j} A.val) * pairAnnihilator Q p {j} B.val)]
  apply Finset.sum_congr rfl
  intro p _
  apply sum_singleton_support
  intro C hC
  have hc : C.card + 2 ≠ B.val.card := by rw [B.property]; omega
  rw [pairAnnihilator_entry_eq_zero p C B.val hc, mul_zero]

 

theorem fourBodyTerm_exteriorLift (Q : ℕ) :
    exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) = fourBodyTerm Q := by
  have h := exteriorLift_congruence Q 4 (fourWedgeMatrix Q) 1
  simp only [Matrix.mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  rw [h]
  simp only [fourWedgeMatrix, wedgeAnnihilator_annihilatorVector Q 4 _
    (annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q _) (pairAnnihilator_mem Q _)),
    Fintype.sum_prod_type]
  simp_rw [pairAnnihilators_commute Q]
  rw [Fin.sum_univ_eq_sum_range (fun p => ∑ r : PairLabel Q,
    (pairAnnihilator Q p * pairAnnihilator Q r.val)ᴴ *
      (pairAnnihilator Q p * pairAnnihilator Q r.val))]
  unfold fourBodyTerm
  apply Finset.sum_congr rfl
  intro p _
  exact Fin.sum_univ_eq_sum_range (fun r =>
    (pairAnnihilator Q p * pairAnnihilator Q r)ᴴ * (pairAnnihilator Q p * pairAnnihilator Q r)) _

 

theorem normal_ordered_square (Q : ℕ) (hQ : 1 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (threeWedgeMatrix Q *
        ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q - 1) * (threeWedgeMatrix Q)ᴴ) +
      exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) := by
  rw [fourBodyTerm_exteriorLift, normal_square Q hQ, sectorHamiltonian_three]
  congr 2
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

end LaughlinFock
end

end OAI
