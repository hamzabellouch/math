import Mathlib
import OAI.Analysis.BoundedHochschild.CentralHomotopy

namespace OAI

/-! Bar-complex identities and the square-zero Hochschild differential. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
namespace BoundedHochschild

lemma mergeInputs_mergeInputs {M : Type*} [Semigroup M] {n : ℕ}
    (v : Fin (n+3) → M) (i : Fin (n+1)) (j : Fin (n+2)) (hj : j.val ≤ i.val) :
    mergeInputs (mergeInputs v j) i =
      mergeInputs (mergeInputs v i.succ) (Fin.castLT j (by omega)) := by
  funext k
  simp only [mergeInputs, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
    Fin.val_castLT]
  split_ifs <;> try simp_all only <;> try omega
  all_goals try contradiction
  all_goals try rfl
  all_goals try simp only [mul_assoc]
  all_goals congr 1 <;> apply Fin.ext <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

variable {M : Type*} [CStarAlgebra M]

 

def barDifferential {n : ℕ} (F : (Fin (n+1) → M) → M) : (Fin (n+2) → M) → M :=
  fun v => ∑ j : Fin (n+1), ((-1:ℂ)^j.val) • F (mergeInputs v j)

lemma barDifferential_squared {n : ℕ} (F : (Fin (n+1) → M) → M)
    (v : Fin (n+3) → M) : barDifferential (barDifferential F) v=0 := by
  classical
  simp only [barDifferential, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm,← Finset.sum_product',Finset.univ_product_univ]
  let P := Fin (n+1) × Fin (n+2)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S,← eq_neg_iff_add_eq_zero,← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt),ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S,φ,Finset.compl_filter,Finset.mem_filter_univ,Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ,Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i',j'⟩ hij'
    simp_rw [S,Finset.compl_filter,Finset.mem_filter_univ,not_le] at hij'
    refine ⟨(j'.pred (by intro h; simp [h] at hij'),i'.castSucc),?_,?_⟩
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ,Fin.castLT_castSucc,Fin.succ_pred]
  · rintro ⟨i,j⟩ hij
    dsimp only [φ]
    rw [← neg_smul]
    have hji : j.val ≤ i.val := (Finset.mem_filter.mp hij).2
    rw [mergeInputs_mergeInputs v i j hji]
    congr 1
    simp only [Fin.val_succ,Fin.val_castLT,pow_succ,mul_neg,mul_one]
    ring

end BoundedHochschild

 

open scoped BigOperators
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

lemma mergeInputs_cons_zero {n : ℕ} (v : Fin (n+1) → M) (a : M) :
    mergeInputs (Fin.cons a v) 0=Fin.cons (a*v 0) (fun i : Fin n => v i.succ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs,Fin.succ_ne_zero]

lemma mergeInputs_cons_succ {n : ℕ} (v : Fin (n+1) → M) (a : M) (j : Fin n) :
    mergeInputs (Fin.cons a v) j.succ=Fin.cons a (mergeInputs v j) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs,Fin.castSucc_succ]

 

def barEnvelope {n : ℕ} (f : Cochain M n) : (Fin (n+2) → M) → M :=
  fun v => v 0*f (fun i => v i.succ.castSucc)*v (Fin.last (n+1))

lemma barEnvelope_apply {n : ℕ} (f : Cochain M n) (a b : M) (v : Fin n → M) :
    barEnvelope f (Fin.snoc (Fin.cons a v) b)=a*f v*b := by
  simp only [barEnvelope,Fin.snoc_last]
  have h0 : (Fin.snoc (Fin.cons a v) b : Fin (n+2) → M) 0=a := by
    change (Fin.snoc (Fin.cons a v) b : Fin (n+2) → M) (0 : Fin (n+1)).castSucc=a
    simp
  have hv : (fun i : Fin n => (Fin.snoc (Fin.cons a v) b : Fin (n+2) → M) i.succ.castSucc)=v := by
    ext i; simp only [Fin.snoc_castSucc,Fin.cons_succ]
  rw [h0,hv]

lemma barDifferential_envelope_apply {n : ℕ} (f : Cochain M n) (a b : M)
    (v : Fin (n+1) → M) :
    barDifferential (barEnvelope f) (Fin.snoc (Fin.cons a v) b)=
      a*differentialValue f v*b := by
  rw [barDifferential,Fin.sum_univ_castSucc]
  simp only [mergeInputs_snoc_castSucc,Fin.val_castSucc]
  rw [Fin.sum_univ_succ]
  simp only [mergeInputs_cons_zero,mergeInputs_cons_succ,barEnvelope_apply,
    Fin.val_zero,pow_zero,one_smul,Fin.val_succ,mergeInputs_snoc_last,Fin.val_last]
  have hi : (fun i : Fin (n+1) => (Fin.cons a v : Fin (n+2) → M) i.castSucc)=Fin.cons a (fun i : Fin n => v i.castSucc) := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.castSucc_succ,Fin.cons_succ]
  have hl : (Fin.cons a v : Fin (n+2) → M) (Fin.last (n+1))=v (Fin.last n) := by
    change (Fin.cons a v : Fin (n+2) → M) (Fin.last n).succ=_
    simp
  rw [hi,hl,barEnvelope_apply]
  simp only [differentialValue,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,mul_assoc]
  try abel

lemma barDifferential_envelope {n : ℕ} (f : Cochain M n) :
    barDifferential (barEnvelope f)=barEnvelope (differential f) := by
  ext v
  have hv : v=Fin.snoc (Fin.cons (v 0) (fun i : Fin (n+1) => v i.succ.castSucc)) (v (Fin.last (n+2))) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp only [Fin.snoc_castSucc,Fin.cons_succ]
  rw [hv,barDifferential_envelope_apply,barEnvelope_apply,differential_apply]

 

theorem differential_squared {n : ℕ} (f : Cochain M n) :
    differential (differential f)=0 := by
  ext v
  have h := barDifferential_squared (barEnvelope f) (Fin.snoc (Fin.cons (1:M) v) 1)
  rw [barDifferential_envelope,barDifferential_envelope,barEnvelope_apply,one_mul,mul_one] at h
  exact h

lemma differential_is_cocycle {n : ℕ} (f : Cochain M n) (v : Fin (n+2) → M) :
    differentialValue (differential f) v=0 := by
  rw [← differential_apply,differential_squared]
  rfl

end BoundedHochschild
end

end OAI
