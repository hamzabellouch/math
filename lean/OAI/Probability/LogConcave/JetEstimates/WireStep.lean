import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Bound

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma Bound.comp {A : I → J → ℝ} {B : J → K → ℝ} {C D : ℝ}
    (hA : Bound A C) (hB : Bound B D) (hC : 0≤C) :
    Bound (fun i k => ∑ j,A i j*B j k) (C*D) := by
  intro v
  have he (i : I) : (∑ k,(∑ j,A i j*B j k)*v k)=
      ∑ j,A i j*(∑ k,B j k*v k) := by
    simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm
  simp_rw [he]
  exact (hA _).trans ((mul_le_mul_of_nonneg_left (hB v) hC).trans_eq (by ring))

lemma bound_identity [DecidableEq I] : Bound (fun i j : I => if i=j then (1:ℝ) else 0) 1 := by
  intro v
  simp

lemma Bound.contract {P : Type*} [Fintype P]
    {A : I → J × P → ℝ} {B : P × K → L → ℝ} {C D : ℝ}
    (hA : Bound A C) (hB : Bound B D) (hC : 0≤C) :
    Bound (fun (i : I × K) (j : J × L) => ∑ p,A i.1 (j.1,p)*B (p,i.2) j.2) (C*D) := by
  classical
  have h₁ := hA.kronecker (bound_identity (I:=K)) hC
  have h₂ := (bound_identity (I:=J)).kronecker hB (by norm_num)
  have h₂' := h₂.reindex (Equiv.prodAssoc J P K) (Equiv.refl (J×L))
  have hh := h₁.comp h₂' (by simpa using hC)
  simp only [mul_one,one_mul] at hh
  convert! hh using 1
  funext i j
  simp only [Fintype.sum_prod_type,Equiv.prodAssoc_apply,Equiv.refl_apply]
  simp [mul_ite,ite_mul]

lemma Bound.entry_sq {A : I → J → ℝ} {C : ℝ} (hA : Bound A C) (i : I) (j : J) :
    (A i j)^2 ≤ C := by
  classical
  have hh := hA (fun k => if k=j then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    ite_pow,one_pow,zero_pow (by decide : (2:ℕ)≠0)] at hh
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (A k j)) (Finset.mem_univ i)).trans hh

lemma Bound.trace_sq {A : I → I → ℝ} {C : ℝ} (hA : Bound A C) :
    (∑ i,A i i)^2 ≤ (Fintype.card I:ℝ)^2*C := by
  have hh := dot_sq (fun _ : I => (1:ℝ)) (fun i => A i i)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  have hg := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset I)) => hA.entry_sq i i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hg
  exact hh.trans ((mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)).trans_eq (by ring))
end LogConcaveSampling.TensorEnergy
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

def wireStep {I O S X Y : Type*} [DecidableEq S]
    (A : O → I → ℝ) (ei : X ≃ I×S) (eo : Y ≃ O×S) : Y → X → ℝ :=
  fun y x => A (eo y).1 (ei x).1 * if (eo y).2=(ei x).2 then 1 else 0

lemma Bound.wireStep {I O S X Y : Type*} [Fintype I] [Fintype O] [Fintype S]
    [Fintype X] [Fintype Y] [DecidableEq S] {A : O → I → ℝ} {C : ℝ}
    (hA : Bound A C) (hC : 0≤C) (ei : X ≃ I×S) (eo : Y ≃ O×S) :
    Bound (wireStep A ei eo) C := by
  have hh := (hA.kronecker (bound_identity (I:=S)) hC).reindex eo ei
  change Bound (fun y x => A (eo y).1 (ei x).1 * if (eo y).2=(ei x).2 then 1 else 0) C
  simpa only [mul_one] using hh

def circuit {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) : ∀n,D n → D 0 → ℝ
  | 0 => fun i j => if i=j then 1 else 0
  | n+1 => fun i j => ∑k,A n i k*circuit A n k j

lemma circuit_bound {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) (C : ℕ → ℝ)
    (hC : ∀k,0≤C k) (hA : ∀k,Bound (A k) (C k)) (n : ℕ) :
    Bound (circuit A n) (∏k∈Finset.range n,C k) := by
  induction n with
  | zero => simpa only [circuit,Finset.range_zero,Finset.prod_empty] using (bound_identity (I:=D 0))
  | succ n ih =>
    simpa only [circuit,Finset.prod_range_succ,mul_comm] using (hA n).comp ih (hC n)

lemma Bound.trace_abs {I : Type*} [Fintype I] {A : I → I → ℝ} {C : ℝ}
    (hA : Bound A (C^2)) (hC : 0≤C) : |∑i,A i i|≤(Fintype.card I:ℝ)*C := by
  have hh := hA.trace_sq
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)).mp
  simpa only [sq_abs,mul_pow] using hh

theorem closed_wire_circuit_bound
    {D I O S : ℕ → Type*} [∀k,Fintype (D k)] [∀k,Fintype (I k)]
    [∀k,Fintype (O k)] [∀k,Fintype (S k)] [∀k,DecidableEq (S k)]
    [DecidableEq (D 0)]
    (A : ∀k,O k → I k → ℝ) (C : ℕ → ℝ)
    (hC : ∀k,0≤C k) (hA : ∀k,Bound (A k) ((C k)^2))
    (ei : ∀k,D k ≃ I k×S k) (eo : ∀k,D (k+1) ≃ O k×S k)
    (n : ℕ) (close : D 0 ≃ D n) :
    |∑i,circuit (fun k => wireStep (A k) (ei k) (eo k)) n (close i) i|≤
      (Fintype.card (D 0):ℝ)*(∏k∈Finset.range n,C k) := by
  have hlocal (k : ℕ) : Bound (wireStep (A k) (ei k) (eo k)) ((C k)^2) :=
    (hA k).wireStep (sq_nonneg _) (ei k) (eo k)
  have hh := (circuit_bound _ (fun k => (C k)^2) (fun k => sq_nonneg _) hlocal n).reindex
    close (Equiv.refl (D 0))
  rw [Finset.prod_pow] at hh
  exact hh.trace_abs (Finset.prod_nonneg (fun k _ => hC k))

lemma cut_bundle_card (d b : ℕ) : Fintype.card (Fin b → Fin d)=d^b := by simp
end LogConcaveSampling.TensorEnergy
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical

variable {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]

abbrev Path (n : ℕ) := ∀k : Fin (n+1),D k.val

def pathWeight (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ) (h : Path (D:=D) n) : ℝ :=
  ∏k : Fin n,A k.val (h k.succ) (h k.castSucc)

omit [∀k,Fintype (D k)] [DecidableEq (D 0)] in
lemma pathWeight_snoc (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ)
    (h : Path (D:=D) n) (y : D (n+1)) :
    pathWeight A (n+1) (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y)=pathWeight A n h*A n y (h (Fin.last n)) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    change A k.val (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y k.succ.castSucc)
      (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y k.castSucc.castSucc) = _
    simp only [Fin.snoc_castSucc]
  · simp only [Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc,Fin.val_last]

theorem circuit_path_expansion (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ)
    (B : D 0 → D n → ℝ) :
    (∑h : Path (D:=D) n,pathWeight A n h*B (h 0) (h (Fin.last n)))=
      ∑i,∑j,circuit A n j i*B i j := by
  induction n with
  | zero =>
    rw [←(Fin.consEquiv (fun k : Fin 1 => D k.val)).sum_comp]
    simp [pathWeight,circuit,Fintype.sum_prod_type]
  | succ n ih =>
    rw [←(Fin.snocEquiv (fun k : Fin (n+2) => D k.val)).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply]
    change (∑y : D (n+1),∑h : Path (D:=D) n,
      pathWeight A (n+1) (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y)*
        B (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y (0 : Fin (n+1)).castSucc)
          (Fin.snoc (α:=fun k : Fin (n+2) => D k.val) h y (Fin.last (n+1))))=_
    simp_rw [pathWeight_snoc,Fin.snoc_castSucc,Fin.snoc_last]
    have hh (y : D (n+1)) :
        (∑h : Path (D:=D) n,pathWeight A n h*A n y (h (Fin.last n))*B (h 0) y)=
        ∑i,∑j,circuit A n j i*(A n y j*B i y) := by
      simpa only [mul_assoc] using ih (fun i j => A n y j*B i y)
    simp_rw [hh]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro y hy
    simp only [circuit,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
