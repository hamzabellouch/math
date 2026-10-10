import Mathlib
import OAI.Probability.SKBarriers.Dynamics.BankAvoidance

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

theorem overlap_orient_right_abs {n : ℕ} (ε : Bool) (x y : Config n) :
    |overlap x (orient ε y)|=|overlap x y| := by
  rw [overlap_comm,overlap_orient_abs,overlap_comm]

theorem exists_orient_overlap {n : ℕ} (x y : Config n) {q : ℝ} (hq : q≤|overlap x y|) :
    ∃ ε : Bool, q≤overlap (orient ε x) y := by
  by_cases h : 0≤overlap x y
  · exact ⟨false,by simpa only [orient,Bool.false_eq_true,ite_false,abs_of_nonneg h] using hq⟩
  · refine ⟨true,?_⟩
    change q≤overlap (flip x) y
    rw [overlap_comm,overlap_flip_right,overlap_comm]
    simpa only [abs_of_neg (lt_of_not_ge h)] using hq

def orientedBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n) (j : Fin p) : Finset (Config n) :=
  Finset.univ.image (fun a : Fin (K j) × Bool => orient a.2 (z ⟨j,a.1⟩))

theorem mem_orientedBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (j : Fin p) (v : Config n) : v∈orientedBankPool K z j ↔ ∃ a ε, v=orient ε (z ⟨j,a⟩) := by
  simp only [orientedBankPool,Finset.mem_image,Finset.mem_univ,true_and,Prod.exists]
  aesop

theorem flip_mem_orientedBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (j : Fin p) {v : Config n} (hv : v∈orientedBankPool K z j) : flip v∈orientedBankPool K z j := by
  obtain ⟨a,ε,rfl⟩ := (mem_orientedBankPool K z j v).mp hv
  apply (mem_orientedBankPool K z j _).mpr
  refine ⟨a,!ε,?_⟩
  cases ε <;> simp [orient]

def natBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n) (j : ℕ) : Finset (Config n) :=
  if h : j<p then orientedBankPool K z ⟨j,h⟩ else {fun _ => false}

def natBankDefault {n p : ℕ} (K : Fin p → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n) (j : ℕ) : Config n :=
  if h : j<p then z ⟨⟨j,h⟩,⟨0,hK ⟨j,h⟩⟩⟩ else fun _ => false

theorem natBankDefault_mem {n p : ℕ} (K : Fin p → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n) :
    ∀j,natBankDefault K hK z j∈natBankPool K z j := by
  intro j
  unfold natBankDefault natBankPool
  split_ifs with h
  · exact (mem_orientedBankPool K z ⟨j,h⟩ _).mpr ⟨⟨0,hK ⟨j,h⟩⟩,false,rfl⟩
  · exact Finset.mem_singleton_self _

def blockPrior (p B : ℕ) (j : Fin p) : Finset (Fin p) :=
  Finset.univ.filter (fun i => j.val/B*B ≤ i.val ∧ i.val<j.val)

@[simp] theorem mem_blockPrior (p B : ℕ) (i j : Fin p) :
    i∈blockPrior p B j ↔ j.val/B*B ≤ i.val ∧ i.val<j.val := by simp [blockPrior]

theorem blockPrior_not_self (p B : ℕ) (j : Fin p) : j∉blockPrior p B j := by simp

theorem bank_pool_coverage {n p : ℕ} (K : Fin p → ℕ) (B : ℕ) (z : BankIndex K → Config n)
    (t q : ℝ) (x : Config n) (hx : ¬bankCoverageBad K (blockPrior p B) t q z x)
    (j : ℕ) (hj : j<p) (v : ℕ → Config n) (hv : ∀i<j,v i∈natBankPool K z i)
    (hc : ∀i,j/B*B ≤ i → i<j → |overlap (v i) x|≤3*t) :
    ∃ w∈natBankPool K z j, q≤overlap w x ∧ ∀i,j/B*B ≤ i → i<j → |overlap (v i) w|≤3*t := by
  let jj : Fin p := ⟨j,hj⟩
  have hg (i : BankPrior (blockPrior p B) jj) :
      ∃ a ε, v i.val.val=orient ε (z ⟨i.val,a⟩) := by
    have hij : i.val.val<j := (mem_blockPrior p B i.val jj).mp i.property |>.2
    have H := hv i.val.val hij
    rw [natBankPool,dite_eq_left i.val.isLt] at H
    exact (mem_orientedBankPool K z i.val _).mp H
  choose T ε hT using hg
  have hcell : bankCell K (blockPrior p B) t z jj T x := by
    intro i
    have hi := (mem_blockPrior p B i.val jj).mp i.property
    have H := hc i.val.val hi.1 hi.2
    rw [hT i,overlap_orient_abs] at H
    exact H
  have hfresh : ∃ a : Fin (K jj), bankCell K (blockPrior p B) t z jj T (z ⟨jj,a⟩) ∧ q≤|overlap x (z ⟨jj,a⟩)| := by
    by_contra H
    apply hx
    exact ⟨jj,T,hcell,by simpa only [not_exists] using H⟩
  obtain ⟨a,ha,hq⟩ := hfresh
  rw [overlap_comm] at hq
  obtain ⟨δ,hδ⟩ := exists_orient_overlap (z ⟨jj,a⟩) x hq
  refine ⟨orient δ (z ⟨jj,a⟩),?_,hδ,?_⟩
  · rw [natBankPool,dite_eq_left hj]
    exact (mem_orientedBankPool K z jj _).mpr ⟨a,δ,rfl⟩
  · intro i hil hij
    let ii : BankPrior (blockPrior p B) jj := ⟨⟨i,hij.trans hj⟩,(mem_blockPrior p B _ _).mpr ⟨hil,hij⟩⟩
    have he : v i=orient (ε ii) (z ⟨ii.val,T ii⟩) := hT ii
    rw [he,overlap_orient_abs,overlap_orient_right_abs]
    exact ha ii

theorem bank_pool_no_triple {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (S : Finset (ReplicaConfig n 3)) (hz : ¬bankTripleBad (fun i : BankIndex K => i.1.val) S z)
    (i j k : Fin p) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (v w u : Config n) (hv : v∈orientedBankPool K z i) (hw : w∈orientedBankPool K z j) (hu : u∈orientedBankPool K z k) :
    (![v,w,u] : ReplicaConfig n 3)∉S := by
  obtain ⟨a,ε,rfl⟩ := (mem_orientedBankPool K z i v).mp hv
  obtain ⟨b,δ,rfl⟩ := (mem_orientedBankPool K z j w).mp hw
  obtain ⟨c,η,rfl⟩ := (mem_orientedBankPool K z k u).mp hu
  intro H
  apply hz
  refine ⟨(⟨i,a⟩,⟨j,b⟩,⟨k,c⟩,![ε,δ,η]),?_,H⟩
  exact ⟨fun h => hij (Fin.ext h),fun h => hik (Fin.ext h),fun h => hjk (Fin.ext h)⟩

theorem bank_pool_no_vertex {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n)
    (S : Finset (ReplicaConfig n 3)) (x : Config n)
    (hx : ¬bankVertexBad (fun i : BankIndex K => i.1.val) S z x)
    (i j : Fin p) (hij : i≠j) (v w : Config n)
    (hv : v∈orientedBankPool K z i) (hw : w∈orientedBankPool K z j) (e : Equiv.Perm (Fin 3)) :
    ((![v,w,x] : ReplicaConfig n 3) ∘ e)∉S := by
  obtain ⟨a,ε,rfl⟩ := (mem_orientedBankPool K z i v).mp hv
  obtain ⟨b,δ,rfl⟩ := (mem_orientedBankPool K z j w).mp hw
  intro H
  apply hx
  refine ⟨(⟨i,a⟩,⟨j,b⟩,(fun k => (![ε,δ,false] : Fin 3 → Bool) (e k)),e),fun h => hij (Fin.ext h),?_⟩
  have he : (fun k => orient ((![ε,δ,false] : Fin 3 → Bool) k) ((![z ⟨i,a⟩,z ⟨j,b⟩,x] : ReplicaConfig n 3) k)) =
      (![orient ε (z ⟨i,a⟩),orient δ (z ⟨j,b⟩),x] : ReplicaConfig n 3) := by funext k; fin_cases k <;> rfl
  change ((fun k => orient ((![ε,δ,false] : Fin 3 → Bool) k) ((![z ⟨i,a⟩,z ⟨j,b⟩,x] : ReplicaConfig n 3) k)) ∘ e)∈S
  rw [he]
  exact H

end SK.Analytic

end
end

end OAI
