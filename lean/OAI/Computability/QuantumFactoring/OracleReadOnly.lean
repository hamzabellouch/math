import Mathlib
import OAI.Computability.QuantumFactoring.ExactnessFurther2
import OAI.Computability.QuantumFactoring.PreparedOracle

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

@[simp] lemma Instruction.target_reverse {q : ℕ} (o : Instruction q) : o.reverse.target=o.target := rfl
@[simp] lemma Instruction.target_place {p q : ℕ} (w : Register p q) (o : Instruction p) :
    (o.place w).target=w o.target := rfl
@[simp] lemma notAt_target {q : ℕ} (t : Fin q) : (notAt t).target=t := rfl
@[simp] lemma cnotAt_target {q : ℕ} (a t : Fin q) (ha : a≠t) : (cnotAt a t ha).target=t := rfl
@[simp] lemma toffoliAt_target {q : ℕ} (a b t : Fin q) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    (toffoliAt a b t hab hat hbt).target=t := rfl

lemma BooleanOp.compile_target {q : ℕ} {t : Fin q} (b : BooleanOp q t) :
    ∀ o∈b.compile,o.target=t := by
  cases b with
  | constant b=>cases b <;> simp [BooleanOp.compile]
  | copy=>simp [BooleanOp.compile]
  | neg=>simp [BooleanOp.compile]
  | conj a b ha hb=>simp only [BooleanOp.compile];split_ifs <;> simp

lemma BooleanProgram.compile_target {q n : ℕ} (P : BooleanProgram q)
    (h : ∀ a∈P,n≤a.1.val) : ∀ o∈P.compile,n≤o.target.val := by
  intro o ho
  obtain ⟨a,ha,ho⟩:=List.mem_flatMap.mp ho
  rw [a.2.compile_target o ho]
  exact h a ha

lemma BoolNet.program_target {n k q : ℕ} (p : BoolNet n k) (h : k≤q) :
    ∀ a∈p.program h,n≤a.1.val := by
  induction p with
  | input=>simp [BoolNet.program]
  | @add k p b ih=>
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ih (by omega) a ha
    · have he:=List.mem_singleton.mp ha
      subst a
      exact p.input_le

lemma BooleanNetwork.copyPrefix_target {k m : ℕ} (f : Fin m→Fin k) (t : ℕ) (h : t ≤ m) :
    ∀ a∈copyPrefix f t h,k≤a.1.val := by
  induction t with
  | zero=>simp [copyPrefix]
  | succ t ih=>
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ih (by omega) a ha
    · have he:=List.mem_singleton.mp ha
      subst a
      simp

lemma BooleanNetwork.oracle_target {n m : ℕ} (c : BooleanNetwork n m) :
    ∀ o∈c.oracle,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · rcases List.mem_append.mp ho with ho|ho
    · exact BooleanProgram.compile_target _ (c.net.program_target _) o ho
    · exact c.net.input_le.trans (BooleanProgram.compile_target _
        (copyPrefix_target _ _ _) o ho)
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
    rw [Instruction.target_reverse]
    exact BooleanProgram.compile_target _ (c.net.program_target _) a (List.mem_reverse.mp ha)

/-- Compute/copy/uncompute never targets a read-only input, including on
malformed scratch states. This global property is what reflection needs. -/
lemma BooleanNetwork.oracleOn_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count≤r) :
    ∀ o∈oracleOn c hr,n≤o.target.val := by
  intro o ho
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ho
  rw [Instruction.target_place,oraclePlacement_val]
  have hn:=c.oracle_target a ha
  simp only [oracleIndex,ite_eq_right (Nat.not_lt.mpr hn)]
  split_ifs <;> omega

lemma targetProgram_target {n m r : ℕ} (P : List (Instruction m)) :
    ∀ o∈targetProgram n r P,n≤o.target.val := by
  intro o ho
  obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp ho
  rw [Instruction.target_place,targetRegister_val]
  omega

lemma preparedOracle_target {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count≤r)
    (P : List (Instruction m)) : ∀ o∈preparedOracle c hr P,n≤o.target.val := by
  intro o ho
  rcases List.mem_append.mp ho with ho|ho
  · exact c.oracleOn_target hr o ho
  · exact targetProgram_target P o ho

/-- The bit prefix is preserved for every input sector, without any data
correctness or clean-work premise. -/
lemma preparedOracle_readOnly {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count≤r)
    (P : List (Instruction m)) :
    ReadOnly (Finset.univ.filter (fun i : Fin (n+m+r)=>i.val<n)) (preparedOracle c hr P) := by
  intro o ho hi
  have hn:=preparedOracle_target c hr P o ho
  have hl:=(Finset.mem_filter.mp hi).2
  omega

end ExactQuantumFactoring


end

end OAI
