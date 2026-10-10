import OAI.InformationTheory.QuantumCircuit.Toffoli
import OAI.InformationTheory.QuantumCircuit.Reflection

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- A physical one-qubit gate, as a local layer. -/
def singleLocal {N : ℕ} (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ) : LocalLayer N :=
  fun i => if i=q then u else 1

lemma local_gate_matrix {N : ℕ} (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ) :
    Gate.matrix (.local q u) = localMatrix (singleLocal q u) := by
  classical
  change tensorMatrix (fun i => if i=q then (u:QubitOperator) else 1) =
    tensorMatrix (fun i => ((singleLocal q u i):QubitOperator))
  congr 1
  funext i
  unfold singleLocal
  split_ifs <;> rfl

lemma reflectList_rotate {N : ℕ} (l : List (Count N)) (L : LocalLayer N) :
    reflectList (l.map (fun A => A.rotate L)) = conjugate (localMatrix L) (reflectList l) := by
  induction l with
  | nil => simp [reflectList,conjugate_one (localMatrix_unitary L)]
  | cons A l ih =>
    simp only [List.map_cons,reflectList,List.prod_cons,List.map_map] at ih ⊢
    rw [conjugate_mul (localMatrix_unitary L),← ih]
    congr 1
    simp only [reflect,conjugate_sub,conjugate_one (localMatrix_unitary L),conjugate_smul]
    rw [A.rotate_zero L]
    rfl

lemma reflectList_rotate_commute {N : ℕ} (l : List (Count N)) (L : LocalLayer N) :
    localMatrix L*reflectList l = reflectList (l.map (fun A => A.rotate L))*localMatrix L := by
  rw [reflectList_rotate,conjugate]
  simp only [mul_assoc,Unitary.star_mul_self_of_mem (localMatrix_unitary L),mul_one]

/-- Local gates are moved to the right by rotating the product axes; supports
are unchanged, so a disjoint physical layer yields one reflection layer. -/
def normalCounts {N : ℕ} : List (Gate N) → List (Count N)
  | [] => []
  | .local q u :: l => (normalCounts l).map (fun A => A.rotate (singleLocal q u))
  | .toffoli c t _ :: l => toffoliCount c t :: normalCounts l

def normalLocal {N : ℕ} : List (Gate N) → LocalLayer N
  | [] => fun _ => 1
  | .local q u :: l => fun i => singleLocal q u i * normalLocal l i
  | .toffoli _ _ _ :: l => normalLocal l

lemma normalCounts_support {N : ℕ} (l : List (Gate N)) :
    ∀ A ∈ normalCounts l, ∃ g ∈ l, A.support=g.support := by
  induction l with
  | nil => simp [normalCounts]
  | cons g l ih =>
    cases g with
    | «local» q u =>
      intro A hA
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
      obtain ⟨g,hg,hBg⟩ := ih B hB
      exact ⟨g,List.mem_cons_of_mem _ hg,hBg⟩
    | toffoli c t ht =>
      intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact ⟨.toffoli c t ht,List.mem_cons_self ..,rfl⟩
      · obtain ⟨g,hg,hAg⟩ := ih A hA
        exact ⟨g,List.mem_cons_of_mem _ hg,hAg⟩

lemma normalCounts_disjoint {N : ℕ} (l : List (Gate N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    (normalCounts l).Pairwise (fun A B => Disjoint A.support B.support) := by
  induction l with
  | nil => simp [normalCounts]
  | cons g l ih =>
    have hparts := List.pairwise_cons.mp hl
    clear hl
    cases g with
    | «local» q u =>
      exact (ih hparts.2).map (fun A : Count N => A.rotate (singleLocal q u)) (fun _ _ h => h)
    | toffoli c t ht =>
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih hparts.2⟩
      intro A hA
      obtain ⟨g,hg',hAg⟩ := normalCounts_support l A hA
      change Disjoint (Gate.support (.toffoli c t ht)) A.support
      rw [hAg]
      exact hparts.1 g hg'

lemma gateList_normal {N : ℕ} (l : List (Gate N)) :
    (l.map Gate.matrix).prod = reflectList (normalCounts l)*localMatrix (normalLocal l) := by
  induction l with
  | nil => simp [normalCounts,normalLocal,reflectList,localMatrix]
  | cons g l ih =>
    cases g with
    | «local» q u =>
      simp only [List.map_cons,List.prod_cons,normalCounts,normalLocal]
      rw [local_gate_matrix,ih,← mul_assoc,reflectList_rotate_commute,mul_assoc,localMatrix_mul]
    | toffoli c t ht =>
      simp only [List.map_cons,List.prod_cons,normalCounts,normalLocal]
      rw [toffoli_reflection,ih]
      simp only [reflectList,List.map_cons,List.prod_cons,mul_assoc]

lemma physicalLayer_isCircuit {N : ℕ} (P : PhysicalLayer N) :
    IsCircuit 1 (physicalLayerMatrix P) := by
  let R : ReflectionLayer N := ⟨normalCounts P.gates,normalCounts_disjoint _ P.disjoint⟩
  refine ⟨1,R,normalLocal P.gates,?_,?_⟩
  · exact ⟨fun _ => 1,by simp [localMatrix]⟩
  · rw [one_mul,reflectionMatrix_eq]
    exact gateList_normal P.gates

lemma physicalCircuit_isCircuit {N : ℕ} (l : List (PhysicalLayer N)) :
    IsCircuit l.length (physicalCircuitMatrix l) := by
  induction l with
  | nil => exact ⟨fun _ => 1,by simp [physicalCircuitMatrix,localMatrix]⟩
  | cons L l ih =>
    have h := ih.mul (physicalLayer_isCircuit L)
    simpa only [physicalCircuitMatrix,List.map_cons,List.reverse_cons,List.prod_append,
      List.prod_singleton,List.length_cons] using h

lemma IsCircuit.succ {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) : IsCircuit (d+1) U := by
  refine ⟨U,⟨[],by simp⟩,fun _ => 1,hU,?_⟩
  simp [reflectionMatrix,localMatrix]

lemma IsCircuit.mono {N d e : ℕ} {U : Operator N} (hU : IsCircuit d U) (hde : d ≤ e) :
    IsCircuit e U := by
  induction hde with
  | refl => exact hU
  | step h ih => exact ih.succ

lemma IsCircuit.local_mul {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) (L : LocalLayer N) :
    IsCircuit d (localMatrix L*U) := by
  have hL : IsCircuit 0 (localMatrix L) := ⟨L,rfl⟩
  simpa only [Nat.zero_add] using hL.mul hU

end QAC

end

end OAI
