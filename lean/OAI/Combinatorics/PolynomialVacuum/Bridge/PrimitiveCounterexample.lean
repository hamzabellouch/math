import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeWordMass
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Lift

namespace OAI

namespace PolynomialVacuumBridge.Corridor
namespace BridgeWord

def zigzagVertices (i : ℤ) : ℕ → List Vertex
  | 0 => [.up i 0,.down i 0]
  | k+1 => [.up i 0,.down i 0]++zigzagVertices (i+1) k

def upperZigzagWord : ℕ → List Bool
  | 0 => [true,true]
  | k+1 => [true,false]++upperZigzagWord k

def zigzagWord : ℕ → List Bool
  | 0 => [false,true]
  | k+1 => [false,false]++upperZigzagWord k

def column : Vertex → ℤ
  | .up i _ => i
  | .down i _ => i

theorem zigzag_bounds (i : ℤ) (k : ℕ) (v : Vertex) (hv : v∈zigzagVertices i k) :
    i≤column v ∧ layer v=0 := by
  induction k generalizing i with
  | zero => simp only [zigzagVertices,List.mem_cons,List.not_mem_nil,or_false] at hv
            rcases hv with rfl|rfl <;> simp [column,layer]
  | succ k ih =>
    simp only [zigzagVertices,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with (rfl|rfl)|hv
    · simp [column,layer]
    · simp [column,layer]
    · have := ih (i+1) hv; constructor <;> omega

theorem zigzag_nodup (i : ℤ) (k : ℕ) : (zigzagVertices i k).Nodup := by
  induction k generalizing i with
  | zero => simp [zigzagVertices]
  | succ k ih =>
    apply List.nodup_append.mpr
    refine ⟨by simp,ih (i+1),?_⟩
    intro v hv u hu he
    have hb := (zigzag_bounds (i+1) k u hu).1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl <;> rw [← he] at hb <;> simp only [column] at hb <;> omega

theorem zigzag_first (i : ℤ) (k : ℕ) : Vertex.up i 0∈zigzagVertices i k := by
  cases k <;> simp [zigzagVertices]
theorem zigzag_last_up (i : ℤ) (k : ℕ) : Vertex.up (i+k) 0∈zigzagVertices i k := by
  induction k generalizing i with
  | zero => simp [zigzagVertices]
  | succ k ih =>
    have hi := ih (i+1)
    apply List.mem_append_right
    simpa [Nat.cast_add,add_assoc,add_left_comm,add_comm] using hi

@[simp] theorem zigzag_step_up2 (i : ℤ) : advance (.up i 0,2) true=(.down i 0,1) := by
  simp only [advance,outgoingSlot,ite_true,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,neighbor,ite_false]
@[simp] theorem zigzag_step_up0 (i : ℤ) : advance (.up i 0,0) false=(.down i 0,1) := by
  simp only [advance,outgoingSlot,Bool.false_eq_true,ite_false,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,neighbor,ite_true]
@[simp] theorem zigzag_step_down_false (i : ℤ) : advance (.down i 0,1) false=(.up (i+1) 0,2) := by
  simp only [advance,outgoingSlot,Bool.false_eq_true,ite_false,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,neighbor,zero_add]
@[simp] theorem zigzag_step_down_true (i : ℤ) : advance (.down i 0,1) true=(.up i 1,0) := by
  simp only [advance,outgoingSlot,ite_true,Fin.reduceAdd,Fin.isValue,Fin.reduceEq,neighbor,zero_add]

theorem upperZigzag_trace (i : ℤ) (k : ℕ) :
    traced (.up i 0,2) (upperZigzagWord k)=zigzagVertices i k ∧
    terminalGerm (.up i 0,2) (upperZigzagWord k)=(.up (i+k) 1,0) := by
  induction k generalizing i with
  | zero => simp [upperZigzagWord,zigzagVertices,traced,terminalGerm]
  | succ k ih =>
    simp only [upperZigzagWord,traced_append,terminalGerm_append,traced,terminalGerm,
      zigzag_step_up2,zigzag_step_down_false]
    rw [(ih (i+1)).1,(ih (i+1)).2]
    simp [zigzagVertices,Nat.cast_add,add_left_comm,add_comm]

theorem zigzag_trace (k : ℕ) :
    traced bottomSource (zigzagWord k)=zigzagVertices 0 k ∧
    terminalGerm bottomSource (zigzagWord k)=(.up k 1,0) := by
  cases k with
  | zero => simp [zigzagWord,zigzagVertices,bottomSource,traced,terminalGerm]
  | succ k =>
    simp only [zigzagWord,traced_append,terminalGerm_append,bottomSource,traced,terminalGerm,
      zigzag_step_up0,zigzag_step_down_false,zero_add]
    rw [(upperZigzag_trace 1 k).1,(upperZigzag_trace 1 k).2]
    simp [zigzagVertices,Nat.cast_add,add_comm]

def zigzag (k : ℕ) : BridgeWord where
  word := zigzagWord k
  height := 1
  endX := k
  distinct := by rw [(zigzag_trace k).1]; exact zigzag_nodup 0 k
  terminal := (zigzag_trace k).2
  inStrip := by
    intro v hv
    rw [(zigzag_trace k).1] at hv
    have := (zigzag_bounds 0 k v hv).2
    rw [this]
    norm_num

theorem height_one_primitive (A : BridgeWord) (hA : A.height=1) : A.IsPrimitive := by
  have hn : A≠1 := by intro he; simp [he] at hA
  refine ⟨hn,?_⟩
  intro B C he
  by_cases hB : B=1
  · exact Or.inl hB
  · right
    by_contra hC
    have hb := positive_of_nonempty hB
    have hc := positive_of_nonempty hC
    have hh := congrArg BridgeWord.height he
    simp only [height_mul,hA] at hh
    omega

theorem zigzag_primitive (k : ℕ) : (zigzag k).IsPrimitive := height_one_primitive _ rfl

def CylinderSafe (M : ℕ) (A : BridgeWord) : Prop :=
  ((traced bottomSource A.word).map (PolynomialVacuumCylinder.projectVertex M)).Nodup

theorem zigzag_unsafe (M : ℕ) (hM : 0<M) : ¬ CylinderSafe M (zigzag M) := by
  intro hs
  unfold CylinderSafe at hs
  change ((traced bottomSource (zigzagWord M)).map _).Nodup at hs
  rw [(zigzag_trace M).1] at hs
  have hinj := (List.nodup_map_iff_inj_on (zigzag_nodup 0 M)).mp hs
  have he := hinj (.up 0 0) (zigzag_first 0 M) (.up M 0)
    (by simpa using zigzag_last_up 0 M) (by simp [PolynomialVacuumCylinder.projectVertex])
  have := congrArg column he
  norm_num [column] at this
  omega

end BridgeWord
end PolynomialVacuumBridge.Corridor

end OAI
