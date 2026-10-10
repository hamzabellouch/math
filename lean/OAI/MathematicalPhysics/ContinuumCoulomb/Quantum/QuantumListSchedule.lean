import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleProgram

namespace OAI

/-! Validity, fixed-round termination and full-space energy bounds for the
literal list-work routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open Matrix MediatorListProgram

theorem partition_zero (xs : List Entry) (e : Entry) (he : e ∈ partition false xs) : e.1=0 := by
  have h := (List.mem_filter.mp he).2
  by_contra hn
  simp [selected,hn] at h

theorem partition_positive (xs : List Entry) (e : Entry) (he : e ∈ partition true xs) : 0<e.1 := by
  have h := (List.mem_filter.mp he).2
  by_cases hz : e.1=0
  · simp [selected,hz] at h
  · omega

theorem erase_append (xs ys : List Entry) : erase (xs++ys)=erase xs++erase ys := List.map_append

theorem erase_block (x : BlockInput) :
    erase (block x) = QuantumListPathProgram.block (blockBondInput x) := by
  simp only [erase,block,QuantumListPathProgram.block,List.map_ofFn]
  rfl

theorem erase_head (xs : List Entry) (i : ℕ) :
    ((xs.drop i).headD zeroEntry).2 = ((erase xs).drop i).headD zeroBond := by
  simp only [erase,← List.map_drop]
  cases xs.drop i <;> rfl

theorem indexed_erase (x : Input) (i : ℕ) :
    blockBondInput (indexed (i,x)) = QuantumListPathProgram.indexed
      (i,(QuantumListPathStep.parameters (stepInput x),erase (partition true x.2.2.2))) := by
  dsimp only [indexed,blockBondInput,QuantumListPathProgram.indexed]
  rw [erase_head]

theorem erase_family (x : Input) :
    erase (family x) = QuantumListPathProgram.family
      (QuantumListPathStep.parameters (stepInput x),erase (partition true x.2.2.2)) := by
  calc
    _ = ((List.range (partition true x.2.2.2).length).map
        (fun i => erase (block (indexed (i,x))))).flatten := by
      simp only [erase,family,List.map_flatten,List.map_map,Function.comp_def]
    _ = _ := by
      simp_rw [erase_block,indexed_erase]
      simp only [QuantumListPathProgram.family,erase,List.length_map]

theorem erase_value (x : Input) : erase (value x).2.2 = QuantumListPathStep.bonds (stepInput x) := by
  change erase (partition false x.2.2.2++family x) = _
  rw [erase_append,erase_family]
  rfl

theorem partition_matrix (n : ℕ) (xs : List Entry) :
    SourceBondLists.matrix n (erase (partition false xs)++erase (partition true xs)) =
      SourceBondLists.matrix n (erase xs) := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases he : e.1=0
    · simpa [partition,selected,he,erase,SourceBondLists.matrix,add_assoc] using
        congrArg (fun x => SourceBondLists.bondMatrix n e.2+x) ih
    · simp [partition,selected,he,erase,SourceBondLists.matrix] at ih ⊢
      rw [← ih]
      abel

def Valid (s : State) : Prop := SourceBondLists.bounded s.1 (erase s.2.2) ∧
  ∀ e ∈ erase s.2.2, e.1 ≠ e.2.1

theorem partition_valid (s : State) (hs : Valid s) (b : Bool) :
    SourceBondLists.bounded s.1 (erase (partition b s.2.2)) ∧
      ∀ e ∈ erase (partition b s.2.2), e.1 ≠ e.2.1 := by
  have hm : ∀ e ∈ erase (partition b s.2.2), e ∈ erase s.2.2 := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    exact List.mem_map.mpr ⟨a,(List.mem_filter.mp ha).1,rfl⟩
  exact ⟨fun e he => hs.1 e (hm e he),fun e he => hs.2 e (hm e he)⟩

theorem value_valid (x : Input) (hx : Valid x.2) : Valid (value x) := by
  have hk := partition_valid x.2 hx false
  have hs := partition_valid x.2 hx true
  constructor
  · change SourceBondLists.bounded (QuantumListPathStep.count (stepInput x)) (erase (value x).2.2)
    rw [erase_value]
    exact QuantumListPathStep.bonds_bounded (stepInput x) hk.1 hs.1
  · rw [erase_value]
    exact QuantumListPathStep.bonds_noLoops (stepInput x) hk.2 hs.1

def energy (s : State) : ℝ :=
  sourceMatrixBottom s.1 (SourceBondLists.matrix s.1 (erase s.2.2)+(s.2.1:ℂ) • 1)

theorem value_energy_error (x : Input) (hx : Valid x.2) (hN : 0<x.1) :
    |energy (value x)-energy x.2| ≤ 1/(x.1:ℝ) := by
  have hk := partition_valid x.2 hx false
  have hs := partition_valid x.2 hx true
  have h := QuantumListPathStep.energy_error_input (stepInput x) hk.1 hs.1 hk.2 hs.2 hN
  change |sourceMatrixBottom (QuantumListPathStep.count (stepInput x))
    (SourceBondLists.matrix (QuantumListPathStep.count (stepInput x)) (erase (value x).2.2)+
      (QuantumListPathStep.constant (stepInput x):ℂ) • 1)-energy x.2| ≤ _
  rw [erase_value]
  have hp : SourceBondLists.matrix (stepInput x).1.1 ((stepInput x).2.1++(stepInput x).2.2) =
      SourceBondLists.matrix x.2.1 (erase x.2.2.2) := partition_matrix x.2.1 x.2.2.2
  rw [hp] at h
  exact h

theorem indexed_mem (x : Input) (i : ℕ) (hi : i<(partition true x.2.2.2).length) :
    (indexed (i,x)).2.2 ∈ x.2.2.2 := by
  have he : ((partition true x.2.2.2).drop i).headD zeroEntry = (partition true x.2.2.2)[i] := by
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi]
    rfl
  change ((partition true x.2.2.2).drop i).headD zeroEntry ∈ _
  rw [he]
  exact (List.mem_filter.mp (List.getElem_mem hi)).1

theorem value_work_le (x : Input) {D : ℕ} (hD : ∀ e ∈ x.2.2.2, e.1≤D) :
    ∀ e ∈ (value x).2.2, e.1≤D-1 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [partition_zero _ _ he]
    exact Nat.zero_le _
  · obtain ⟨bs,hbs,he⟩ := List.mem_flatten.mp he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
    change blockWork (indexed (i,x)) k ≤ _
    unfold blockWork
    split
    · exact Nat.sub_le_sub_right (hD _ (indexed_mem x i (List.mem_range.mp hi))) 1
    · exact Nat.zero_le _

theorem iterate_valid (N : ℚ) (s : State) (hs : Valid s) (k : ℕ) : Valid (iterate N k s) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact value_valid (N,iterate N k s) ih

theorem iterate_work_le (N : ℚ) (s : State) {D : ℕ} (hD : ∀ e ∈ s.2.2, e.1≤D) (k : ℕ) :
    ∀ e ∈ (iterate N k s).2.2, e.1≤D-k := by
  induction k with
  | zero => exact hD
  | succ k ih =>
    simpa only [iterate,Nat.sub_sub] using value_work_le (N,iterate N k s) ih

theorem iterate_complete (N : ℚ) (s : State) {D : ℕ} (hD : ∀ e ∈ s.2.2, e.1≤D) :
    ∀ e ∈ (iterate N D s).2.2, e.1=0 := by
  intro e he
  have h := iterate_work_le N s hD D e he
  omega

theorem iterate_energy_error {N : ℚ} (hN : 0<N) (s : State) (hs : Valid s) (k : ℕ) :
    |energy (iterate N k s)-energy s| ≤ (k:ℝ)/(N:ℝ) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    calc
      _ ≤ |energy (value (N,iterate N k s))-energy (iterate N k s)|+
          |energy (iterate N k s)-energy s| := abs_sub_le _ _ _
      _ ≤ 1/(N:ℝ)+(k:ℝ)/(N:ℝ) :=
        add_le_add (value_energy_error (N,iterate N k s) (iterate_valid N s hs k) hN) ih
      _ = _ := by push_cast; ring

theorem partition_lengths (xs : List Entry) :
    (partition false xs).length+(partition true xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases he : e.1=0 <;> simp [partition,selected,he] at ih ⊢ <;> omega

theorem family_length (x : Input) : (family x).length=(partition true x.2.2.2).length*3 := by
  have hl (is : List ℕ) : (is.map (fun i => block (indexed (i,x)))).flatten.length=is.length*3 := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_cons,List.flatten_cons,List.length_append,block,List.length_ofFn,
        List.length_cons] at *
      omega
  simpa only [family,List.length_range] using hl (List.range (partition true x.2.2.2).length)

theorem value_size (x : Input) :
    (value x).1+(value x).2.2.length ≤ 5*(x.2.1+x.2.2.2.length) := by
  change QuantumListPathStep.count (stepInput x)+(partition false x.2.2.2++family x).length ≤ _
  simp only [QuantumListPathStep.count,stepInput,erase,List.length_map,List.length_append,family_length]
  have h := partition_lengths x.2.2.2
  omega

theorem iterate_size (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1+(iterate N k s).2.2.length ≤ 5^k*(s.1+s.2.2.length) := by
  induction k with
  | zero => simp only [iterate,pow_zero,one_mul,le_refl]
  | succ k ih =>
    change (value (N,iterate N k s)).1+(value (N,iterate N k s)).2.2.length ≤ _
    exact (value_size (N,iterate N k s)).trans
      (by simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm 5] using Nat.mul_le_mul_left 5 ih)

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
