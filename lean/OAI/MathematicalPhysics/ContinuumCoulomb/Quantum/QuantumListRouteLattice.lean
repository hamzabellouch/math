import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRoutePreservation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListLatticeProgram

namespace OAI

/-! The final literal route tape is itself the serialized lattice source.
Its coordinate and edge order are the computed orders, and its exact scalar
offset is removed from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode MediatorListProgram
open ExactQuantumFactoring.BitStackProgram

def latticePacket (s : State) (a b : ℚ) : QuantumListLattice.Input :=
  (s.2.1,erase s.1.2.2,a,b,s.1.2.1)

def latticeOutput (s : State) (a b : ℚ) : BinaryHeisenberg :=
  QuantumListLattice.value (latticePacket s a b)

noncomputable def latticePacketProgram :
    Procedure (prodCode stateCode (prodCode ratCode ratCode))
      QuantumListLattice.inputCode (fun x : State × (ℚ × ℚ) => latticePacket x.1 x.2.1 x.2.2) := by
  let s := Procedure.first stateCode (prodCode ratCode ratCode)
  let t := Procedure.second stateCode (prodCode ratCode ratCode)
  let data := (Procedure.first QuantumListSchedule.stateCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode)))).comp s
  let spatial := (Procedure.second QuantumListSchedule.stateCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode)))).comp s
  let ps := (Procedure.first (listCode pairCode) (listCode (listCode pairCode))).comp spatial
  let tail := (Procedure.second unaryCode (prodCode ratCode (listCode entryCode))).comp data
  let c := (Procedure.first ratCode (listCode entryCode)).comp tail
  let xs := eraseProgram.comp ((Procedure.second ratCode (listCode entryCode)).comp tail)
  let a := (Procedure.first ratCode ratCode).comp t
  let b := (Procedure.second ratCode ratCode).comp t
  exact ps.pair (xs.pair (a.pair (b.pair c)))

noncomputable def latticeOutputProgram :
    Procedure (prodCode stateCode (prodCode ratCode ratCode)) binaryHeisenbergCodec.encode
      (fun x : State × (ℚ × ℚ) => latticeOutput x.1 x.2.1 x.2.2) :=
  QuantumListLattice.program.comp latticePacketProgram

private theorem get_of_eq_ofFn {α : Type} {n : ℕ} {xs : List α} {f : Fin n → α}
    (h : xs=List.ofFn f) (i : Fin xs.length) :
    xs.get i=f ⟨i.val,by simpa only [h,List.length_ofFn] using i.isLt⟩ := by
  subst xs
  simp only [List.get_eq_getElem,List.getElem_ofFn]

theorem represented_length (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P) :
    s.2.1.length=s.1.1 := by rw [hP.1,List.length_ofFn]; rfl

theorem represented_nodup (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P) :
    s.2.1.Nodup := by
  rw [hP.1]
  exact List.nodup_ofFn.mpr P.position_injective

theorem represented_bounded (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P) :
    SourceBondLists.bounded s.2.1.length (erase s.1.2.2) := by
  rw [represented_length s hs P hP]
  exact hs.1

theorem represented_adjacent (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e))) :
    QuantumListLattice.Adjacent s.2.1 (erase s.1.2.2) (represented_bounded s hs P hP) := by
  intro e he
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hw
  rw [get_of_eq_ofFn hP.1,get_of_eq_ofFn hP.1]
  exact ha i

theorem latticeOutput_valid (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e)))
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b) :
    (latticeOutput s a b).Valid := by
  apply QuantumListLattice.value_valid _ _
    (by rw [represented_length s hs P hP]; exact hn)
    (represented_nodup s hs P hP) (represented_bounded s hs P hP) hs.2
    (represented_adjacent s hs P hP ha) a b s.1.2.1 hab

theorem latticeOutput_yes (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e)))
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b) {k : ℕ}
    (hp : (latticeOutput s a b).PolynomialPromise k)
    (he : QuantumListSchedule.energy s.1 ≤ (a:ℝ)) :
    latticeOutput s a b ∈ (sourceHeisenbergPromise k).yes := by
  apply QuantumListLattice.value_mem_yes _ _
    (by rw [represented_length s hs P hP]; exact hn)
    (represented_nodup s hs P hP) (represented_bounded s hs P hP) hs.2
    (represented_adjacent s hs P hP ha) a b s.1.2.1 hab hp
  rw [represented_length s hs P hP]
  exact he

theorem latticeOutput_no (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e)))
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b) {k : ℕ}
    (hp : (latticeOutput s a b).PolynomialPromise k)
    (he : (b:ℝ) ≤ QuantumListSchedule.energy s.1) :
    latticeOutput s a b ∈ (sourceHeisenbergPromise k).no := by
  apply QuantumListLattice.value_mem_no _ _
    (by rw [represented_length s hs P hP]; exact hn)
    (represented_nodup s hs P hP) (represented_bounded s hs P hP) hs.2
    (represented_adjacent s hs P hP ha) a b s.1.2.1 hab hp
  rw [represented_length s hs P hP]
  exact he

theorem latticeOutput_polynomialPromise (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e)))
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b) (n k : ℕ) (hsize : n ≤ s.1.1)
    (hpos : ∀ v, ((P.position v).1:ℝ) ≤ (n+1:ℝ)^k ∧
      ((P.position v).2:ℝ) ≤ (n+1:ℝ)^k)
    {L : ℝ} (hL : 0 ≤ L) (hc : (graph s.1 hs).CoefficientBound L)
    (hcoeff : s.1.2.2.length*L ≤ (n+1:ℝ)^k)
    (hgap : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (latticeOutput s a b).PolynomialPromise k := by
  have hbound : ∀ e ∈ erase s.1.2.2, |(e.2.2:ℝ)| ≤ L := by
    intro e he
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hw
    exact hc.2 i
  have h := QuantumListLattice.source_polynomialPromise s.2.1 (erase s.1.2.2)
    (by rw [represented_length s hs P hP]; exact hn)
    (represented_nodup s hs P hP) (represented_bounded s hs P hP) hs.2
    (represented_adjacent s hs P hP ha) a b s.1.2.1 hab n k
    (by rwa [represented_length s hs P hP])
    (by
      intro p hp
      rw [hP.1] at hp
      obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hp
      exact hpos v)
    hL hbound (by simpa only [erase,List.length_map] using hcoeff) hgap
  rwa [← QuantumListLattice.value_source] at h

theorem iterate_count_le (N : ℚ) (s : State) (k : ℕ) :
    s.1.1 ≤ (iterate N k s).1.1 := by
  rw [iterate_state]
  suffices ∀ k, s.1.1 ≤ (QuantumListSchedule.iterate N k s.1).1 from this k
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    change s.1.1 ≤ (QuantumListSchedule.value (N,QuantumListSchedule.iterate N k s.1)).1
    rw [value_count]
    exact ih.trans (Nat.le_add_right _ _)

theorem compiled_lattice_promise {N : ℚ} (hN : 0 < N) (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    {D X Y : ℕ} (hD : ∀ e ∈ s.1.2.2, e.1 ≤ D) (hbox : P.Bounded X Y)
    (hn : 0 < s.1.1) (a b ε : ℚ) (hab : a+ε < b-ε) {k : ℕ}
    (hp : (latticeOutput (iterate N D s) (a+ε) (b-ε)).PolynomialPromise k)
    (herr : (D:ℝ)/(N:ℝ) ≤ (ε:ℝ)) :
    (QuantumListSchedule.energy s.1 ≤ (a:ℝ) →
      latticeOutput (iterate N D s) (a+ε) (b-ε) ∈ (sourceHeisenbergPromise k).yes) ∧
    ((b:ℝ) ≤ QuantumListSchedule.energy s.1 →
      latticeOutput (iterate N D s) (a+ε) (b-ε) ∈ (sourceHeisenbergPromise k).no) := by
  obtain ⟨hs',Q,hQ,_hQbox,hgrid,_hsize,henergy⟩ :=
    compile_realization hN s hs P hP hD hbox
  have hn' : 0 < (iterate N D s).1.1 := hn.trans_le (iterate_count_le N s D)
  constructor
  · intro he
    apply latticeOutput_yes (iterate N D s) hs' Q hQ hgrid hn' (a+ε) (b-ε) hab hp
    have h := (abs_le.mp henergy).2
    push_cast
    linarith
  · intro he
    apply latticeOutput_no (iterate N D s) hs' Q hQ hgrid hn' (a+ε) (b-ε) hab hp
    have h := (abs_le.mp henergy).1
    push_cast
    linarith

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
