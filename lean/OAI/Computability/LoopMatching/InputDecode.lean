import OAI.Computability.LoopMatching.InputMachine

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode

abbrev LoopBits := List Bool × List Bool
abbrev BitsData := List Bool × (List Parse.RecordBits × List LoopBits)

def loopBitsRepr (r : LoopRecord) : LoopBits := (r.vertex.bits,r.multiplicity.bits)
def bitsRepr (G : LoopMatching.Input) : BitsData :=
  (G.n.bits,(G.ordinary.records.map Parse.recordRepr,G.loops.map loopBitsRepr))

def supportBound (z : BitsData) : ℕ := 2*z.2.1.length+z.2.2.length

def decodeLoop (b : ℕ) (r : LoopBits) : LoopData := (Parse.boundedValue b r.1,r.2)

def decode (z : BitsData) : Data :=
  let b := supportBound z+1
  (Parse.boundedValue b z.1,
    (z.2.1.map (Raw.InputData.decodeRecord b),z.2.2.map (decodeLoop b)))

@[fun_prop] theorem decodeLoop_poly : Poly (fun z : ℕ × LoopBits => decodeLoop z.1 z.2) := by
  unfold decodeLoop
  fun_prop

@[fun_prop] theorem decode_poly : Poly decode := by
  have hr := Poly.mapWith (fun z : BitsData => z.2.1)
    (fun z : BitsData × Parse.RecordBits => Raw.InputData.decodeRecord (supportBound z.1+1) z.2)
    (by fun_prop) (by unfold supportBound; fun_prop)
  have hs := Poly.mapWith (fun z : BitsData => z.2.2)
    (fun z : BitsData × LoopBits => decodeLoop (supportBound z.1+1) z.2)
    (by fun_prop) (by unfold supportBound; fun_prop)
  have hn : Poly (fun z : BitsData => Parse.boundedValue (supportBound z+1) z.1) := by
    unfold supportBound
    fun_prop
  exact Poly.pair _ _ hn (Poly.pair _ _ hr hs)

lemma supportBound_repr (G : LoopMatching.Input) :
    supportBound (bitsRepr G) = 2*G.ordinary.records.length+G.loops.length := by
  simp [supportBound,bitsRepr]

lemma decode_n_repr (G : LoopMatching.Input) :
    (decode (bitsRepr G)).1 = min (2*G.ordinary.records.length+G.loops.length+1) G.n := by
  simp [decode,bitsRepr,supportBound,Parse.boundedValue_bits]

lemma decode_lengths (z : BitsData) :
    (decode z).2.1.length=z.2.1.length ∧ (decode z).2.2.length=z.2.2.length := by
  simp [decode]

lemma decode_repr (G : LoopMatching.Input)
    (hn : G.n ≤ 2*G.ordinary.records.length+G.loops.length) :
    decode (bitsRepr G)=repr G := by
  let b := 2*G.ordinary.records.length+G.loops.length+1
  have hb : G.n ≤ b := by dsimp [b]; omega
  have hr : (G.ordinary.records.map Parse.recordRepr).map (Raw.InputData.decodeRecord b) =
      G.ordinary.records.map Raw.InputData.repr := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    exact Raw.InputData.decodeRecord_repr G.ordinary b hb r hr
  have hs : (G.loops.map loopBitsRepr).map (decodeLoop b)=G.loops.map loopRepr := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    have hv := G.valid r hr
    change r.vertex < G.n at hv
    simp only [Function.comp_def,decodeLoop,loopBitsRepr,loopRepr,Parse.boundedValue_bits]
    rw [min_eq_right (by omega : r.vertex ≤ b)]
  unfold decode
  rw [supportBound_repr]
  change (Parse.boundedValue b G.n.bits,
    ((G.ordinary.records.map Parse.recordRepr).map (Raw.InputData.decodeRecord b),
      (G.loops.map loopBitsRepr).map (decodeLoop b))) = _
  rw [Parse.boundedValue_bits,min_eq_right hb,hr,hs]
  rfl

lemma sparse_guard_repr (G : LoopMatching.Input) :
    (2*(decode (bitsRepr G)).2.1.length+(decode (bitsRepr G)).2.2.length <
      (decode (bitsRepr G)).1) ↔
    2*G.ordinary.records.length+G.loops.length < G.n := by
  rw [decode_n_repr]
  simp only [decode,bitsRepr,List.length_map]
  omega

end LoopMatching.InputMachine

end OAI
