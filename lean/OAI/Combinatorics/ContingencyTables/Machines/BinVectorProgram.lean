import OAI.Combinatorics.ContingencyTables.Machines.BinIntervalProgram
import OAI.Combinatorics.ContingencyTables.Machines.DependentWordProgram

namespace OAI

/-! # The executed independent bin-coordinate draws

Each coordinate reserves a width determined by its full range, and
uses only the prefix needed by the selected interval. The implementation
splits one Boolean list and performs binary arithmetic per coordinate.
-/

namespace ContingencyTables.BinVectorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators

/-- The interval input together with accuracy and dimension allowances. -/
abbrev Frame := BinIntervalProgram.Input×(ℕ×ℕ)

def reservedWidth (z : Frame) : ℕ := Nat.clog 2 (z.1.1.2+1)+4*(z.2.1+z.2.2)
def reservedWidthRealizer : Realizer reservedWidth := by
  let rangeR : Realizer (fun z : Frame => z.1.1.2) :=
    composition (composition first first) second
  let binary := composition (composition rangeR successor) ceilLogTwoRealizer
  let accuracy := composition (f := fun z : Frame => (4,z.2.1+z.2.2))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 4) (composition second add)) multiply
  exact composition (f := fun z : Frame =>
    (Nat.clog 2 (z.1.1.2+1),4*(z.2.1+z.2.2)))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair binary accuracy) add
lemma polynomial_reservedWidth : PolynomialTime reservedWidthRealizer := by
  unfold reservedWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_successor) polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 4)
      (polynomial_composition polynomial_second polynomial_add)) polynomial_multiply)) polynomial_add

def activeWidth (z : Frame) : ℕ :=
  Nat.clog 2 (BinIntervalProgram.intervalSize z.1+1)+4*(z.2.1+z.2.2)
def activeWidthRealizer : Realizer activeWidth := by
  let sizeR : Realizer (fun z : Frame => BinIntervalProgram.intervalSize z.1) :=
    composition (f := fun z : Frame => z.1) (g := BinIntervalProgram.intervalSize)
      first BinIntervalProgram.intervalSizeRealizer
  let binary : Realizer (fun z : Frame => Nat.clog 2 (BinIntervalProgram.intervalSize z.1+1)) :=
    composition (composition sizeR successor) ceilLogTwoRealizer
  let accuracy := composition (f := fun z : Frame => (4,z.2.1+z.2.2))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 4) (composition second add)) multiply
  exact composition (f := fun z : Frame =>
    (Nat.clog 2 (BinIntervalProgram.intervalSize z.1+1),4*(z.2.1+z.2.2)))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair binary accuracy) add
lemma polynomial_activeWidth : PolynomialTime activeWidthRealizer := by
  unfold activeWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first BinIntervalProgram.polynomial_intervalSize)
      polynomial_successor) polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 4)
      (polynomial_composition polynomial_second polynomial_add)) polynomial_multiply)) polynomial_add

def coordinate (z : Frame×List Bool) : ℕ :=
  BinIntervalProgram.draw (z.1.1,z.2.take (activeWidth z.1))
def coordinateRealizer : Realizer coordinate :=
  composition (f := fun z : Frame×List Bool => (z.1.1,z.2.take (activeWidth z.1)))
    (g := BinIntervalProgram.draw)
    (pair (composition first first)
      (composition (pair second (composition first activeWidthRealizer)) takeFast))
    BinIntervalProgram.drawRealizer
lemma polynomial_coordinate : PolynomialTime coordinateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_activeWidth)) polynomial_takeFast))
    BinIntervalProgram.polynomial_draw

lemma intervalSize_le (K N beta : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K) :
    CompanionOracleDensity.intervalSize K N beta ≤ N := by
  have he := FairBits.fiber_card hK hN hb
  have hc : (FairBits.fiber K N beta).card ≤ N :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range N)
  simpa only [he,CompanionOracleDensity.intervalSize] using hc

lemma active_le_reserved (K N beta h d : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K) :
    activeWidth (((K,N),beta),(h,d)) ≤ reservedWidth (((K,N),beta),(h,d)) := by
  unfold activeWidth reservedWidth
  rw [BinIntervalProgram.intervalSize_eq]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2
    (Nat.add_le_add_right (intervalSize_le K N beta hK hN hb) 1)) _

lemma take_ofFn_prefix {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (List.ofFn bits).take k=List.ofFn (FirstSuccess.prefixWord hk bits) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left hk]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,FirstSuccess.prefixWord,Fin.castLE]

theorem coordinate_ofFn (K N beta h d : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K)
    (hsize : 0<CompanionOracleDensity.intervalSize K N beta)
    (bits : Fin (reservedWidth (((K,N),beta),(h,d))) → Bool) :
    coordinate ((((K,N),beta),(h,d)),List.ofFn bits)=
      (CompanionOracleDensity.intervalEquiv K N beta hK hN hb
        (FairBits.scaledBitInteger (CompanionOracleDensity.intervalSize K N beta)
          (activeWidth (((K,N),beta),(h,d))) hsize
          (FirstSuccess.prefixWord (active_le_reserved K N beta h d hK hN hb) bits))).val := by
  unfold coordinate
  rw [take_ofFn_prefix (active_le_reserved K N beta h d hK hN hb)]
  exact BinIntervalProgram.draw_ofFn K N beta _ hK hN hb hsize _

abbrev Input := List Frame×List Bool

def widths (z : Input) : List ℕ := z.1.map reservedWidth
def widthsRealizer : Realizer widths := composition first (map reservedWidthRealizer)
lemma polynomial_widths : PolynomialTime widthsRealizer :=
  polynomial_composition polynomial_first (polynomial_map polynomial_reservedWidth)

def item (z : Input×ℕ) : ℕ := coordinate
  (z.1.1.getD z.2 (((0,0),0),(0,0)),dependentChunk ((widths z.1,z.1.2),z.2))
def itemRealizer : Realizer item :=
  composition (f := fun z : Input×ℕ =>
    (z.1.1.getD z.2 (((0,0),0),(0,0)),dependentChunk ((widths z.1,z.1.2),z.2)))
    (g := coordinate)
    (pair (composition (pair (composition first first) second)
      (getDFast (((0,0),0),(0,0))))
      (composition (pair (pair (composition first widthsRealizer)
        (composition first second)) second) dependentChunkRealizer)) coordinateRealizer
lemma polynomial_item : PolynomialTime itemRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) (polynomial_getDFast (((0,0),0),(0,0))))
    (polynomial_composition (polynomial_pair (polynomial_pair
      (polynomial_composition polynomial_first polynomial_widths)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
      polynomial_dependentChunk)) polynomial_coordinate

def indices (z : Input) : List ℕ := List.range z.1.length
def indicesRealizer : Realizer indices := composition (composition first listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
    Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def output (z : Input) : List ℕ := (indices z).map (fun i => item (z,i))
def outputRealizer : Realizer output :=
  composition (pair identity indicesRealizer) (mapWith itemRealizer)
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_item)

theorem output_ofFn {q : ℕ} (frames : Fin q → Frame)
    (bits : Fin (∑ i,reservedWidth (frames i)) → Bool) :
    output (List.ofFn frames,List.ofFn bits)=
      List.ofFn (fun i => coordinate (frames i,List.ofFn (fun j : Fin (reservedWidth (frames i)) =>
        bits (finSigmaFinEquiv ⟨i,j⟩)))) := by
  have hw : widths (List.ofFn frames,List.ofFn bits)=
      List.ofFn (fun i => reservedWidth (frames i)) := by
    simp only [widths,List.map_ofFn,Function.comp_def]
  apply List.ext_getElem
  · simp only [output,indices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hiq : i<q := by simpa only [List.length_ofFn] using hj
    have hd := dependentChunk_ofFn (fun i => reservedWidth (frames i)) bits (⟨i,hiq⟩ : Fin q)
    simp only [output,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,item,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hiq,dite_true,
      Option.getD_some,hw]
    exact congrArg (fun b => coordinate (frames ⟨i,hiq⟩,b)) hd

end ContingencyTables.BinVectorProgram

end OAI
