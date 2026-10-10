import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListBlock

namespace OAI

/-! A literal simultaneous crossing layer: nine bonds and two fresh spins per
crossing, with every scalar correction retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev FamilyInput := Parameters × List Crossing
def familyCode : FamilyInput → List Bool := prodCode parametersCode (listCode crossingCode)
def zeroCrossing : Crossing := ((0,0),(0,0),(0,0))
def indexed (x : ℕ × FamilyInput) : Input :=
  (x.2.1,x.1,(x.2.2.drop x.1).headD zeroCrossing)
def family (x : FamilyInput) : List Bond :=
  ((List.range x.2.length).map (fun i => block (indexed (i,x)))).flatten
def offset (x : Input) : ℚ := QuantumRoutingCode.coefficients (x.1.2,x.2.2.1) 9
def familyOffset (x : FamilyInput) : ℚ := (x.2.map (fun c => offset (x.1,0,c))).sum

noncomputable opaque indexedProgram : Procedure (prodCode unaryCode familyCode) inputCode indexed := by
  let i := Procedure.first unaryCode familyCode
  let x := Procedure.second unaryCode familyCode
  let p := (Procedure.first parametersCode (listCode crossingCode)).comp x
  let cs := (Procedure.second parametersCode (listCode crossingCode)).comp x
  let c := (Procedure.listGet crossingCode zeroCrossing).comp ((Procedure.unaryToBits.comp i).pair cs)
  exact p.pair (i.pair c)
noncomputable opaque familyProgram : Procedure familyCode (listCode bondCode) family := by
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength crossingCode zeroCrossing).comp
    (Procedure.second parametersCode (listCode crossingCode))
  let tab := (Procedure.tabulate (f := fun x i => block (indexed (i,x))) []
    (blockProgram.comp indexedProgram)).comp (n.pair (Procedure.identity familyCode))
  exact (QuantumRawExchange.flattenProgram bondCode zeroBond).comp tab
noncomputable opaque offsetProgram : Procedure inputCode ratCode offset := coefficientsProgram 9
noncomputable opaque familyOffsetProgram : Procedure familyCode ratCode familyOffset := by
  let p := Procedure.first parametersCode crossingCode
  let c := Procedure.second parametersCode crossingCode
  let entry := offsetProgram.comp (p.pair ((Procedure.constant _ unaryCode 0).pair c))
  exact RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := parametersCode) (eb := crossingCode) (ec := ratCode)
      (f := fun p c => offset (p,0,c)) zeroCrossing 0 entry)

theorem family_length (x : FamilyInput) : (family x).length=9*x.2.length := by
  simp only [family,List.length_flatten,List.map_map,Function.comp_def,block_length,
    List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul,Nat.mul_comm]
  norm_cast

theorem indexed_mem (x : FamilyInput) (i : ℕ) (hi : i<x.2.length) :
    (indexed (i,x)).2.2 ∈ x.2 := by
  change ((x.2.drop i).headD zeroCrossing) ∈ x.2
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem family_bounded (x : FamilyInput)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.1) :
    SourceBondLists.bounded (x.1.1+2*x.2.length) (family x) := by
  intro b hb
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  exact block_bounded (indexed (i,x)) x.2.length hi'
    (hs _ (indexed_mem x i hi')) b hb

theorem family_noLoops (x : FamilyInput)
    (hs : ∀ c ∈ x.2, ∀ a, site c.2 a < x.1.1)
    (hinj : ∀ c ∈ x.2, Function.Injective (site c.2)) :
    ∀ e ∈ family x, e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨bs,hbs,he⟩ := List.mem_flatten.mp he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hc := indexed_mem x i (List.mem_range.mp hi)
  exact block_noLoops (indexed (i,x)) (hs _ hc) (hinj _ hc) e he

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
