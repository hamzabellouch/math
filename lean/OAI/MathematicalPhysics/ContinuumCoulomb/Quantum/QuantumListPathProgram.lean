import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathScaleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! Literal three-edge output for one selected path subdivision. Fresh spin
labels are assigned in the input list order; both path parities are supported. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev Parameters := ℕ × (Bool × ℚ)
def parametersCode : Parameters → List Bool :=
  prodCode unaryCode (prodCode Procedure.boolCode ratCode)
abbrev Input := Parameters × (ℕ × Bond)
def inputCode : Input → List Bool :=
  prodCode parametersCode (prodCode unaryCode bondCode)

def left (x : Input) : Fin 3 → ℕ :=
  ![x.1.1+2*x.2.1,x.2.2.1,x.2.2.2.1]
def right (x : Input) : Fin 3 → ℕ :=
  ![x.1.1+2*x.2.1+1,x.1.1+2*x.2.1,
    x.1.1+2*x.2.1+(if x.1.2.1 then 0 else 1)]
def coefficient (x : Input) (k : Fin 4) : ℚ :=
  QuantumPathCode.coefficients (x.1.2.1,x.1.2.2,x.2.2.2.2) k
def bond (x : Input) (k : Fin 3) : Bond :=
  (left x k,right x k,coefficient x k.castSucc)
def block (x : Input) : List Bond := List.ofFn (bond x)
def offset (x : Input) : ℚ := coefficient x 3

noncomputable opaque countProgram : Procedure inputCode Nat.bits (fun x => x.1.1) :=
  Procedure.unaryToBits.comp ((Procedure.first unaryCode
    (prodCode Procedure.boolCode ratCode)).comp (Procedure.first _ _))
noncomputable opaque indexProgram : Procedure inputCode Nat.bits (fun x => x.2.1) :=
  Procedure.unaryToBits.comp ((Procedure.first unaryCode bondCode).comp (Procedure.second _ _))
noncomputable opaque sourceProgram : Procedure inputCode bondCode (fun x => x.2.2) :=
  (Procedure.second unaryCode bondCode).comp (Procedure.second _ _)
noncomputable opaque baseProgram : Procedure inputCode Nat.bits (fun x => x.1.1+2*x.2.1) :=
  Procedure.binaryAdd.comp (countProgram.pair
    (Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 2).pair indexProgram)))
noncomputable opaque nextProgram : Procedure inputCode Nat.bits (fun x => x.1.1+2*x.2.1+1) :=
  Procedure.binaryAdd.comp (baseProgram.pair (Procedure.constant inputCode Nat.bits 1))
noncomputable opaque parityProgram : Procedure inputCode Procedure.boolCode (fun x => x.1.2.1) :=
  (Procedure.first Procedure.boolCode ratCode).comp
    ((Procedure.second unaryCode (prodCode Procedure.boolCode ratCode)).comp (Procedure.first _ _))

noncomputable opaque leftProgram (k : Fin 3) : Procedure inputCode Nat.bits (fun x => left x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp sourceProgram
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact (Procedure.first Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp sourceProgram)

noncomputable opaque rightProgram (k : Fin 3) : Procedure inputCode Nat.bits (fun x => right x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact nextProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact (Procedure.conditional parityProgram baseProgram nextProgram).congrFun (by
    intro x
    cases h : x.1.2.1 <;> simp [right,h])

noncomputable opaque coefficientProgram (k : Fin 4) :
    Procedure inputCode ratCode (fun x => coefficient x k) := by
  let r : Procedure inputCode ratCode (fun x => x.1.2.2) :=
    (Procedure.second Procedure.boolCode ratCode).comp
      ((Procedure.second unaryCode (prodCode Procedure.boolCode ratCode)).comp (Procedure.first _ _))
  let j : Procedure inputCode ratCode (fun x => x.2.2.2.2) :=
    (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp sourceProgram)
  exact (QuantumPathCode.coefficientProgram k).comp (parityProgram.pair (r.pair j))

noncomputable opaque bondProgram (k : Fin 3) : Procedure inputCode bondCode (fun x => bond x k) :=
  (leftProgram k).pair ((rightProgram k).pair (coefficientProgram k.castSucc))
noncomputable opaque blockProgram : Procedure inputCode (listCode bondCode) block :=
  QuantumRawExchange.fixedListProgram inputCode bondCode 3 (fun k x => bond x k) bondProgram
noncomputable opaque offsetProgram : Procedure inputCode ratCode offset := coefficientProgram 3

abbrev FamilyInput := Parameters × List Bond
def familyCode : FamilyInput → List Bool := prodCode parametersCode (listCode bondCode)
def indexed (x : ℕ × FamilyInput) : Input :=
  (x.2.1,x.1,(x.2.2.drop x.1).headD zeroBond)
def family (x : FamilyInput) : List Bond :=
  ((List.range x.2.length).map (fun i => block (indexed (i,x)))).flatten
def familyOffset (x : FamilyInput) : ℚ :=
  (x.2.map (fun e => offset (x.1,0,e))).sum

noncomputable opaque indexedProgram :
    Procedure (prodCode unaryCode familyCode) inputCode indexed := by
  let i := Procedure.first unaryCode familyCode
  let x := Procedure.second unaryCode familyCode
  let p := (Procedure.first parametersCode (listCode bondCode)).comp x
  let xs := (Procedure.second parametersCode (listCode bondCode)).comp x
  let b := (Procedure.listGet bondCode zeroBond).comp ((Procedure.unaryToBits.comp i).pair xs)
  exact p.pair (i.pair b)

noncomputable opaque familyProgram : Procedure familyCode (listCode bondCode) family := by
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp
    (Procedure.second parametersCode (listCode bondCode))
  let tab := (Procedure.tabulate (f := fun x i => block (indexed (i,x))) []
    (blockProgram.comp indexedProgram)).comp (n.pair (Procedure.identity familyCode))
  exact (QuantumRawExchange.flattenProgram bondCode zeroBond).comp tab

noncomputable opaque familyOffsetProgram : Procedure familyCode ratCode familyOffset := by
  let p := Procedure.first parametersCode bondCode
  let e := Procedure.second parametersCode bondCode
  let entry := offsetProgram.comp (p.pair ((Procedure.constant _ unaryCode 0).pair e))
  exact RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := parametersCode) (eb := bondCode) (ec := ratCode)
      (f := fun p e => offset (p,0,e)) zeroBond 0 entry)

theorem block_length (x : Input) : (block x).length = 3 := List.length_ofFn

theorem block_bounded (x : Input) (r : ℕ) (hi : x.2.1 < r)
    (hl : x.2.2.1 < x.1.1) (hr : x.2.2.2.1 < x.1.1) :
    SourceBondLists.bounded (x.1.1+r*2) (block x) := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  fin_cases k <;> dsimp [bond,left,right]
  all_goals first | omega | (split_ifs <;> omega)

theorem block_noLoops (x : Input) (hl : x.2.2.1 < x.1.1) (hr : x.2.2.2.1 < x.1.1) :
    ∀ e ∈ block x, e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  fin_cases k <;> dsimp [bond,left,right]
  all_goals omega

theorem indexed_mem (p : Parameters) (xs : List Bond) (i : ℕ) (hi : i < xs.length) :
    (indexed (i,(p,xs))).2.2 ∈ xs := by
  have he : (xs.drop i).headD zeroBond = xs[i] := by
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi]
    rfl
  change (xs.drop i).headD zeroBond ∈ xs
  rw [he]
  exact List.getElem_mem hi

theorem family_bounded (x : FamilyInput) (hb : SourceBondLists.bounded x.1.1 x.2) :
    SourceBondLists.bounded (x.1.1+x.2.length*2) (family x) := by
  intro b hb'
  obtain ⟨bs,hbs,hb'⟩ := List.mem_flatten.mp hb'
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  have hsource := hb _ (indexed_mem x.1 x.2 i hi')
  exact block_bounded (indexed (i,x)) x.2.length hi' hsource.1 hsource.2 b hb'

theorem family_noLoops (x : FamilyInput) (hb : SourceBondLists.bounded x.1.1 x.2) :
    ∀ b ∈ family x, b.1 ≠ b.2.1 := by
  intro b hb'
  obtain ⟨bs,hbs,hb'⟩ := List.mem_flatten.mp hb'
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  have hsource := hb _ (indexed_mem x.1 x.2 i hi')
  exact block_noLoops (indexed (i,x)) hsource.1 hsource.2 b hb'

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
