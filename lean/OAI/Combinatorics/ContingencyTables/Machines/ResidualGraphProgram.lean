import OAI.Combinatorics.ContingencyTables.Machines.DirectedBFSRuntime
import OAI.Combinatorics.ContingencyTables.Machines.SignedPairProgram
import OAI.Combinatorics.ContingencyTables.Transport.ResidualSearch

namespace OAI

/-! # Binary construction and search of the actual residual graph -/

namespace ContingencyTables.ResidualGraphProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram SignedPairProgram

abbrev NatMatrix := List (List ℕ)
abbrev FlowMatrix := List (List Signed)
abbrev Data := NatMatrix×FlowMatrix
abbrev ArcInput := Data×(ℕ×ℕ)

def matrixIndices (C : NatMatrix) : List ℕ := List.range C.length

def matrixIndicesRealizer : Realizer matrixIndices := composition listLength range

lemma polynomial_matrixIndices : PolynomialTime matrixIndicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength Polynomial.X
  intro C
  simpa only [Function.comp_apply,Polynomial.eval_X] using list_length_le_weight C

def capacityEntry (z : NatMatrix×(ℕ×ℕ)) : ℕ :=
  (z.1.getD z.2.1 []).getD z.2.2 0

def capacityEntryRealizer : Realizer capacityEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast 0)

lemma polynomial_capacityEntry : PolynomialTime capacityEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_first))
    (polynomial_getDFast [])) (polynomial_composition polynomial_second polynomial_second))
    (polynomial_getDFast 0)

def flowEntry (z : FlowMatrix×(ℕ×ℕ)) : Signed :=
  (z.1.getD z.2.1 []).getD z.2.2 (0,0)

def flowEntryRealizer : Realizer flowEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast (0,0))

lemma polynomial_flowEntry : PolynomialTime flowEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_first))
    (polynomial_getDFast [])) (polynomial_composition polynomial_second polynomial_second))
    (polynomial_getDFast (0,0))

def arcData (z : ArcInput) : ℕ×Signed :=
  (capacityEntry (z.1.1,z.2),flowEntry (z.1.2,z.2))

def arcDataRealizer : Realizer arcData :=
  pair (composition (pair (composition first first) second) capacityEntryRealizer)
    (composition (pair (composition first second) second) flowEntryRealizer)

lemma polynomial_arcData : PolynomialTime arcDataRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_capacityEntry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_flowEntry)

def residualValue (z : ℕ×Signed) : ℕ := (z.1+z.2.2)-z.2.1

def residualValueRealizer : Realizer residualValue :=
  composition (pair (composition (pair first (composition second second)) add)
    (composition second first)) subtract

lemma polynomial_residualValue : PolynomialTime residualValueRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_second))
    polynomial_add) (polynomial_composition polynomial_second polynomial_first)) polynomial_subtract

def positive (z : ℕ×Signed) : Bool := decide (z.2.1< z.1+z.2.2)

def positiveRealizer : Realizer positive :=
  composition (pair (composition second first)
    (composition (pair first (composition second second)) add)) less

lemma polynomial_positive : PolynomialTime positiveRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)) polynomial_less

def arc (z : ArcInput) : Bool := positive (arcData z)
def arcRealizer : Realizer arc := composition arcDataRealizer positiveRealizer
lemma polynomial_arc : PolynomialTime arcRealizer :=
  polynomial_composition polynomial_arcData polynomial_positive

def arcRow (z : Data×ℕ) : List Bool :=
  (List.range z.1.1.length).map (fun v=>arc (z.1,(z.2,v)))

def arcRowRealizer : Realizer arcRow :=
  composition
    (f := fun z : Data×ℕ=>(z,List.range z.1.1.length))
    (g := fun z : (Data×ℕ)×List ℕ=>z.2.map (fun v=>arc (z.1.1,(z.1.2,v))))
    (pair identity (composition
      (f := fun z : Data×ℕ=>z.1.1) (g := matrixIndices)
      (composition first first) matrixIndicesRealizer))
    (mapWith (composition
      (f := fun z : (Data×ℕ)×ℕ=>(z.1.1,(z.1.2,z.2))) (g := arc)
      (pair (composition first first) (pair (composition first second) second)) arcRealizer))

lemma polynomial_arcRow : PolynomialTime arcRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_matrixIndices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_arc))

def graph (z : Data) : DirectedBFSCode.Graph :=
  (List.range z.1.length).map (fun u=>arcRow (z,u))

def graphRealizer : Realizer graph :=
  composition
    (f := fun z : Data=>(z,List.range z.1.length))
    (g := fun z : Data×List ℕ=>z.2.map (fun u=>arcRow (z.1,u)))
    (pair identity (composition (f := fun z : Data=>z.1) (g := matrixIndices)
      first matrixIndicesRealizer)) (mapWith arcRowRealizer)

lemma polynomial_graph : PolynomialTime graphRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_matrixIndices))
    (polynomial_mapWith polynomial_arcRow)

def natCode {m n : ℕ} (c : Fin m→Fin n→ℕ) : NatMatrix :=
  List.ofFn (fun u=>List.ofFn (c u))

def flowCode {m n : ℕ} (f : Fin m→Fin n→ℤ) : FlowMatrix :=
  List.ofFn (fun u=>List.ofFn (fun v=>ForestAffineProgram.signedParts (f u v)))

lemma capacityEntry_code {m n : ℕ} (c : Fin m→Fin n→ℕ) (u : Fin m) (v : Fin n) :
    capacityEntry (natCode c,(u.val,v.val))=c u v := by
  simp only [capacityEntry,natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    u.isLt,v.isLt,dite_true,Option.getD_some,Fin.eta]

lemma flowEntry_code {m n : ℕ} (f : Fin m→Fin n→ℤ) (u : Fin m) (v : Fin n) :
    flowEntry (flowCode f,(u.val,v.val))=ForestAffineProgram.signedParts (f u v) := by
  simp only [flowEntry,flowCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    u.isLt,v.isLt,dite_true,Option.getD_some,Fin.eta]

lemma residualValue_correct (c : ℕ) (z : Signed) :
    residualValue (c,z)=((c:ℤ)-SignedPairProgram.value z).toNat := by
  unfold residualValue SignedPairProgram.value
  dsimp only
  omega

lemma positive_correct (c : ℕ) (z : Signed) :
    positive (c,z)=decide (0<(c:ℤ)-SignedPairProgram.value z) := by
  apply Bool.eq_iff_iff.mpr
  change (decide (z.1 < c+z.2)=true) ↔
    (decide (0<(c:ℤ)-SignedPairProgram.value z)=true)
  rw [decide_eq_true_eq,decide_eq_true_eq]
  change z.1 < c+z.2 ↔ 0<(c:ℤ)-((z.1:ℤ)-z.2)
  omega

lemma arc_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (u v : Fin n) :
    arc ((natCode c,flowCode f),(u.val,v.val))=ResidualSearch.edge c f u v := by
  simp only [arc,arcData,capacityEntry_code,flowEntry_code,positive_correct,
    SignedPairProgram.value,ForestAffineProgram.signedParts_sub,ResidualSearch.edge]

lemma graph_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) :
    graph (natCode c,flowCode f)=DirectedBFSCode.graphCode (ResidualSearch.edge c f) := by
  simp only [graph,arcRow,natCode,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,DirectedBFSCode.graphCode]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  exact arc_code c f u v

def search (z : Data×(ℕ×ℕ)) : Option (List ℕ) :=
  DirectedBFSCode.search (graph z.1) z.2.1 z.2.2

def searchRealizer : Realizer search :=
  composition (pair (pair (composition first graphRealizer) (composition second first))
    (composition second second)) DirectedBFSRuntime.searchRealizer

lemma polynomial_search : PolynomialTime searchRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_graph)
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second))
    DirectedBFSRuntime.polynomial_search

lemma search_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (s t : Fin n) :
    search ((natCode c,flowCode f),(s.val,t.val))=
      (ResidualSearch.search c f s t).map (List.map Fin.val) := by
  rw [search,graph_code,DirectedBFSCode.search_code]
  rfl

end ContingencyTables.ResidualGraphProgram

end OAI
