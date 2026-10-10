import OAI.Combinatorics.ContingencyTables.Machines.CellMinimumProgram

namespace OAI

/-! # Computing every attained cell endpoint

Both scans use the dimensions of the stored margin lists. Each entry is
computed by the binary feasibility search; neither scan enumerates tables.
-/

namespace ContingencyTables.EndpointMatrixProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

abbrev Input := NetworkVertexCode.Input
abbrev RowInput := Input × ℕ
abbrev CellInput := RowInput × ℕ

def context (z : CellInput) : CellLowerTestProgram.Context := (z.1.1,(z.1.2,z.2))
def contextRealizer : Realizer context := pair (composition first first)
  (pair (composition first second) second)
lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_second)

def lowerEntry (z : CellInput) : ℕ := CellMinimumProgram.minimum (context z)
def lowerEntryRealizer : Realizer lowerEntry :=
  composition (f := context) (g := CellMinimumProgram.minimum)
    contextRealizer CellMinimumProgram.minimumRealizer
lemma polynomial_lowerEntry : PolynomialTime lowerEntryRealizer :=
  polynomial_composition polynomial_context CellMinimumProgram.polynomial_minimum

def upperEntry (z : CellInput) : ℕ := CellMaximumProgram.maximum (context z)
def upperEntryRealizer : Realizer upperEntry :=
  composition (f := context) (g := CellMaximumProgram.maximum)
    contextRealizer CellMaximumProgram.maximumRealizer
lemma polynomial_upperEntry : PolynomialTime upperEntryRealizer :=
  polynomial_composition polynomial_context CellMaximumProgram.polynomial_maximum

def columns (z : RowInput) : List ℕ := List.range z.1.1.2.length
def columnsRealizer : Realizer columns :=
  composition (composition (composition (composition first first) second) listLength) range
lemma polynomial_columns : PolynomialTime columnsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1.2).trans
      ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))

def lowerRow (z : RowInput) : List ℕ := (columns z).map (fun j => lowerEntry (z,j))
def lowerRowRealizer : Realizer lowerRow :=
  composition (pair identity columnsRealizer) (mapWith lowerEntryRealizer)
lemma polynomial_lowerRow : PolynomialTime lowerRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_lowerEntry)

def upperRow (z : RowInput) : List ℕ := (columns z).map (fun j => upperEntry (z,j))
def upperRowRealizer : Realizer upperRow :=
  composition (pair identity columnsRealizer) (mapWith upperEntryRealizer)
lemma polynomial_upperRow : PolynomialTime upperRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_upperEntry)

def rows (z : Input) : List ℕ := List.range z.1.1.length
def rowsRealizer : Realizer rows :=
  composition (composition (composition first first) listLength) range
lemma polynomial_rows : PolynomialTime rowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def lowerMatrix (z : Input) : NatMatrix := (rows z).map (fun i => lowerRow (z,i))
def lowerMatrixRealizer : Realizer lowerMatrix :=
  composition (pair identity rowsRealizer) (mapWith lowerRowRealizer)
lemma polynomial_lowerMatrix : PolynomialTime lowerMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rows)
    (polynomial_mapWith polynomial_lowerRow)

def upperMatrix (z : Input) : NatMatrix := (rows z).map (fun i => upperRow (z,i))
def upperMatrixRealizer : Realizer upperMatrix :=
  composition (pair identity rowsRealizer) (mapWith upperRowRealizer)
lemma polynomial_upperMatrix : PolynomialTime upperMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rows)
    (polynomial_mapWith polynomial_upperRow)

def endpoints (z : Input) : NatMatrix × NatMatrix := (lowerMatrix z,upperMatrix z)
def endpointsRealizer : Realizer endpoints := pair lowerMatrixRealizer upperMatrixRealizer
lemma polynomial_endpoints : PolynomialTime endpointsRealizer :=
  polynomial_pair polynomial_lowerMatrix polynomial_upperMatrix

lemma lowerMatrix_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    lowerMatrix (NetworkVertexCode.data r c b) = natCode (fun (i : Fin m) (j : Fin n) =>
      CellMinimumProgram.minimum (NetworkVertexCode.data r c b,(i.val,j.val))) := by
  simp only [lowerMatrix,rows,NetworkVertexCode.data,List.length_ofFn,
    DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  simp only [lowerRow,columns,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn]
  rfl

lemma upperMatrix_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    upperMatrix (NetworkVertexCode.data r c b) = natCode (fun (i : Fin m) (j : Fin n) =>
      CellMaximumProgram.maximum (NetworkVertexCode.data r c b,(i.val,j.val))) := by
  simp only [upperMatrix,rows,NetworkVertexCode.data,List.length_ofFn,
    DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  simp only [upperRow,columns,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn]
  rfl

end ContingencyTables.EndpointMatrixProgram

end OAI
