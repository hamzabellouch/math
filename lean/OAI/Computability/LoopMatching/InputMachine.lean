import OAI.Computability.LoopMatching.ExpandInput
import OAI.Computability.MatchingCount.BinarySolve

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching BinaryMatching.StackCode

abbrev LoopData := ℕ × List Bool
abbrev Data := ℕ × (List Raw.InputData.Rec × List LoopData)

def loopRepr (r : LoopRecord) : LoopData := (r.vertex,r.multiplicity.bits)
def repr (G : LoopMatching.Input) : Data :=
  (G.n,(G.ordinary.records.map Raw.InputData.repr,G.loops.map loopRepr))

def crossBlock (n j : ℕ) (r : LoopData) : List Raw.InputData.Rec :=
  (List.range j).map (fun d => (r.1,(n+d,r.2)))

def cross (n j : ℕ) (rs : List LoopData) : List Raw.InputData.Rec :=
  rs.flatMap (crossBlock n j)

def expanded (z : Data) (j : ℕ) : Raw.InputData.Data :=
  (z.1+j,z.2.1 ++ cross z.1 j z.2.2)

@[fun_prop] theorem crossBlock_poly :
    Poly (fun z : (ℕ × ℕ) × LoopData => crossBlock z.1.1 z.1.2 z.2) := by
  exact Poly.mapWith (fun z : (ℕ × ℕ) × LoopData => List.range z.1.2)
    (fun z : ((ℕ × ℕ) × LoopData) × ℕ =>
      (z.1.2.1,(z.1.1.1+z.2,z.1.2.2))) (by fun_prop) (by fun_prop)

@[fun_prop] theorem cross_poly :
    Poly (fun z : (ℕ × ℕ) × List LoopData => cross z.1.1 z.1.2 z.2) := by
  apply Poly.flatMapWith (fun z : (ℕ × ℕ) × List LoopData => z.2)
    (fun z : ((ℕ × ℕ) × List LoopData) × LoopData =>
      crossBlock z.1.1.1 z.1.1.2 z.2) (by fun_prop)
  exact Poly.comp _ (fun z : ((ℕ × ℕ) × List LoopData) × LoopData =>
    (z.1.1,z.2)) crossBlock_poly (by fun_prop)

@[fun_prop] theorem expanded_poly : Poly (fun z : Data × ℕ => expanded z.1 z.2) := by
  have hc : Poly (fun z : Data × ℕ => cross z.1.1 z.2 z.1.2.2) :=
    Poly.comp _ (fun z : Data × ℕ => ((z.1.1,z.2),z.1.2.2)) cross_poly (by fun_prop)
  unfold expanded
  fun_prop

lemma cross_repr (n j : ℕ) (rs : List LoopRecord) :
    cross n j (rs.map loopRepr) = (crossRecords n j rs).map Raw.InputData.repr := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, cross, List.flatMap_cons, crossRecords, List.map_append]
    rw [← cross, ih]
    simp only [crossBlock, List.map_map]
    rfl

lemma expanded_repr (G : LoopMatching.Input) (j : ℕ) :
    expanded (repr G) j = ((expand G j).n,(expand G j).records.map Raw.InputData.repr) := by
  simp only [expanded, repr, cross_repr, expand, List.map_append]

def call (z : Data) (j : ℕ) : List Bool := Raw.InputData.solve (expanded z j)

@[fun_prop] theorem call_poly : Poly (fun z : Data × ℕ => call z.1 z.2) :=
  Poly.comp Raw.InputData.solve _ Raw.InputData.solve_poly expanded_poly

lemma solve_repr (G : BinaryMatching.Input) :
    Raw.InputData.solve (G.n,G.records.map Raw.InputData.repr) =
      (Raw.InputData.sparseEstimate G).bits := by
  unfold Raw.InputData.solve Raw.InputData.sparseEstimate
  simp only [List.length_map]
  split_ifs
  · rfl
  · exact Raw.InputData.smallSolve_repr G

lemma call_repr (G : LoopMatching.Input) (j : ℕ) :
    call (repr G) j = (Raw.InputData.sparseEstimate (expand G j)).bits := by
  rw [call, expanded_repr, solve_repr]

end LoopMatching.InputMachine

end OAI
