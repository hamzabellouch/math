import OAI.Computability.Scheduling.EncodingCosts

namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
theorem answerMatrix (d : J → Option ℕ) (hn : Poly s n 1)
    (hd : Poly s (fun j => (d j).getD 0) 1) :
    Poly s (fun j => Uniform.answerMatrix.time (n j) (U j,(M j,d j))) 150011 := by
  have hD : Poly s (fun j => volume (d j)) 1 := by
    apply Poly.of_le (fun j : J => volume_option_le_getD (d j) 0)
    have hv := Poly.volumeNat hd
    poly_auto
  have hS := Poly.volumeSchedule s n (fun j => (d j).getD 0) M hn hd
  have hB := Poly.volumeBest s n n M hn hn
  have hST : Poly s (fun j => Uniform.scheduleMatrix.time (n j) (U j,((d j).getD 0,M j))) 150010 :=
    Poly.reparam (r := 1) (d := 150010) scheduleMatrix
      (fun j => ⟨n j,(U j,((d j).getD 0,M j))⟩) (hn.add hd)
  have hSV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.scheduleMatrix (M j) ((d j).getD 0)).map List.ofFn)) 2 := by
    simpa only [volume_optionFunctionList] using hS
  have hBV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.bestMatrix (M j) (n j)).map (fun a => List.ofFn a.2))) 2 :=
    Poly.of_le (fun j => volume_optionSndFunctionList_le _) hB
  have hBT := bestMatrix s n U M hn
  poly_auto

theorem unaryAnswer (G : ∀ j, Instance (n j)) (d : J → Option ℕ)
    (hn : Poly s n 1) (he : Poly s (fun j => (G j).edges.length) 1)
    (hd : Poly s (fun j => (d j).getD 0) 1) :
    Poly s (fun j => Uniform.unaryAnswer.time (n j) (U j,(G j,d j))) 150011 := by
  have hD : Poly s (fun j => volume (d j)) 1 := by
    apply Poly.of_le (fun j : J => volume_option_le_getD (d j) 0)
    have hv := Poly.volumeNat hd
    poly_auto
  have hG := Poly.volumeInstance G hn he
  have hA := answerMatrix s n U (fun j => closureMatrix (G j) (n j)) d hn hd
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler
namespace Request
def size {n : ℕ} (x : Request n) : ℕ :=
  n+x.graph.edges.length+x.deadline.getD 0+(ThreeMachine.encodeInput x.graph x.deadline).length
end Request
namespace Binary
def vertices (n : ℕ) : List ℕ := (List.range n).map (·+1)
def edges {n : ℕ} (G : Instance n) : List (ℕ × ℕ) := G.edges.map (fun e => (e.1.val,e.2.val))

theorem input_eq {n : ℕ} (G : Instance n) (d : Option ℕ) :
    ThreeMachine.encodeInput G d = encodeHeader d ++
      (ThreeMachine.encodeList ThreeMachine.encodeNat (vertices n) ++
        ThreeMachine.encodeList encodeEdge (edges G)) := by
  rw [ThreeMachine.encodeInput.eq_def,encodeEdges_map]
  cases d <;> simp only [encodeHeader,List.append_assoc,vertices,edges]

theorem readHeader_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    readHeader (ThreeMachine.encodeInput G d) =
      (d,ThreeMachine.encodeList ThreeMachine.encodeNat (vertices n) ++
        ThreeMachine.encodeList encodeEdge (edges G)) := by
  rw [input_eq,readHeader_correct]

theorem readVertices_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    readList readNat (readHeader (ThreeMachine.encodeInput G d)).2 =
      (vertices n, ThreeMachine.encodeList encodeEdge (edges G)) := by
  rw [readHeader_input,readList_correct readNat_encodeNat]

theorem readEdges_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    readList readEdge (readList readNat (readHeader (ThreeMachine.encodeInput G d)).2).2 =
      (edges G, []) := by
  rw [readVertices_input]
  simpa only [List.append_nil] using readList_correct readEdge_correct (edges G) []

theorem readNat_tail_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    (readNat (ThreeMachine.encodeInput G d).tail).1 = d.getD n := by
  rw [input_eq]
  cases d with
  | none =>
    simp only [encodeHeader,List.cons_append,List.nil_append,List.tail_cons,Option.getD_none,
      ThreeMachine.encodeList,List.append_assoc,readNat_encodeNat,List.length_map,List.length_range,vertices]
  | some T =>
    simp only [encodeHeader,List.cons_append,List.tail_cons,readNat_encodeNat,Option.getD_some]

theorem encodeNat_pos (n : ℕ) : 1 ≤ (ThreeMachine.encodeNat n).length := by
  simp only [ThreeMachine.encodeNat,List.length_append,List.length_replicate,List.length_cons]
  omega

theorem length_le_flatMap_encode {α : Type} (enc : α → List Bool) (h : ∀ a, 1 ≤ (enc a).length) (xs : List α) :
    xs.length ≤ (xs.flatMap enc).length := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_cons,List.length_append]
    have := h a
    omega

theorem length_le_encodeList {α : Type} (enc : α → List Bool) (h : ∀ a, 1 ≤ (enc a).length) (xs : List α) :
    xs.length ≤ (ThreeMachine.encodeList enc xs).length := by
  have := length_le_flatMap_encode enc h xs
  simp only [ThreeMachine.encodeList,List.length_append]
  omega

theorem input_length_bounds {n : ℕ} (G : Instance n) (d : Option ℕ) :
    n ≤ (ThreeMachine.encodeInput G d).length ∧ G.edges.length ≤ (ThreeMachine.encodeInput G d).length := by
  have hv := length_le_encodeList ThreeMachine.encodeNat encodeNat_pos (vertices n)
  have he := length_le_encodeList encodeEdge (fun e => by
    have := encodeNat_pos (e.1+1)
    simp only [encodeEdge,List.length_append]
    omega) (edges G)
  have hv' : n ≤ (ThreeMachine.encodeList ThreeMachine.encodeNat (vertices n)).length := by
    simpa only [vertices,List.length_map,List.length_range] using hv
  have he' : G.edges.length ≤ (ThreeMachine.encodeList encodeEdge (edges G)).length := by
    simpa only [edges,List.length_map] using he
  rw [input_eq]
  simp only [List.length_append]
  omega
end Binary

theorem requestSize_le {n : ℕ} (x : Request n) (hd : x.deadline.getD 0 ≤ n) :
    x.size ≤ 4*(ThreeMachine.encodeInput x.graph x.deadline).length := by
  have h := Binary.input_length_bounds x.graph x.deadline
  dsimp [Request.size]
  omega
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace RequestData
abbrev Index := Σ n, Request n
def size (x : Index) := x.2.size
def bits (x : Index) := ThreeMachine.encodeInput x.2.graph x.2.deadline
def vbytes (x : Index) := ThreeMachine.encodeList ThreeMachine.encodeNat (Binary.vertices x.1)
def ebytes (x : Index) := ThreeMachine.encodeList Binary.encodeEdge (Binary.edges x.2.graph)

theorem nPoly : Poly size (fun x => x.1) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,Request.size]; omega

theorem edgesPoly : Poly size (fun x => x.2.graph.edges.length) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,Request.size]; omega

theorem deadlinePoly : Poly size (fun x => x.2.deadline.getD 0) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,Request.size]; omega

theorem bitsPoly : Poly size (fun x => (bits x).length) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,bits,Request.size]; omega

theorem vrestPoly : Poly size (fun x => (vbytes x ++ ebytes x).length) 1 := by
  apply Poly.of_le _ bitsPoly
  intro x
  dsimp [bits,vbytes,ebytes]
  rw [Binary.input_eq]
  simp only [List.length_append]
  omega

theorem ebytesPoly : Poly size (fun x => (ebytes x).length) 1 := by
  apply Poly.of_le _ vrestPoly
  intro x; simp only [List.length_append]; omega

theorem verticesLength : Poly size (fun x => (Binary.vertices x.1).length) 1 := by
  simpa only [Binary.vertices,List.length_map,List.length_range] using nPoly

theorem edgesLength : Poly size (fun x => (Binary.edges x.2.graph).length) 1 := by
  simpa only [Binary.edges,List.length_map] using edgesPoly

theorem verticesBound (x : Index) (a : ℕ) (ha : a ∈ Binary.vertices x.1) : a ≤ x.1 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hk
  omega

theorem edgesBound (x : Index) (a : ℕ × ℕ) (ha : a ∈ Binary.edges x.2.graph) :
    a.1 ≤ x.1 ∧ a.2 ≤ x.1 := by
  obtain ⟨e,_he,rfl⟩ := List.mem_map.mp ha
  exact ⟨Nat.le_of_lt e.1.isLt,Nat.le_of_lt e.2.isLt⟩

theorem volumeDeadline : Poly size (fun x => volume x.2.deadline) 1 := by
  have h : Poly size (fun x => volume (x.2.deadline.getD 0)) 1 := Poly.volumeNat deadlinePoly
  apply Poly.of_le (fun x : Index => volume_option_le_getD x.2.deadline 0)
  poly_auto

theorem volumeVertices : Poly size (fun x => volume (Binary.vertices x.1)) 2 := by
  have hK : Poly size (fun x => 2*x.1+1) 1 := by
    have hn := nPoly
    poly_auto
  apply Poly.volumeList verticesLength hK
  intro x a ha
  rw [volume_nat]
  have := verticesBound x a ha
  omega

theorem volumeEdges : Poly size (fun x => volume (Binary.edges x.2.graph)) 2 := by
  have hK : Poly size (fun x => 4*x.1+3) 1 := by
    have hn := nPoly
    poly_auto
  apply Poly.volumeList edgesLength hK
  intro x a ha
  rw [volume_prod,volume_nat,volume_nat]
  have := edgesBound x a ha
  omega

theorem volumeVrest : Poly size (fun x => volume (vbytes x ++ ebytes x)) 1 := by
  apply Poly.of_le (fun x : Index => volume_boolList_le (vbytes x ++ ebytes x))
  have h := vrestPoly
  poly_auto

theorem volumeEbytes : Poly size (fun x => volume (ebytes x)) 1 := by
  apply Poly.of_le (fun x : Index => volume_boolList_le (ebytes x))
  have h := ebytesPoly
  poly_auto

theorem volumeGraph : Poly size (fun x => volume x.2.graph) 2 :=
  Poly.volumeInstance (fun x => x.2.graph) nPoly edgesPoly

theorem volumeRequest : Poly size (fun x => volume x.2) 1 := by
  change Poly size (fun x => volume (bits x)) 1
  apply Poly.of_le (fun x : Index => volume_boolList_le (bits x))
  have h := bitsPoly
  poly_auto
end RequestData
end ThreeMachine.StackCompiler
end

end OAI
