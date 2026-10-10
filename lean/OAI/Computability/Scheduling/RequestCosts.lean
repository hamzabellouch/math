import OAI.Computability.Scheduling.ListParserCosts

namespace OAI

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type}
def parseVertices : Uniform (fun (_ : I) (bs : List Bool) =>
    Binary.readList Binary.readNat (Binary.readHeader bs).2) :=
  binaryReadHeader.comp (snd.comp binaryReadNat.binaryReadList)
def parseEdges : Uniform (fun (_ : I) (bs : List Bool) =>
    Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader bs).2).2) :=
  parseVertices.comp (snd.comp binaryReadEdge.binaryReadList)
def parseVertexLength : Uniform (fun (_ : I) (bs : List Bool) =>
    (Binary.readList Binary.readNat (Binary.readHeader bs).2).1.length) :=
  parseVertices.comp (fst.comp length)
theorem time_binaryParse (i : I) (bs : List Bool) :
    (binaryParse (I := I)).time i bs =
    (parseVertexLength.pair ((parseEdges.comp fst).pair (binaryReadHeader.comp fst))).time i bs := rfl
theorem time_binaryParse_outer (i : I) (bs : List Bool) :
    (binaryParse (I := I)).time i bs =
      (parseVertexLength (I := I)).time i bs +
      (((parseEdges (I := I)).comp fst).pair ((binaryReadHeader (I := I)).comp fst)).time i bs +
      20*(volume bs + volume ((Binary.readList Binary.readNat (Binary.readHeader bs).2).1.length) +
      volume ((Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader bs).2).2).1,
        (Binary.readHeader bs).1)+1) := by
  rw [time_binaryParse]
  exact time_pair (parseVertexLength (I := I))
    (((parseEdges (I := I)).comp fst).pair ((binaryReadHeader (I := I)).comp fst)) i bs
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem binaryReadHeader (bs : J → List Bool)
    (hb : Poly s (fun j => (bs j).length) 1)
    (hn : Poly s (fun j => (Binary.readNat (bs j).tail).1) 1) :
    Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4 := by
  have hh : Poly s (fun j => volume (bs j).head?) 0 := by
    apply Poly.volumeOption _ (Poly.const s 3)
    intro j b hb; exact volume_bool b
  have htail : Poly s (fun j => (bs j).tail.length) 1 := Poly.lengthTail bs hb
  have hT := binaryReadNat s idx (fun j => (bs j).tail) htail hn
  have hRest : Poly s (fun j => (Binary.readNat (bs j).tail).2.length) 1 := by
    apply Poly.of_le (fun j : J => Binary.readNat_rest_length _)
    exact htail
  poly_auto

theorem parseVertices (bs : J → List Bool)
    (_hb : Poly s (fun j => (bs j).length) 1)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hV : Poly s (fun j => (Uniform.binaryReadNat (I := I)).binaryReadList.time (idx j) (Binary.readHeader (bs j)).2) 4)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2)
    (_hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2) :
    Poly s (fun j => (Uniform.parseVertices (I := I)).time (idx j) (bs j)) 4 := by
  have ht : Poly s (fun j => volume (Binary.readHeader (bs j)).2) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvH
  poly_auto

theorem parseEdges (bs : J → List Bool)
    (_hb : Poly s (fun j => (bs j).length) 1)
    (hV : Poly s (fun j => (Uniform.parseVertices (I := I)).time (idx j) (bs j)) 4)
    (hE : Poly s (fun j => (Uniform.binaryReadEdge (I := I)).binaryReadList.time (idx j)
      (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2) 4)
    (hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2)
    (_hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2) :
    Poly s (fun j => (Uniform.parseEdges (I := I)).time (idx j) (bs j)) 4 := by
  have hvr : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvV
  poly_auto

theorem parseVertexLength (bs : J → List Bool)
    (_hb : Poly s (fun j => (bs j).length) 1)
    (hV : Poly s (fun j => (Uniform.parseVertices (I := I)).time (idx j) (bs j)) 4)
    (hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2) :
    Poly s (fun j => (Uniform.parseVertexLength (I := I)).time (idx j) (bs j)) 4 := by
  have hv : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvV
  have hl := Poly.lengthVolume _ hv
  poly_auto

theorem binaryParseEH (bs : J → List Bool)
    (hBV : Poly s (fun j => volume (bs j)) 1)
    (hPE : Poly s (fun j => (Uniform.parseEdges (I := I)).time (idx j) (bs j)) 4)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2) :
    Poly s (fun j => (((Uniform.parseEdges (I := I)).comp Uniform.fst).pair
      ((Uniform.binaryReadHeader (I := I)).comp Uniform.fst)).time (idx j) (bs j)) 4 := by
  have hh : Poly s (fun j => volume (Binary.readHeader (bs j)).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvH
  have he : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvE
  have hvs : Poly s (fun j => (Uniform.fst (α := fun _ : I => List (ℕ × ℕ)) (β := fun _ : I => List Bool)).time (idx j)
      (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 4 := by
    simp only [Uniform.time_fst]
    exact (hvE.add (Poly.const s 2)).lift (by omega)
  have hhs : Poly s (fun j => (Uniform.fst (α := fun _ : I => Option ℕ) (β := fun _ : I => List Bool)).time (idx j) (Binary.readHeader (bs j))) 4 := by
    simp only [Uniform.time_fst]
    exact (hvH.add (Poly.const s 2)).lift (by omega)
  have hA := Poly.compTimeSame (Uniform.parseEdges (I := I)) Uniform.fst idx bs
    hPE hvs (hvE.lift (by omega))
  have hB := Poly.compTimeSame (Uniform.binaryReadHeader (I := I)) Uniform.fst idx bs
    hH hhs (hvH.lift (by omega))
  exact Poly.pairTimeSame ((Uniform.parseEdges (I := I)).comp Uniform.fst)
    idx bs ((Uniform.binaryReadHeader (I := I)).comp Uniform.fst)
    hA hB (hBV.lift (by omega)) (he.lift (by omega)) (hh.lift (by omega))

theorem binaryParseParts (bs : J → List Bool)
    (hb : Poly s (fun j => (bs j).length) 1)
    (hPL : Poly s (fun j => (Uniform.parseVertexLength (I := I)).time (idx j) (bs j)) 4)
    (hPE : Poly s (fun j => (Uniform.parseEdges (I := I)).time (idx j) (bs j)) 4)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2)
    (hl : Poly s (fun j => (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1.length) 2) :
    Poly s (fun j => (Uniform.binaryParse (I := I)).time (idx j) (bs j)) 4 := by
  have hh : Poly s (fun j => volume (Binary.readHeader (bs j)).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvH
  have he : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvE
  have hBV : Poly s (fun j => volume (bs j)) 1 := by
    apply Poly.of_le (fun j : J => volume_boolList_le (bs j))
    exact ((Poly.const s 4).mul hb).add (Poly.const s 1)
  have hAB := binaryParseEH s idx bs hBV hPE hH hvE hvH
  have hvAB : Poly s (fun j => volume
      ((Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1,
       (Binary.readHeader (bs j)).1)) 2 := Poly.volumeProd (fun j : J =>
      ((Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1,
       (Binary.readHeader (bs j)).1)) he hh
  have hvl : Poly s (fun j => volume ((Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1.length)) 2 := Poly.volumeNat hl
  have hvol := ((hBV.add hvl).add hvAB).add (Poly.const s 1)
  have hpoly := (hPL.add hAB).add ((Poly.const s 20).mul hvol)
  obtain ⟨C,hC⟩ := hpoly
  refine ⟨C,?_⟩
  intro j
  change (Uniform.binaryParse (I := I)).time (idx j) (bs j) ≤ C * (s j + 2)^4
  rw [Uniform.time_binaryParse_outer]
  exact hC j

theorem binaryParse (bs : J → List Bool)
    (hb : Poly s (fun j => (bs j).length) 1)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hV : Poly s (fun j => (Uniform.binaryReadNat (I := I)).binaryReadList.time (idx j) (Binary.readHeader (bs j)).2) 4)
    (hE : Poly s (fun j => (Uniform.binaryReadEdge (I := I)).binaryReadList.time (idx j)
      (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2) 4)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2)
    (hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2)
    (hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2) :
    Poly s (fun j => (Uniform.binaryParse (I := I)).time (idx j) (bs j)) 4 := by
  have hPV := parseVertices s idx bs hb hH hV hvH hvV
  have hPE := parseEdges s idx bs hb hPV hE hvV hvE
  have hPL := parseVertexLength s idx bs hb hPV hvV
  have hl : Poly s (fun j => (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1.length) 2 :=
    Poly.lengthVolume _ (Poly.of_le (fun j => by rw [volume_prod]; omega) hvV)
  exact binaryParseParts s idx bs hb hPL hPE hH hvE hvH hl
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
theorem time_parseRequest (n : ℕ) (x : Request n) :
    parseRequest.time n x = (binaryParse (I := ℕ)).time n (ThreeMachine.encodeInput x.graph x.deadline) := by
  simp only [Uniform.time,parseRequest]
  exact congrArg (binaryParse (I := ℕ)).charge (show enc x = enc (ThreeMachine.encodeInput x.graph x.deadline) from rfl)
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open RequestData

theorem requestHeader : Poly size
    (fun x : Index => (Uniform.binaryReadHeader (I := ℕ)).time x.1 (bits x)) 4 := by
  have hval : Poly size (fun x : Index => (Binary.readNat (bits x).tail).1) 1 := by
    simp only [bits,Binary.readNat_tail_input]
    apply Poly.of_le (fun x : Index => show x.2.deadline.getD x.1 ≤ x.1+x.2.deadline.getD 0 from by
      cases x.2.deadline <;> simp only [Option.getD_none,Option.getD_some] <;> omega)
    exact nPoly.add deadlinePoly
  exact binaryReadHeader size Sigma.fst bits bitsPoly hval

theorem requestVertices : Poly size
    (fun x : Index => (Uniform.binaryReadNat (I := ℕ)).binaryReadList.time x.1 (Binary.readHeader (bits x)).2) 4 := by
  simp only [bits,Binary.readHeader_input]
  exact binaryNatList size Sigma.fst (fun x : Index => Binary.vertices x.1) ebytes
    (fun x => x.1) verticesLength nPoly verticesBound vrestPoly

theorem requestEdges : Poly size
    (fun x : Index => (Uniform.binaryReadEdge (I := ℕ)).binaryReadList.time x.1
      (Binary.readList Binary.readNat (Binary.readHeader (bits x)).2).2) 4 := by
  simp only [bits,Binary.readVertices_input]
  have h := binaryEdgeList size Sigma.fst (fun x : Index => Binary.edges x.2.graph) (fun _ => [])
    (fun x => x.1) edgesLength nPoly edgesBound
    (show Poly size (fun x : Index => (ThreeMachine.encodeList Binary.encodeEdge
      (Binary.edges x.2.graph) ++ []).length) 1 from by simpa only [List.append_nil,ebytes] using ebytesPoly)
  simpa only [List.append_nil] using h

theorem requestBinaryParse : Poly size
    (fun x : Index => (Uniform.binaryParse (I := ℕ)).time x.1 (bits x)) 4 := by
  have hvH : Poly size (fun x : Index => volume (Binary.readHeader (bits x))) 2 := by
    simp only [bits,Binary.readHeader_input]
    have h := volumeDeadline
    have hv := volumeVrest
    dsimp only [vbytes,ebytes] at hv
    poly_auto
  have hvV : Poly size (fun x : Index => volume
      (Binary.readList Binary.readNat (Binary.readHeader (bits x)).2)) 2 := by
    simp only [bits,Binary.readVertices_input]
    have h := volumeVertices
    have hv := volumeEbytes
    dsimp only [ebytes] at hv
    poly_auto
  have hvE : Poly size (fun x : Index => volume
      (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bits x)).2).2)) 2 := by
    simp only [bits,Binary.readEdges_input]
    have h := volumeEdges
    poly_auto
  exact binaryParse size Sigma.fst bits bitsPoly requestHeader requestVertices requestEdges hvH hvV hvE

theorem parseRequest : Poly size (fun x : Index => Uniform.parseRequest.time x.1 x.2) 4 :=
  by simpa only [Uniform.time_parseRequest,RequestData.bits] using requestBinaryParse
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open RequestData

theorem requestAnswer : Poly size (fun x : Index => Uniform.requestAnswer.time x.1 x.2) 150011 := by
  let U (x : Index) : Universe x.1 := Universe.mk ()
  have hParse := parseRequest
  have hRequest := volumeRequest
  have hGraph := volumeGraph
  have hn := nPoly
  have hD := volumeDeadline
  have hAnswer := unaryAnswer size (fun x : Index => x.1) U (fun x => x.2.graph)
    (fun x => x.2.deadline) nPoly edgesPoly deadlinePoly
  have hOut := requestSlotsVolume
  have hEncode := requestEncodeAnswer
  dsimp only [requestSlots] at hOut hEncode
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
