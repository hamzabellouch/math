import Mathlib
import OAI.Computability.VertexCover.Machines.GraphNumber
import OAI.Computability.VertexCover.Machines.BinaryOutput

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
noncomputable section
variable {a b d : ℕ}

def candidates (I : FixedLC a b) (d : ℕ) : List (ℕ × ℕ) :=
  (List.range (count I d * count I d)).map (fun i => (i/count I d,i%count I d))
def edgeValues (I : FixedLC a b) (d : ℕ) (t : ℝ) : List (ℕ × ℕ) :=
  (candidates I d).filter (fun p => test (d := d) t (I,p))

theorem candidates_eq (I : FixedLC a b) (d : ℕ) :
    candidates I d = (List.ofFn fun e : Fin (count I d * count I d) => finProdFinEquiv.symm e).map
      (fun p => (p.1.val,p.2.val)) := by
  apply List.ext_getElem
  · simp [candidates]
  · intro i hi hj
    simp only [candidates,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rfl

theorem edgeValues_eq (I : FixedLC a b) (d : ℕ) (t : ℝ) :
    edgeValues I d t=(explicitGraph I d t).edges.map (fun p => (p.1.val,p.2.val)) := by
  classical
  rw [edgeValues,candidates_eq,List.filter_map]
  change List.map _ (List.filter _ _) = List.map _ (List.filter _ _)
  congr 1
  apply List.filter_congr
  intro p hp
  apply Bool.eq_iff_iff.mpr
  exact (test_correct I t p.1 p.2).trans decide_eq_true_iff.symm

def candidatesPoly (ha : 0<a) (hb : 0<b) (d : ℕ) :
    Poly (FixedLC.code (a := a) (b := b)) (listBits (prodBits natBits natBits)) (fun I => candidates I d) := by
  let c := countPoly (a := a) hb d
  let n := (c.pair c).comp Poly.natMul
  let count := (Poly.fst (FixedLC.code (a := a) (b := b)) natBits).comp c
  let i := Poly.snd (FixedLC.code (a := a) (b := b)) natBits
  let pair := ((i.pair count).comp Poly.natDiv).pair ((i.pair count).comp Poly.natMod)
  exact Poly.tabulate FixedLC.code (prodBits natBits natBits) (FixedLC.one ha hb) (0,0) n pair

def edgeValuesPoly (ha : 0<a) (hb : 0<b) (d : ℕ) (t : ℝ) :
    Poly (FixedLC.code (a := a) (b := b)) (listBits (prodBits natBits natBits)) (fun I => edgeValues I d t) :=
  (((Poly.identity FixedLC.code).pair (candidatesPoly ha hb d)).comp
    (Poly.listFilterWith FixedLC.code (prodBits natBits natBits) (FixedLC.one ha hb) (0,0)
      (testPoly (d := d) ha hb t))).congr (fun _ => rfl)

def endpointPoly : Poly (prodBits natBits natBits) (listBits natBits) (fun p : ℕ × ℕ => [p.1,p.2]) :=
  (((Poly.fst natBits natBits).pair ((Poly.snd natBits natBits).comp (Poly.listSingleton natBits))).comp
    (Poly.listCons natBits)).congr (fun _ => rfl)
def names (I : FixedLC a b) (d : ℕ) (t : ℝ) : List ℕ :=
  [count I d] ++ List.range (count I d) ++ [(edgeValues I d t).length] ++
    (edgeValues I d t).flatMap (fun p => [p.1,p.2])
def namesPoly (ha : 0<a) (hb : 0<b) (d : ℕ) (t : ℝ) :
    Poly (FixedLC.code (a := a) (b := b)) (listBits natBits) (fun I => names I d t) := by
  let n := countPoly (a := a) hb d
  let head := n.comp (Poly.listSingleton natBits)
  let verts := n.comp Poly.range
  let es := edgeValuesPoly ha hb d t
  let ne := ((es.comp (Poly.listLength (prodBits natBits natBits) (0,0))).comp (Poly.listSingleton natBits))
  let ends := es.comp (Poly.listFlatMap (prodBits natBits natBits) natBits (0,0) 0 endpointPoly)
  let one := (head.pair verts).comp (Poly.listAppend natBits 0)
  let two := (one.pair ne).comp (Poly.listAppend natBits 0)
  exact ((two.pair ends).comp (Poly.listAppend natBits 0)).congr (fun _ => rfl)

theorem names_bits (I : FixedLC a b) (d : ℕ) (t : ℝ) :
    (names I d t).flatMap UniqueGames.BinaryEncoding.nameBits = (explicitGraph I d t).bits := by
  rw [names,edgeValues_eq]
  simp only [List.length_map,List.flatMap_map]
  rfl

def outputPoly (ha : 0<a) (hb : 0<b) (d : ℕ) (t : ℝ) :
    Poly (FixedLC.code (a := a) (b := b)) ExplicitGraph.bits (fun I => explicitGraph I d t) :=
  ((namesPoly ha hb d t).comp Poly.nameList).encodeCongr id (fun _ => rfl) (fun I => names_bits I d t)
end
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
