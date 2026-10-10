import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteProgram

namespace OAI

/-! Exact finite route pieces used by one literal subdivision round. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumRouteCode

theorem lookup_range (f : ℕ → Pair) (n i : ℕ) (hi : i<n) :
    lookup ((List.range n).map f) i = f i := by
  unfold lookup
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hi)]
  simp only [List.getElem_map,List.getElem_range,Option.getD_some]

theorem tail_reverse (f : ℕ → Pair) (w : ℕ) :
    (((List.range (2*w+2)).map f).drop 2).reverse =
      (List.range (2*w)).map (fun k => f (2*w+1-k)) := by
  apply List.ext_getElem
  · simp only [List.length_reverse,List.length_drop,List.length_map,List.length_range]
    omega
  · intro i hi hj
    have hi' : i<2*w := by simpa only [List.length_map,List.length_range] using hj
    rw [List.getElem_reverse]
    simp only [List.getElem_drop,List.getElem_map,List.getElem_range,
      List.length_drop,List.length_map,List.length_range]
    congr 1
    omega

theorem freshPoints_range (e : QuantumListSchedule.Entry) (f : ℕ → Pair) (w : ℕ)
    (hw : 0<w) : freshPoints (e,(List.range (2*w+2)).map f) = [f 1,f 2] := by
  simp only [freshPoints,lookup_range f (2*w+2) 1 (by omega),
    lookup_range f (2*w+2) 2 (by omega)]

theorem pathBlock_range (e : QuantumListSchedule.Entry) (f : ℕ → Pair) (w : ℕ)
    (hw : 0<w) : pathBlock (e,(List.range (2*w+2)).map f) =
      [[f 1,f 2],[f 0,f 1],(List.range (2*(w-1)+2)).map (fun k => f (2*w+1-k))] := by
  have hn : 2*(w-1)+2=2*w := by omega
  simp only [pathBlock,lookup_range f (2*w+2) 0 (by omega),
    lookup_range f (2*w+2) 1 (by omega),lookup_range f (2*w+2) 2 (by omega),
    tail_reverse,hn]

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
