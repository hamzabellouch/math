import OAI.GroupTheory.Hyperbolic.CayleyPaths

namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- Honest linear filling estimate on *all* lazy Cayley loops, not just original edges. -/
theorem presentation_cochainBound : Discrete.CochainBound (d.presentation hr).cayleyMetric 114 := by
  intro o a x T p
  obtain ⟨w,hw,hlen,hF⟩ := (d.presentation hr).exists_path_word p
  have h := d.liftedForm_loop_bound hr hw o a T
  rw [hF] at h
  have hlen' : (w.length:ℤ) ≤ 3*p.length := by exact_mod_cast hlen
  omega

/-- The constructed finite presentation is word hyperbolic in the literal thin-triangle sense. -/
theorem presentation_wordHyperbolic : WordHyperbolic (d.presentation hr).GroupType := by
  let P := d.presentation hr
  refine ⟨Set.range P.edge,P.generators_finite,P.cayley_connected,10000*(114+1),?_⟩
  intro x y z p q s hp hq hs
  let p' := Discrete.walkPath P.cayley P.cayley_connected p
  let q' := Discrete.walkPath P.cayley P.cayley_connected q
  let s' := Discrete.walkPath P.cayley P.cayley_connected s.reverse
  have hp' : p'.Geodesic := hp
  have hq' : q'.Geodesic := hq
  have hs' : s'.Geodesic := by
    change s.reverse.length = P.cayley.dist x z
    rw [SimpleGraph.Walk.length_reverse,P.cayley.dist_comm]
    exact hs
  have hthin := Discrete.Path.triangleNear_of_cochainBound
    (Discrete.graphMetric_geodesicSpace P.cayley P.cayley_connected)
    (d.presentation_cochainBound hr) hp' hq' hs'
  have hpMem (v : P.GroupType) : p'.Mem v ↔ v ∈ p.support :=
    Discrete.walkPath_mem P.cayley P.cayley_connected p
  have hqMem (v : P.GroupType) : q'.Mem v ↔ v ∈ q.support :=
    Discrete.walkPath_mem P.cayley P.cayley_connected q
  have hsMem (v : P.GroupType) : s'.Mem v ↔ v ∈ s.support := by
    rw [Discrete.walkPath_mem,SimpleGraph.Walk.support_reverse,List.mem_reverse]
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.1 v ((hpMem v).mpr hv)
    exact ⟨w,hw.imp ((hqMem w).mp) ((hsMem w).mp),hd⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.2.1 v ((hqMem v).mpr hv)
    exact ⟨w,hw.imp ((hsMem w).mp) ((hpMem w).mp),hd⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.2.2 v ((hsMem v).mpr hv)
    exact ⟨w,hw.imp ((hpMem w).mp) ((hqMem w).mp),hd⟩

end Release075.MarkedLineData

end OAI
