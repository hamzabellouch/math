import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTranslatedInternalSeparation

namespace OAI

/-! The two orientations of the internal-path/external-corridor separation. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem internal_half_disjoint (p : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b : Bool) (he : P.RoutingAllowed (qmaInternalBody p e)) (hb : b = decide (P.IsCrossing p)) :
    Disjoint (((qmaInternalPath e).drop 1).dropLast).toFinset (qmaHalfCorridorPath b a).toFinset := by
  subst b
  rcases e with e | (e | e)
  · have hn : ¬P.IsCrossing p := he.2
    simpa only [qmaInternalPath,hn,decide_false] using qmaCellRay_half e a
  · have hn : ¬P.IsCrossing p := he.1
    simpa only [qmaInternalPath,hn,decide_false] using qmaCellPair_half e a
  · have hp : P.IsCrossing p := he
    simpa only [qmaInternalPath,hp,decide_true] using qmaLocalPatch_half e a

theorem half_internal_disjoint (p : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b : Bool) (he : P.RoutingAllowed (qmaInternalBody p e)) (hb : b = decide (P.IsCrossing p)) :
    Disjoint ((qmaHalfCorridorPath b a).drop 1).toFinset (qmaInternalPath e).toFinset := by
  subst b
  rcases e with e | (e | e)
  · have hn : ¬P.IsCrossing p := he.2
    simpa only [qmaInternalPath,hn,decide_false] using qmaHalfCorridor_ray a e
  · have hn : ¬P.IsCrossing p := he.1
    simpa only [qmaInternalPath,hn,decide_false] using qmaHalfCorridor_pair a e
  · have hp : P.IsCrossing p := he
    simpa only [qmaInternalPath,hp,decide_true] using qmaHalfCorridor_patch a e

theorem internal_halfAt_disjoint (p q : ℕ × ℕ) (e : QMAInternalEdge) (a : Fin 4)
    (b : Bool) (he : P.RoutingAllowed (qmaInternalBody p e)) (hb : b = decide (P.IsCrossing q)) :
    Disjoint ((((qmaInternalBody p e).path).drop 1).dropLast).toFinset
      (qmaHalfPathAt q b a).toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  have hz' := List.mem_toFinset.mp hz
  rw [qmaInternalBody_path,← List.map_drop,← List.map_dropLast] at hz'
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz'
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  have hu' := List.mem_of_mem_drop (List.mem_of_mem_dropLast hu)
  have hh := qmaCellTranslate_unique (qmaInternalPath_bounded e u hu')
    (qmaHalfCorridor_bounded b a v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  exact Finset.disjoint_left.mp (P.internal_half_disjoint p e a b he hb)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv)

theorem halfAt_internal_disjoint (p q : ℕ × ℕ) (a : Fin 4) (b : Bool) (e : QMAInternalEdge)
    (he : P.RoutingAllowed (qmaInternalBody q e)) (hb : b = decide (P.IsCrossing p)) :
    Disjoint ((qmaHalfPathAt p b a).drop 1).toFinset (qmaInternalBody q e).path.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  have hz' := List.mem_toFinset.mp hz
  change z ∈ ((qmaHalfCorridorPath b a).map (qmaCellTranslate p)).drop 1 at hz'
  rw [← List.map_drop] at hz'
  have hw' := List.mem_toFinset.mp hw
  rw [qmaInternalBody_path] at hw'
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz'
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp hw'
  have hh := qmaCellTranslate_unique (qmaHalfCorridor_bounded b a u (List.mem_of_mem_drop hu))
    (qmaInternalPath_bounded e v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  exact Finset.disjoint_left.mp (P.half_internal_disjoint p e a b he hb)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
