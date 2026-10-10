import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInternalRouteSeparation

namespace OAI

/-! Cell-local disjointness extends to the actual translated physical paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaInterior_reverse (l : List (ℕ × ℕ)) :
    (((l.reverse).drop 1).dropLast).toFinset = ((l.drop 1).dropLast).toFinset := by
  simp only [List.drop_one,List.tail_reverse,List.dropLast_reverse,List.tail_dropLast,List.toFinset_reverse]

theorem qmaRoute_path_finset (R : QMACellRoute) : R.path.toFinset = R.body.path.toFinset := by
  rcases R with ⟨b,r⟩
  cases r
  · rfl
  · exact List.toFinset_reverse

theorem qmaRoute_interior_finset (R : QMACellRoute) :
    ((R.path.drop 1).dropLast).toFinset = ((R.body.path.drop 1).dropLast).toFinset := by
  rcases R with ⟨b,r⟩
  cases r
  · rfl
  · exact qmaInterior_reverse b.path

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem internal_bodies_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (p q : ℕ × ℕ) (e f : QMAInternalEdge) (hne : p ≠ q ∨ e ≠ f)
    (he : P.RoutingAllowed (qmaInternalBody p e))
    (hf : P.RoutingAllowed (qmaInternalBody q f)) :
    Disjoint ((((qmaInternalBody p e).path).drop 1).dropLast).toFinset
      (qmaInternalBody q f).path.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  have hz' := List.mem_toFinset.mp hz
  have hw' := List.mem_toFinset.mp hw
  rw [qmaInternalBody_path,← List.map_drop,← List.map_dropLast] at hz'
  rw [qmaInternalBody_path] at hw'
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz'
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp hw'
  have hu' := List.mem_of_mem_drop (List.mem_of_mem_dropLast hu)
  have hh := qmaCellTranslate_unique (qmaInternalPath_bounded e u hu')
    (qmaInternalPath_bounded f v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  have hef : e ≠ f := hne.resolve_left (by intro h; exact h rfl)
  exact Finset.disjoint_left.mp (P.internal_allowed_disjoint havoid p e f hef he hf)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv)

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
