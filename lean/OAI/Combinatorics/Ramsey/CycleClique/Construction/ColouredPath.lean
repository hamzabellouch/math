import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathRotation
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OAI

/-!
# Starting the coloured-path argument

The first step of manuscript Lemma `clq:coloured-path` is proved by
walk induction: preservation of colour across two steps, together with
one monochromatic edge, makes the colour constant on its component.
-/

namespace CycleClique.Construction
private theorem color_eq_of_walk {V : Type*} {G : SimpleGraph V} (χ : V → Fin 2)
    (htwo : ∀ {u x v}, G.Adj u x → G.Adj x v → χ u = χ v)
    {u v w : V} (p : G.Walk v w) (huv : G.Adj u v) (heq : χ u = χ v) : χ w = χ v := by
  induction p generalizing u with
  | nil => rfl
  | @cons v z w hvz p ih =>
    have hχ : χ v = χ z := heq.symm.trans (htwo huv hvz)
    exact (ih hvz hχ).trans hχ.symm

/-- In a connected nonbipartite graph, any nonconstant two-colouring
has differently coloured vertices sharing a neighbour. -/
theorem differently_colored_common_neighbors {V : Type*} {G : SimpleGraph V}
    (hconnected : G.Connected) (hnonbipartite : ¬ G.IsBipartite)
    (χ : V → Fin 2) (hnonconstant : ∃ u v, χ u ≠ χ v) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ χ y ≠ χ z := by
  classical
  by_contra hnone
  have htwo : ∀ {u x v}, G.Adj u x → G.Adj x v → χ u = χ v := by
    intro u x v hux hxv
    by_contra hχ
    exact hnone ⟨x, u, v, hux.symm, hxv, hχ⟩
  have hproper : ∀ {u v}, G.Adj u v → χ u ≠ χ v := by
    intro u v huv heq
    have hconstant : ∀ w, χ w = χ v := by
      intro w
      obtain ⟨p⟩ := hconnected v w
      exact color_eq_of_walk χ htwo p huv heq
    obtain ⟨a, b, hab⟩ := hnonconstant
    exact hab ((hconstant a).trans (hconstant b).symm)
  exact hnonbipartite ⟨SimpleGraph.Coloring.mk χ hproper⟩

end CycleClique.Construction

end OAI
