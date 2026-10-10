import Mathlib
import OAI.Geometry.HyperbolicGroups.PermSwitch

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*}

/-- Oriented polygonal side-pairings (darts are individually indexed sides).
`face` turns around each polygon; `edge` pairs sides with opposite orientation.
Vertices are the cycles of `face * edge`, so no abstract vertex incidences or
Euler changes are supplied as hypotheses. -/
structure PictureMap (D : Type*) where
  face : Perm D
  edge : Perm D
  edge_sq : edge * edge = 1
  edge_ne : ∀ d, edge d ≠ d

namespace PictureMap
variable (M : PictureMap D)

def vertex : Perm D := M.face * M.edge

lemma edge_edge (x : D) : M.edge (M.edge x) = x := by
  have h := congrArg (fun p : Perm D => p x) M.edge_sq
  exact h

variable [DecidableEq D]

/-- Crosswise re-pairing of the two specified outgoing sides. All original
face cycles (hence all original corners and their maps) are unchanged. -/
def switch (a b : D) : PictureMap D where
  face := M.face
  edge := swap a b * M.edge * swap a b
  edge_sq := by
    calc
      _ = swap a b * M.edge * (swap a b * swap a b) * M.edge * swap a b := by group
      _ = swap a b * (M.edge * M.edge) * swap a b := by rw [swap_mul_self,mul_one,mul_assoc (swap a b) M.edge M.edge]
      _ = 1 := by rw [M.edge_sq]; simp
  edge_ne := by
    intro d he
    have hh := congrArg (swap a b) he
    have hz : M.edge (swap a b d) = swap a b d := by
      simpa only [mul_apply,swap_apply_self] using hh
    exact M.edge_ne _ hz

@[simp] lemma switch_face (a b : D) : (M.switch a b).face = M.face := rfl

lemma vertex_switch (a b : D) :
    (M.switch a b).vertex =
      M.vertex * swap (M.edge a) (M.edge b) * swap a b := by
  have he : M.edge * swap (M.edge a) (M.edge b) = swap a b * M.edge := by
    rw [mul_swap_eq_swap_mul,M.edge_edge,M.edge_edge]
  simp only [vertex,switch]
  rw [mul_assoc M.face M.edge,he]
  group

section Finite
variable [Fintype D]

def euler : ℤ := cycles M.vertex + cycles M.face - (Fintype.card D : ℤ) / 2

/-- Exact vertex count under the radial switch in the manuscript. The two
far vertices are either joined, or each original link is split. -/
theorem switch_vertices (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b)) :
    cycles (M.switch a b).vertex = cycles M.vertex +
      if M.vertex.SameCycle (M.edge a) (M.edge b) then 2 else 0 := by
  rw [vertex_switch]
  have hn : (M.vertex * swap (M.edge a) (M.edge b)).SameCycle a b :=
    (sameCycle_right_swap_away M.vertex hfar₁ hfar₂).mpr hv
  rw [cycles_split_right _ hab hn]
  by_cases he : M.vertex.SameCycle (M.edge a) (M.edge b)
  · rw [ite_eq_left he,cycles_split_right _ (M.edge.injective.ne hab) he]
    ring
  · rw [ite_eq_right he]
    have hh := cycles_merge_right M.vertex he
    omega

/-- No appeal to a drawing is used for the Euler change; all faces and edges
are retained, while the exact vertex-cycle computation gives the change. -/
theorem switch_euler (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b)) :
    (M.switch a b).euler = M.euler +
      if M.vertex.SameCycle (M.edge a) (M.edge b) then 2 else 0 := by
  simp only [euler,switch_face,M.switch_vertices a b hab hv hfar₁ hfar₂]
  ring

end Finite
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
