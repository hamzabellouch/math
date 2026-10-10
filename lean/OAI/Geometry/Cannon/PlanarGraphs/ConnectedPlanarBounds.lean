import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Support
import OAI.Geometry.Cannon.PlaneTopology.FreeArcDeleteConnected

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
noncomputable section
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem connected_planar_bounds (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hconn : IsPreconnected (support F Finset.univ)) (hcard : 3≤Nat.card ι) :
    Fintype.card ι+6≤3*(vertices F Finset.univ).card ∧
      faces F Finset.univ+4≤2*(vertices F Finset.univ).card := by
  let _ : Finite (Faces F) := face_finite F hF Q hQ
  let _ := Fintype.ofFinite (Faces F)
  have h3 : 3*Nat.card (Faces F)≤2*Nat.card ι := by
    calc
      _=∑ _ : Faces F,3 := by simp [Nat.card_eq_fintype_card,mul_comm]
      _≤∑ d : Faces F,Nat.card (regionEdges F ConnectedComponents.mk d) :=
        Finset.sum_le_sum (fun d _ => face_edges_card_three F hF Q hQ hcard d)
      _≤_ := total_face_incidence_le F hF Q hQ
  have hEuler := planar_euler F hF Q hQ hconn
  have hfaces : faces F Finset.univ=Nat.card (Faces F) := by
    unfold faces support Faces
    have he : (⋃ i ∈ (Finset.univ : Finset ι),range (F i))=⋃ i,range (F i) := by simp
    rw [he]
  rw [←hfaces,Nat.card_eq_fintype_card] at h3
  omega
end CannonPlanarEuler

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
