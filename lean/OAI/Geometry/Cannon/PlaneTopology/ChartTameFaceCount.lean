import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.PullChartUnionCompl

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

namespace CannonEmbeddedArc.Arc
open Set Topology CannonFaceIncidence

variable {ι X D : Type*} [Fintype ι] [Nonempty ι] [TopologicalSpace X] [T2Space X]
  [TopologicalSpace D] [DiscreteTopology D]

theorem chart_tame_face_count (e : ℂ → X) (he : IsOpenEmbedding e) (hden : DenseRange e)
    (F : ι → Arc X) (hrange : ∀ i, range (F i)⊆range e)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, e ⁻¹' range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set X) → D} (hπ : Continuous π)
    (hsur : Function.Surjective π) : Nat.card D≤2*Nat.card ι := by
  let Fc : ι → Arc ℂ := fun i => pullChart e he.isEmbedding (F i) (hrange i)
  have hEq : (⋃ i,range (Fc i))ᶜ=e ⁻¹' (⋃ i,range (F i))ᶜ :=
    pullChart_union_compl e he.isEmbedding F hrange
  let πc := labelPull e hEq π
  have hπc : Continuous πc := labelPull_continuous e he.continuous hEq hπ
  have hFc : Pairwise (fun i j => Compatible (Fc i) (Fc j)) := by
    intro i j hij
    exact pullChart_compatible e he.isEmbedding (F i) (F j) (hrange i) (hrange j) (hF hij)
  have hQc : ∀ i, range (Fc i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    intro i
    rw [show range (Fc i)=e ⁻¹' range (F i) from pullChart_range ..]
    exact hQ i
  exact tame_face_labels_card Fc hFc Q hQc hπc
    (labelPull_surjective e hden hEq
      (isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed)).isOpen_compl hπ hsur)
end CannonEmbeddedArc.Arc

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
