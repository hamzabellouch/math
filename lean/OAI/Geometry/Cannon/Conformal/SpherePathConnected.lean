import Mathlib
import OAI.Geometry.Cannon.Modulus.Weights
import OAI.Geometry.Cannon.Modulus.PathCellIndices
import OAI.Geometry.Cannon.Energy.StripCrossing

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonCharts

open CannonCells CannonDuality CannonAnnular

lemma sphere_pathConnected : PathConnectedSpace SphereTwo := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank]
  simp

lemma macroFamily_nonempty {X : Type*} [MetricSpace X] [PathConnectedSpace X]
    {d : ℝ} (hd : 0 < d) (hdia : d < diam (univ : Set X)) :
    (macroFamily (X := X) d).Nonempty := by
  have hp : ∃ x y : X, d < dist x y := by
    by_contra hn
    push Not at hn
    exact not_le_of_gt hdia (diam_le_of_forall_dist_le hd.le (fun x _ y _ => hn x y))
  obtain ⟨x,y,hxy⟩ := hp
  let p := PathConnectedSpace.somePath x y
  refine ⟨range p,p,p.continuous,rfl,?_⟩
  exact hxy.le.trans (dist_le_diam_of_mem (isCompact_range p.continuous).isBounded
    ⟨0,p.source⟩ ⟨1,p.target⟩)

theorem sphere_macro_modulus_minimum {X ι : Type*} [MetricSpace X] [Fintype ι]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) (hdia : d < diam (univ : Set X))
    (p : ι → X) (r : ℝ) (hcover : ∀ x, ∃ i, x ∈ ball (p i) (2*r)) :
    0 < modulus (fun i => ball (p i) (2*r)) (macroFamily d) ∧
      ∃ ω : ι → ℝ, MacroscopicAdmissible p r d ω ∧
        (∑ i, (ω i)^2) = modulus (fun i => ball (p i) (2*r)) (macroFamily d) := by
  let : PathConnectedSpace SphereTwo := sphere_pathConnected
  let : PathConnectedSpace X := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let C := fun i => ball (p i) (2*r)
  obtain ⟨hpos,w,hw,he⟩ := modulus_minimum C hcover (macroFamily_nonempty hd hdia)
    (fun A hA => by obtain ⟨p,_,rfl,_⟩ := hA; exact ⟨p 0,⟨0,rfl⟩⟩)
  refine ⟨hpos,(fun i => w i),?_,?_⟩
  · have ha := (admissible_iff C (macroFamily d) w).mp hw
    refine ⟨ha.1,fun u v q hq => ?_⟩
    have hh := ha.2 (range q) ⟨q,q.continuous,rfl,hq⟩
    have hi : indices C (range q) = pathCellIndices p r q := by
      ext i
      simp only [mem_indices,pathCellIndices,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨x,⟨t,rfl⟩,ht⟩
        exact ⟨t,ht⟩
      · rintro ⟨t,ht⟩
        exact ⟨q t,⟨t,rfl⟩,ht⟩
    rw [hi] at hh
    exact hh
  · rw [← he,EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]

end CannonCharts

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
