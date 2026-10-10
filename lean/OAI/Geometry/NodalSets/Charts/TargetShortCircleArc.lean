import OAI.Geometry.NodalSets.Charts.TargetProductChart

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Jets
open scoped ContDiff Topology
noncomputable section

lemma productChartDomain_iff (p : Manifold5) (a b : ℝ) (z : Coord × ℝ) :
    z ∈ productChartDomain p a b ↔
      WithLp.toLp 2 z.1 ∈ (extChartAt (𝓡 4) p.1).target ∧
      WithLp.toLp 2 (fun _ : Fin 1 ↦ a+b*z.2) ∈ (extChartAt (𝓡 1) p.2).target := by
  have he : modelCoordinateEquiv.symm (z.1,a+b*z.2) =
      (WithLp.toLp 2 z.1, WithLp.toLp 2 (fun _ : Fin 1 ↦ a+b*z.2)) := rfl
  change modelCoordinateEquiv.symm (z.1,a+b*z.2) ∈
    (extChartAt modelWithCorners p).target ↔ _
  rw [he]
  simp [modelWithCorners]
  rfl

lemma exists_short_circle_arc (p : Manifold5) :
    ∃ a b : ℝ, 0 < b ∧ ∀ {K : Set Coord},
      (∀ y ∈ K, WithLp.toLp 2 y ∈ (extChartAt (𝓡 4) p.1).target) →
      K ×ˢ Icc (-1:ℝ) 1 ⊆ productChartDomain p a b := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 1 ↦ ℝ)
  let a := e (extChartAt (𝓡 1) p.2 p.2)
  let V := e.symm ⁻¹' (extChartAt (𝓡 1) p.2).target
  have hV : IsOpen V := (isOpen_extChartAt_target p.2).preimage e.symm.continuous
  have ha : a ∈ V := by simp [V,a]
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ha)
  refine ⟨a,r/2,by positivity,?_⟩
  intro K hK z hz
  rw [productChartDomain_iff]
  refine ⟨hK z.1 hz.1,?_⟩
  have habs : |z.2| ≤ 1 := abs_le.mpr hz.2
  have hin : a+(r/2)*z.2 ∈ V := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have hnorm : |a+(r/2)*z.2-a| = (r/2)*|z.2| := by
      rw [add_sub_cancel_left,abs_mul,abs_of_pos (by positivity : 0 < r/2)]
    rw [hnorm]
    nlinarith
  exact hin

end
end Yau.Target

end OAI
