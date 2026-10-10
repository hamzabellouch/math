import OAI.Geometry.SurfaceImmersion.Whitney.CornerBridgePath

namespace OAI

/-! A separated corner bridge preserves the embedding of the whole path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {O : Set M}
namespace LocalCornerBridge

theorem replacement_injective (B : LocalCornerBridge γ t O) (hi : Function.Injective γ)
    (hsep : ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico (0:ℝ) B.left ∪ Ioc B.right 1,
      B.arc.curve s ≠ γ.extend u) : Function.Injective B.replacement := by
  have hpi : Function.Injective B.initialPath :=
    injective_subpath γ hi (by intro he; have := congrArg (fun x : I => (x:ℝ)) he; exact B.left_pos.ne' this.symm)
  have hsi : Function.Injective B.finalPath :=
    injective_subpath γ hi (by intro he; have := congrArg (fun x : I => (x:ℝ)) he; exact B.right_lt_one.ne this)
  have hleft : range B.initialPath ∩ range B.path ⊆ {γ B.leftPoint} := by
    rintro z ⟨hz,hz'⟩
    rw [B.initialPath_range] at hz
    rw [B.path_range] at hz'
    obtain ⟨u,hu,rfl⟩ := hz
    obtain ⟨s,hs,he⟩ := hz'
    have hu' : u = B.left := by
      apply le_antisymm hu.2
      apply le_of_not_gt
      intro hult
      exact hsep s hs u (Or.inl ⟨hu.1,hult⟩) he
    subst u
    exact mem_singleton_iff.mpr (Path.extend_apply γ B.leftPoint.property)
  have hjoin : Function.Injective (B.initialPath.trans B.path) :=
    path_trans_injective_of_range B.initialPath B.path hpi B.path_injective hleft
  have hright : range (B.initialPath.trans B.path) ∩ range B.finalPath ⊆ {γ B.rightPoint} := by
    rintro z ⟨hz,hz'⟩
    rw [Path.trans_range,B.initialPath_range,B.path_range] at hz
    rw [B.finalPath_range] at hz'
    obtain ⟨u,hu,rfl⟩ := hz'
    rcases hz with hz | hz
    · obtain ⟨v,hv,hve⟩ := hz
      have hv01 : v ∈ Icc (0:ℝ) 1 := ⟨hv.1,hv.2.trans B.leftPoint.property.2⟩
      have hu01 : u ∈ Icc (0:ℝ) 1 := ⟨B.rightPoint.property.1.trans hu.1,hu.2⟩
      have h := embeddedPath_extend_injOn γ hi hv01 hu01 hve
      have hlr := B.left_lt.trans B.lt_right
      exfalso
      linarith [hv.2,hu.1]
    · obtain ⟨s,hs,he⟩ := hz
      have hu' : u = B.right := by
        apply le_antisymm _ hu.1
        apply le_of_not_gt
        intro hru
        exact hsep s hs u (Or.inr ⟨hru,hu.2⟩) he
      subst u
      exact mem_singleton_iff.mpr (Path.extend_apply γ B.rightPoint.property)
  exact path_trans_injective_of_range (B.initialPath.trans B.path) B.finalPath hjoin hsi hright

end LocalCornerBridge
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
