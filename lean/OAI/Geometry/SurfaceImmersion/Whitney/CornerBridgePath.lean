import OAI.Geometry.SurfaceImmersion.Whitney.SeparatedCornerBridge

namespace OAI

/-! Turning a separated smooth corner bridge into an embedded replacement
path, retaining finite regular pieces and the exact unchanged trace. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {O : Set M}
namespace LocalCornerBridge

def leftPoint (B : LocalCornerBridge γ t O) : I :=
  ⟨B.left,B.left_pos.le,(B.left_lt.trans B.lt_right |>.trans B.right_lt_one).le⟩
def rightPoint (B : LocalCornerBridge γ t O) : I :=
  ⟨B.right,(B.left_pos.trans B.left_lt |>.trans B.lt_right).le,B.right_lt_one.le⟩

lemma source_eq (B : LocalCornerBridge γ t O) : B.arc.curve B.arc.start = γ B.leftPoint := by
  have he := B.left_germ.eq_of_nhds
  dsimp only [Function.comp_apply] at he
  rw [B.left_value] at he
  exact he.trans (Path.extend_extends' γ B.leftPoint)

lemma target_eq (B : LocalCornerBridge γ t O) : B.arc.curve B.arc.finish = γ B.rightPoint := by
  have he := B.right_germ.eq_of_nhds
  dsimp only [Function.comp_apply] at he
  rw [B.right_value] at he
  exact he.trans (Path.extend_extends' γ B.rightPoint)

def path (B : LocalCornerBridge γ t O) : Path (γ B.leftPoint) (γ B.rightPoint) :=
  B.arc.path.cast B.source_eq.symm B.target_eq.symm

lemma path_injective (B : LocalCornerBridge γ t O) : Function.Injective B.path :=
  B.arc.path_injective

lemma path_range (B : LocalCornerBridge γ t O) :
    range B.path = B.arc.curve '' Icc B.arc.start B.arc.finish := B.arc.path_range

def initialPath (B : LocalCornerBridge γ t O) : Path p (γ B.leftPoint) :=
  (γ.subpath 0 B.leftPoint).cast γ.source.symm rfl

def finalPath (B : LocalCornerBridge γ t O) : Path (γ B.rightPoint) q :=
  (γ.subpath B.rightPoint 1).cast rfl γ.target.symm

def replacement (B : LocalCornerBridge γ t O) : Path p q :=
  (B.initialPath.trans B.path).trans B.finalPath

lemma initialPath_range (B : LocalCornerBridge γ t O) :
    range B.initialPath = γ.extend '' Icc (0:ℝ) B.left := by
  change range (γ.subpath 0 B.leftPoint) = _
  rw [Path.range_subpath,uIcc_of_le (show (0:I) ≤ B.leftPoint from bot_le)]
  apply Subset.antisymm
  · rintro x ⟨u,hu,rfl⟩
    have hu' : (u:ℝ) ∈ Icc (0:ℝ) B.left := ⟨hu.1,hu.2⟩
    exact ⟨u,hu',Path.extend_extends' γ u⟩
  · rintro x ⟨u,hu,rfl⟩
    have huI : u ∈ Icc (0:ℝ) 1 := ⟨hu.1,hu.2.trans B.leftPoint.property.2⟩
    exact ⟨⟨u,huI⟩,⟨hu.1,hu.2⟩,Path.extend_apply γ huI |>.symm⟩

lemma finalPath_range (B : LocalCornerBridge γ t O) :
    range B.finalPath = γ.extend '' Icc B.right (1:ℝ) := by
  change range (γ.subpath B.rightPoint 1) = _
  rw [Path.range_subpath,uIcc_of_le (show B.rightPoint ≤ (1:I) from le_top)]
  apply Subset.antisymm
  · rintro x ⟨u,hu,rfl⟩
    have hu' : (u:ℝ) ∈ Icc B.right (1:ℝ) := ⟨hu.1,hu.2⟩
    exact ⟨u,hu',Path.extend_extends' γ u⟩
  · rintro x ⟨u,hu,rfl⟩
    have huI : u ∈ Icc (0:ℝ) 1 := ⟨B.rightPoint.property.1.trans hu.1,hu.2⟩
    exact ⟨⟨u,huI⟩,⟨hu.1,hu.2⟩,Path.extend_apply γ huI |>.symm⟩

lemma replacement_range (B : LocalCornerBridge γ t O) :
    range B.replacement = (γ.extend '' Icc (0:ℝ) B.left ∪
      B.arc.curve '' Icc B.arc.start B.arc.finish) ∪ γ.extend '' Icc B.right (1:ℝ) := by
  change range ((B.initialPath.trans B.path).trans B.finalPath) = _
  rw [Path.trans_range,Path.trans_range,B.initialPath_range,B.path_range,B.finalPath_range]

lemma replacement_finite_regular (B : LocalCornerBridge γ t O)
    (hγ : FiniteRegularPath planeModel γ) : FiniteRegularPath planeModel B.replacement := by
  exact (((hγ.subpath 0 B.leftPoint).cast γ.source.symm rfl).trans
    ((FiniteRegularPath.arc B.arc).cast B.source_eq.symm B.target_eq.symm)).trans
      ((hγ.subpath B.rightPoint 1).cast rfl γ.target.symm)

end LocalCornerBridge
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
