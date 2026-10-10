import OAI.Combinatorics.Crossing.OrientedSimilarity
import OAI.Combinatorics.Crossing.ParallelDirection
import OAI.Combinatorics.Crossing.CircleParameterChart

namespace OAI

noncomputable section
namespace Zarankiewicz

def similarityCoordinates (o u x : Plane) : Plane :=
  (dot2 u (x-o)/squaredLength u,det2 u (x-o)/squaredLength u)

theorem similarityPoint_coordinates (o u x : Plane) (hu : u ≠ 0) :
    similarityPoint o u (similarityCoordinates o u x)=x := by
  have hL := ne_of_gt (squaredLength_pos u hu)
  change u.1^2+u.2^2 ≠ 0 at hL
  apply Prod.ext <;>
    dsimp [similarityPoint,similarityCoordinates,dot2,det2,rotateQuarter,squaredLength] <;>
    field_simp [hL] <;> ring

theorem similarityCoordinates_point (o u x : Plane) (hu : u ≠ 0) :
    similarityCoordinates o u (similarityPoint o u x)=x := by
  have hL := ne_of_gt (squaredLength_pos u hu)
  change u.1^2+u.2^2 ≠ 0 at hL
  apply Prod.ext <;>
    dsimp [similarityPoint,similarityCoordinates,dot2,det2,rotateQuarter,squaredLength] <;>
    field_simp [hL] <;> ring

theorem similarityCoordinates_length (o u x : Plane) (hu : u ≠ 0) :
    squaredLength (similarityCoordinates o u x)=squaredLength (x-o)/squaredLength u := by
  have hL := ne_of_gt (squaredLength_pos u hu)
  change u.1^2+u.2^2 ≠ 0 at hL
  dsimp [similarityCoordinates,dot2,det2,squaredLength]
  field_simp [hL]
  ring

theorem similarityPoint_cut (o u : Plane) : similarityPoint o u (-1,0)=o-u := by
  apply Prod.ext <;> dsimp [similarityPoint,rotateQuarter] <;> ring

theorem circle_similarity_parameter (o u x : Plane) (hu : u ≠ 0)
    (hx : squaredLength (x-o)=squaredLength u) (hcut : x ≠ o-u) :
    ∃ t : ℝ, similarityPoint o u (circlePoint t)=x := by
  let c := similarityCoordinates o u x
  have hL := ne_of_gt (squaredLength_pos u hu)
  have hc : c.1^2+c.2^2=1 := by
    change squaredLength (similarityCoordinates o u x)=1
    rw [similarityCoordinates_length o u x hu,hx,div_self hL]
  have hcx : c.1 ≠ -1 := by
    intro hh
    have hc2 : c.2=0 := by rw [hh] at hc; nlinarith [sq_nonneg c.2]
    have he : c=(-1,0) := Prod.ext hh hc2
    apply hcut
    calc
      x = similarityPoint o u c := (similarityPoint_coordinates o u x hu).symm
      _ = o-u := by rw [he,similarityPoint_cut]
  refine ⟨c.2/(1+c.1),?_⟩
  rw [circlePoint_surjective_away_cut c hc hcx]
  exact similarityPoint_coordinates o u x hu

end Zarankiewicz

end

end OAI
