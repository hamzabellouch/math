import OAI.Combinatorics.Crossing.OffsetVectors
import OAI.Combinatorics.Crossing.SegmentSymmetries

namespace OAI

noncomputable section
namespace Zarankiewicz

def similarityPoint (o u x : Plane) : Plane :=
  o+(u.1*x.1-u.2*x.2,u.2*x.1+u.1*x.2)

theorem similarityPoint_injective (o u : Plane) (hu : u ≠ 0) : Function.Injective (similarityPoint o u) := by
  intro x y he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  dsimp [similarityPoint] at h₁ h₂
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hx : squaredLength u*(x.1-y.1)=0 := by
    dsimp [squaredLength]
    linear_combination u.1*h₁+u.2*h₂
  have hy : squaredLength u*(x.2-y.2)=0 := by
    dsimp [squaredLength]
    linear_combination -u.2*h₁+u.1*h₂
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hs))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hs))

theorem similarityPoint_segment (o u a b : Plane) (t : ℝ) :
    similarityPoint o u (segmentPoint a b t) =
      segmentPoint (similarityPoint o u a) (similarityPoint o u b) t := by
  apply Prod.ext <;> dsimp [similarityPoint,segmentPoint] <;> ring

theorem similarityPoint_det (o u a b c d : Plane) :
    det2 (similarityPoint o u b-similarityPoint o u a)
      (similarityPoint o u d-similarityPoint o u c) = squaredLength u*det2 (b-a) (d-c) := by
  dsimp [similarityPoint,squaredLength,det2]
  ring

theorem segmentsCrossProperly_similarity (o u a b c d : Plane) (hu : u ≠ 0) :
    SegmentsCrossProperly (similarityPoint o u a) (similarityPoint o u b)
      (similarityPoint o u c) (similarityPoint o u d) ↔ SegmentsCrossProperly a b c d := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  unfold SegmentsCrossProperly
  rw [similarityPoint_det,mul_ne_zero_iff]
  simp only [← similarityPoint_segment,(similarityPoint_injective o u hu).eq_iff]
  exact ⟨fun hh => ⟨hh.1.2,hh.2⟩,fun hh => ⟨⟨hs,hh.1⟩,hh.2⟩⟩

theorem segmentCrossingSign_similarity (o u a b c d : Plane) (hu : u ≠ 0) :
    segmentCrossingSign (similarityPoint o u a) (similarityPoint o u b)
      (similarityPoint o u c) (similarityPoint o u d) = segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_similarity o u a b c d hu]
  simp only [similarityPoint_det,mul_pos_iff_of_pos_left (squaredLength_pos u hu)]

end Zarankiewicz

end

end OAI
