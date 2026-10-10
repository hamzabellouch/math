import OAI.Combinatorics.Crossing.PolygonalReach

namespace OAI

noncomputable section
namespace Zarankiewicz

def polygonalArcPath (v : ℕ → Plane) : (n : ℕ) → Path (v 0) (v n)
  | 0 => Path.refl (v 0)
  | 1 => Path.segment (v 0) (v 1)
  | n+2 => (polygonalArcPath v (n+1)).trans (Path.segment (v (n+1)) (v (n+2)))

structure PolygonalChain (O : Set Plane) (a b : Plane) where
  pieces : ℕ
  vertices : ℕ → Plane
  first : vertices 0=a
  last : vertices pieces=b
  start_mem : a ∈ O
  inside : ∀ i, i < pieces → segment ℝ (vertices i) (vertices (i+1)) ⊆ O

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

def point (O : Set Plane) (a : Plane) (ha : a ∈ O) : PolygonalChain O a a where
  pieces := 0
  vertices := fun _ => a
  first := rfl
  last := rfl
  start_mem := ha
  inside := by intro i hi; omega

def append (P : PolygonalChain O a b) (c : Plane) (h : segment ℝ b c ⊆ O) : PolygonalChain O a c where
  pieces := P.pieces+1
  vertices := fun i => if i ≤ P.pieces then P.vertices i else c
  first := by simp [P.first]
  last := by simp
  start_mem := P.start_mem
  inside := by
    intro i hi
    by_cases hin : i < P.pieces
    · simpa only [ite_eq_left (show i ≤ P.pieces by omega),ite_eq_left (show i+1 ≤ P.pieces by omega)] using P.inside i hin
    · have he : i=P.pieces := by omega
      subst i
      simpa [P.last] using h

def path (P : PolygonalChain O a b) : Path a b :=
  (polygonalArcPath P.vertices P.pieces).cast P.first.symm P.last.symm

end PolygonalChain

theorem nonempty_polygonalChain_of_reach {O : Set Plane} {a b : Plane}
    (ha : a ∈ O) (h : SegmentReach O a b) : Nonempty (PolygonalChain O a b) := by
  induction h with
  | refl => exact ⟨PolygonalChain.point O a ha⟩
  | @tail b c hab hbc ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.append c hbc⟩

theorem nonempty_polygonalChain_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : Nonempty (PolygonalChain O a b) := by
  exact nonempty_polygonalChain_of_reach (by simpa using hγ 0) (segmentReach_of_path γ O hO hγ)

end Zarankiewicz

end

end OAI
