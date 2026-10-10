import OAI.MeasureTheory.Falconer.Geometry.PointBallCounts
import OAI.MeasureTheory.Falconer.Geometry.DyadicSeparation
import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRegularity

namespace OAI

/-! Actual dyadic parent centers and the original finite fibers over them. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

noncomputable def prefixCenter (Q : DyadicCube 2) (l : Space 2 → CellPath 2)
    (n : ℕ) (x : Space 2) : Space 2 := (Q.descendant ((l x).take n)).center

theorem DyadicCube.center_coordinate_bound (Q : DyadicCube 2) {x : Space 2}
    (hx : x ∈ Q.carrier) (i : Fin 2) : |x i-Q.center i| ≤ Q.side/2 := by
  have hi := hx i
  change |x i-(Q.origin i+Q.side/2)| ≤ Q.side/2
  rw [abs_le]
  constructor <;> linarith

theorem DyadicCube.center_distance_bound (Q : DyadicCube 2) (hQ : 0 ≤ Q.side)
    {x : Space 2} (hx : x ∈ Q.carrier) : dist x Q.center ≤ Q.side := by
  have h := EuclideanSpace.dist_sq_eq x Q.center
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h
  have h0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr
    (Q.center_coordinate_bound hx 0)
  have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr
    (Q.center_coordinate_bound hx 1)
  rw [sq_abs] at h0 h1
  nlinarith [dist_nonneg (x := x) (y := Q.center)]

theorem DyadicCube.center_injective_at_depth (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {n : ℕ} {p q : CellPath 2} (hp : p.length = n) (hq : q.length = n)
    (he : (Q.descendant p).center = (Q.descendant q).center) : p = q := by
  by_contra hne
  have hh := Q.centers_separated hQ hp hq hne
  rw [he,dist_self] at hh
  exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^n)) hh

theorem prefixCenter_near {N n : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) {x : Space 2} (hx : x ∈ P) :
    dist x (prefixCenter Q l n x) ≤ Q.side/(2:ℝ)^n := by
  have hm := descendant_subset_take Q hQ (l x) n (hleaf x hx).2
  have hh := (Q.descendant ((l x).take n)).center_distance_bound
    (Q.descendant_side_pos hQ _).le hm
  have hlen : ((l x).take n).length = n := by
    rw [List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hn]
  simpa only [prefixCenter,Q.descendant_side,hlen] using hh

theorem prefixCenter_fiber {N n : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) {p : CellPath 2} (hp : p ∈ (P.image l).image (List.take n)) :
    (P.filter fun x => prefixCenter Q l n x = (Q.descendant p).center) = pointPrefixFiber P l n p := by
  have hlen (x : Space 2) (hx : x ∈ P) : ((l x).take n).length = n := by
    rw [List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hn]
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  have hplen : p.length = n := he ▸ hlen x hx
  ext z
  simp only [Finset.mem_filter,pointPrefixFiber]
  constructor
  · rintro ⟨hz,heq⟩
    exact ⟨hz,Q.center_injective_at_depth hQ (hlen z hz) hplen heq⟩
  · rintro ⟨hz,heq⟩
    exact ⟨hz,by simp only [prefixCenter,heq]⟩

theorem prefixCenter_separated {N n : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) : FiniteSeparatedAt (Q.side/(2:ℝ)^n) (P.image (prefixCenter Q l n)) := by
  intro x hx y hy hxy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have hlen (z : Space 2) (hz : z ∈ P) : ((l z).take n).length = n := by
    rw [List.length_take,(mem_cubePaths _ _ _).mp (hleaf z hz).1,Nat.min_eq_left hn]
  exact Q.centers_separated hQ (hlen a ha) (hlen b hb)
    (fun he => hxy (congrArg (fun p => (Q.descendant p).center) he))

end Falconer

end OAI
