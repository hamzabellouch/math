import OAI.Geometry.RCD.Metric.EuclideanHoleBall
import Mathlib.MeasureTheory.Covering.Vitali

namespace OAI

/-! # Finite disjoint dilated balls covering a compact part of an open hole -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

theorem compact_hole_ball_cover {n : ℕ} {A H : Set (Euclidean n)} (hA : IsOpen A)
    (hproper : ∃ q ∈ ball (0 : Euclidean n) 1, q ∉ A)
    (hH : IsCompact H) (hHA : H ⊆ A) (hHunit : H ⊆ ball 0 1)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Euclidean n) (r : ι → ℝ),
      (∀ i, 0 < r i ∧ r i < 1 ∧ ball (c i) (r i) ⊆ A ∧
        closedBall (c i) (r i) ⊆ ball 0 1 ∧ (sphere (c i) (r i) ∩ frontier A).Nonempty) ∧
      Pairwise (fun i j => Disjoint (ball (c i) (L*r i)) (ball (c j) (L*r j))) ∧
      H ⊆ ⋃ i, ball (c i) (5*L*r i) := by
  classical
  have hlocal (x : H) : ∃ (c : Euclidean n) (r : ℝ),
      0 < r ∧ r < 1 ∧ x.1 ∈ ball c r ∧ ball c r ⊆ A ∧
      closedBall c r ⊆ ball 0 1 ∧ (sphere c r ∩ frontier A).Nonempty := by
    obtain ⟨d,hd,hsub⟩ := Metric.isOpen_iff.mp hA x (hHA x.2)
    have hx : ‖(x : Euclidean n)‖ < 1 := by
      simpa only [mem_ball,dist_zero_right] using hHunit x.2
    let t := min (d/2) ((1-‖(x : Euclidean n)‖)/2)
    have ht : 0 < t := lt_min (by positivity) (by positivity)
    have htd : t < d := (min_le_left _ _).trans_lt (half_lt_self hd)
    have hroom : ‖(x : Euclidean n)‖+t < 1 := by
      have hh := min_le_right (d/2) ((1-‖(x : Euclidean n)‖)/2)
      change t ≤ (1-‖(x : Euclidean n)‖)/2 at hh
      linarith
    obtain ⟨c,r,hr,hr1,hinc,hA',hunit,hcontact⟩ := euclidean_hole_ball hA hproper ht hroom
      ((closedBall_subset_ball htd).trans hsub)
    exact ⟨c,r,hr,hr1,hinc (mem_ball_self ht),hA',hunit,hcontact⟩
  choose c r hr hr1 hmem hsub hunit hcontact using hlocal
  obtain ⟨I,hI⟩ := hH.elim_finite_subcover (fun x : H => ball (c x) (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion_of_mem ⟨x,hx⟩ (hmem ⟨x,hx⟩))
  obtain ⟨J,hJI,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (I : Set H) c (fun x => L*r x) L (fun x _ =>
      (mul_le_mul_of_nonneg_left (hr1 x).le (zero_le_one.trans hL)).trans_eq (mul_one L))
      5 (by norm_num)
  have hJ : J.Finite := I.finite_toSet.subset hJI
  let ι := J
  let : Fintype ι := hJ.fintype
  refine ⟨ι,inferInstance,(fun i => c i.1),(fun i => r i.1),?_,?_,?_⟩
  · intro i
    exact ⟨hr i.1,hr1 i.1,hsub i.1,hunit i.1,hcontact i.1⟩
  · intro i j hij
    exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  · intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hI hx)
    obtain ⟨j,hj,hball⟩ := hcover i hi
    have hlarge : x ∈ ball (c i) (L*r i) :=
      ball_subset_ball (by nlinarith [hr i]) hxi
    exact mem_iUnion_of_mem ⟨j,hj⟩ (by simpa only [mul_assoc] using hball hlarge)

end RegularPointCoordinates

end

end OAI
