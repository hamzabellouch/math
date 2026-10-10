import OAI.Geometry.RCD.Metric.CompactHoleBallCover
import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # The finite hole-cover volume estimate

De Philippis--Gigli (2018), Lemma 3.3, with an explicit covering constant.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem hole_ball_volume_cover {n : ℕ} (hn : 0 < n) {A : Set (Euclidean n)}
    (hA : IsOpen A) (hAunit : A ⊆ ball 0 1)
    (hproper : ∃ q ∈ ball (0 : Euclidean n) 1, q ∉ A) {L : ℝ} (hL : 1 ≤ L) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Euclidean n) (r : ι → ℝ),
      (∀ i, 0 < r i ∧ r i < 1 ∧ ball (c i) (r i) ⊆ A ∧
        closedBall (c i) (r i) ⊆ ball 0 1 ∧ (sphere (c i) (r i) ∩ frontier A).Nonempty) ∧
      Pairwise (fun i j => Disjoint (ball (c i) (L*r i)) (ball (c j) (L*r j))) ∧
      volume.real A ≤ (2*(5*L)^n*volume.real (ball (0 : Euclidean n) 1)) * ∑ i, (r i)^n := by
  classical
  by_cases hAe : A=∅
  · subst A
    exact ⟨Empty,inferInstance,Empty.elim,Empty.elim,by simp,by simp,by simp⟩
  have hAfin : volume A ≠ ⊤ := measure_ne_top_of_subset hAunit measure_ball_ne_top
  have hApos : 0 < volume.real A := ENNReal.toReal_pos
    (hA.measure_pos volume (Set.nonempty_iff_ne_empty.mpr hAe)).ne' hAfin
  have hhalf : ENNReal.ofReal (volume.real A/2) < volume A := by
    rw [← ENNReal.ofReal_toReal hAfin]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (half_lt_self hApos)
  obtain ⟨H,hHA,hH,hHmass⟩ := hA.exists_lt_isCompact hhalf
  have hhalfH : volume.real A/2 ≤ volume.real H := by
    have hh := ENNReal.toReal_mono (hH.measure_lt_top.ne) hHmass.le
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact hh
  obtain ⟨ι,hι,c,r,hr,hdisj,hcover⟩ := compact_hole_ball_cover hA hproper hH hHA
    (hHA.trans hAunit) hL
  let := hι
  have hcover_fin : volume (⋃ i, ball (c i) (5*L*r i)) ≠ ⊤ := by
    simpa only [Set.mem_univ, iUnion_true] using
      (measure_biUnion_ne_top (s := (Set.univ : Set ι)) (Set.toFinite _)
        (fun i _ => (measure_ball_ne_top : volume (ball (c i) (5*L*r i)) ≠ ⊤)))
  have hvol : volume.real H ≤ ((5*L)^n*volume.real (ball (0 : Euclidean n) 1)) * ∑ i, (r i)^n := by
    calc
      volume.real H ≤ volume.real (⋃ i, ball (c i) (5*L*r i)) :=
        measureReal_mono hcover hcover_fin
      _ ≤ ∑ i, volume.real (ball (c i) (5*L*r i)) := measureReal_iUnion_fintype_le _
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [euclidean_ball_real hn (c i) (by positivity [hL, (hr i).1]),mul_pow]
        ring
  refine ⟨ι,hι,c,r,hr,hdisj,?_⟩
  nlinarith

end RegularPointCoordinates

end

end OAI
