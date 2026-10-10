import OAI.Probability.GammaPassage.EndpointCoarse

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set Finset

lemma gridMesh_scale_bound (m J : ℕ) :
    (2 : ℝ)^m ≤ (2 : ℝ)^(4*J+1)*(gridMesh m J : ℝ) :=
  (div_le_iff₀ (by exact_mod_cast gridMesh_pos m J)).mp (gridMesh_count_ratio m J)

noncomputable def coarseColumnIndices (A : ℝ) (J : ℕ) : Finset ℤ :=
  gridIndexRange ((A+2)*(2 : ℝ)^(4*J+1))

lemma coarse_column_index (A : ℝ) (hA : 0 ≤ A) (m J : ℕ) (X : ℤ)
    (hX : gridMesh m J ∣ X) (hbound : |(X : ℝ)| ≤ (A+2)*(2 : ℝ)^m) :
    ∃ i ∈ coarseColumnIndices A J, X=gridMesh m J*i := by
  obtain ⟨i,hi⟩ := hX
  refine ⟨i,?_,hi⟩
  apply mem_gridIndexRange_of_abs_le
  have hd : (0 : ℝ) < gridMesh m J := by exact_mod_cast gridMesh_pos m J
  have hprod := mul_le_mul_of_nonneg_left (gridMesh_scale_bound m J) (by linarith : 0 ≤ A+2)
  rw [hi,Int.cast_mul,abs_mul,abs_of_pos hd] at hbound
  nlinarith

noncomputable def coarseRegionFactor (A : ℝ) (J : ℕ) : ℝ := (2*A+8)*(2 : ℝ)^(4*J+1)

lemma endpointBox_into_rareFastRegion (b A R : ℝ) (hA : 0 ≤ A) (k m J : ℕ) (X Y : ℤ)
    (hX : |(X : ℝ)| ≤ (A+2)*(2 : ℝ)^m)
    (hspan : (gridMesh m J : ℝ) ≤ ((Y-X : ℤ) : ℝ)) :
    endpointBox b (A+4) R k m ⊆
      rareFastRegion b (coarseRegionFactor A J) (R+1) ((2 : ℝ)^k) (Y-X) (endpointVertex b 0 X) := by
  have hd : (0 : ℝ) < gridMesh m J := by exact_mod_cast gridMesh_pos m J
  have hY : (0 : ℝ) ≤ ((Y-X : ℤ) : ℝ) := hd.le.trans hspan
  have hscale : (2 : ℝ)^m ≤ (2 : ℝ)^(4*J+1)*((Y-X : ℤ) : ℝ) :=
    (gridMesh_scale_bound m J).trans (mul_le_mul_of_nonneg_left hspan (by positivity))
  intro z hz
  have hzabs : |(z.1 : ℝ)-(X : ℝ)| ≤ (2*A+6)*(2 : ℝ)^m :=
    (abs_sub _ _).trans (by linarith [hz.1])
  have habs : |(z.1 : ℝ)-(X : ℝ)| ≤ coarseRegionFactor A J*((Y-X : ℤ) : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ 2*A+8)
    unfold coarseRegionFactor
    have hp : (0 : ℝ) < 2^m := by positivity
    nlinarith
  have hcoord : ((z-endpointVertex b 0 X).1 : ℝ)=(z.1 : ℝ)-(X : ℝ) := by simp [endpointVertex]
  have htrans : transverse b (z-endpointVertex b 0 X)=transverse b z-transverse b (endpointVertex b 0 X) := by
    simp [transverse]; ring
  have ht : |transverse b (endpointVertex b 0 X)| ≤ 1 := by simpa using (endpointVertex_close b 0 X).le
  have hs : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  refine ⟨?_,?_,?_⟩
  · rw [hcoord]
    have hh := (abs_le.mp habs).1
    linarith
  · rw [hcoord]
    have hh := (abs_le.mp habs).2
    nlinarith
  · rw [htrans]
    exact (abs_sub _ _).trans (by linarith [hz.2])

end GammaFPP.CrossingBridge

end OAI
