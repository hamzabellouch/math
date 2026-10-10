import Mathlib
import OAI.Analysis.Conductivity.Branching.EndingJoinElliptic
import OAI.Analysis.Conductivity.Variational.SmoothRankRegularity
import OAI.Analysis.Conductivity.Branching.DelayedEndingRegularity
import OAI.Analysis.Conductivity.Fourier.EndingJoinMiddleModel

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def endingJoinSymmetricTensor (D : Coord3 → Mat3) (hD : ∀ x,(D x).IsSymm)
    (lam k J L K : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨endingJoinTensor D lam k J L K x,endingJoinTensor_symm hD _ _ _ _ _ x⟩

lemma matchedEndingPair_pure {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (x : Coord3) (hx : x 0∈Icc (4:ℝ) 7) :
    matchedEndingPair u lam k J L K x=wallCoordinatePair (pureWallMode 1 lam k) x := by
  rw [wallCoordinatePair_pure,matchedEndingPair]
  split_ifs
  · exact hu x hx.1
  · rw [delayedEndingValue_initial hk hJ x hx.2]

theorem matchedEnding_regularRegion_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hDs : ∀ x,(D x).IsSymm) {s : Fin 3 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J) (hL : 0<L) (hK : 0<K)
    (hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s)
    (hur : ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col)
    {U : Set Coord3} (hU : IsOpen U) (hUpos : U⊆{x : Coord3 | 0<x 0}) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (matchedEndingPair u lam k J L K)
      (endingJoinSymmetricTensor D hDs lam k J L K) U := by
  have he := delayedEnding_regularRegion_ae (lam:=lam) (J:=J) (R:=7) hk.ne' hL hK isOpen_univ
  have hm := endingJoinMiddle_regular_ae s lam J hk.ne'
  filter_upwards [hur,he,hm,ae_coord3_ne 0 6,ae_coord3_ne 0 7] with x hxrank hxe hxm hx6 hx7
  intro hxU
  have hxpos := hUpos hxU
  by_cases ht6 : x 0<6
  · let A : Coord3 → Symmetric3 := fun y => ⟨D y,hDs y⟩
    have hr : x∈regularRegion u A univ :=
      smoothPair_mem_regularRegion hu hD (hxrank ⟨hxpos,ht6⟩) isOpen_univ (mem_univ _)
    apply mem_regularRegion_congr_nhds hr ?_ ?_ hU hxU
    · exact axial_paste_eventually_left (continuous_apply 0) (by linarith : x 0<13/2)
    · filter_upwards [(isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht6] with y hy
      apply Subtype.ext
      exact endingJoinTensor_left _ _ _ _ _ _ _ hy.le
  · have h6 : 6<x 0 := lt_of_le_of_ne (le_of_not_gt ht6) (Ne.symm hx6)
    by_cases ht7 : x 0<7
    · apply mem_regularRegion_congr_nhds hxm ?_ ?_ hU hxU
      · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds h6,
          (isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht7] with y hy6 hy7
        exact matchedEndingPair_pure hk hJ hum y ⟨by linarith,hy7.le⟩
      · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds h6,
          (isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht7] with y hy6 hy7
        apply Subtype.ext
        change endingJoinTensor D lam k J L K y=_
        rw [endingJoinTensor,hDm y ⟨hy6.le,hy7.le⟩,
          delayedEndingTensor_initial y (show k*(y 0-7)<J+2 from
            (mul_neg_of_pos_of_neg hk (by linarith)).trans (by linarith))]
        rfl
    · have h7 : 7<x 0 := lt_of_le_of_ne (le_of_not_gt ht7) (Ne.symm hx7)
      apply mem_regularRegion_congr_nhds (hxe (mem_univ _)) ?_ ?_ hU hxU
      · exact axial_paste_eventually_right (continuous_apply 0) (by linarith : 13/2<x 0)
      · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds h7] with y hy
        apply Subtype.ext
        exact endingJoinTensor_right _ _ _ _ _ _ _ hy.le

end ScalarConductivity

end

end OAI
