import Mathlib
import OAI.Analysis.Conductivity.Walls.EndingJoinCutoff
import OAI.Analysis.Conductivity.Flux.DelayedPairFlux
import OAI.Analysis.Conductivity.Branching.EndingJoinOverlap

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def matchingFlux (D : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) (x : Coord3) : Coord3 :=
  (D x*gradientColumns (fderiv ℝ u x)).col j

def joinedFlux (D : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (lam k J L K : ℝ) (j : Fin 2) : Coord3 → Coord3 :=
  axialFluxBlend endingJoinCutoff (matchingFlux D u j) (delayedPairFlux lam k J L K 7 j)

lemma endingJoin_constitution_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)]) :
    ∀ᵐ x : Coord3,∀ j : Fin 2,
      (endingJoinTensor D lam k J L K x*gradientColumns
        (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j=joinedFlux D u lam k J L K j x := by
  filter_upwards [delayedPairFlux_constitution_ae (lam:=lam) (R:=7) hk.ne' hJ hL hK] with x hx
  intro j
  by_cases hleft : x 0≤6
  · rw [endingJoinTensor_left _ _ _ _ _ _ _ hleft,
      matchedEndingPair_left_deriv (by linarith : x 0<13/2)]
    unfold joinedFlux axialFluxBlend matchingFlux
    ext i
    simp only [endingJoinCutoff_left hleft,sub_zero,one_mul,zero_mul,add_zero]
  · by_cases hright : 7≤x 0
    · rw [endingJoinTensor_right _ _ _ _ _ _ _ hright,
        matchedEndingPair_right_deriv (by linarith : 13/2<x 0),hx j]
      unfold joinedFlux axialFluxBlend
      ext i
      simp only [endingJoinCutoff_right hright,sub_self,one_mul,zero_mul,zero_add]
    · have he := endingJoin_overlap (L:=L) (K:=K) hk hJ hu (x:=x) ⟨(lt_of_not_ge hleft).le,(lt_of_not_ge hright).le⟩
      rw [(matchedEndingPair_overlap he).fderiv_eq]
      have hg : (delayedEndingTensor lam k J L K 7 x*gradientColumns (fderiv ℝ u x)).col j=
          delayedPairFlux lam k J L K 7 j x := by
        rw [he.fderiv_eq]
        exact hx j
      unfold endingJoinTensor joinedFlux axialFluxBlend matchingFlux
      rw [Matrix.add_mul,Matrix.smul_mul,Matrix.smul_mul]
      ext i
      change (1-endingJoinCutoff (x 0))*(D x*gradientColumns (fderiv ℝ u x)).col j i+
        endingJoinCutoff (x 0)*(delayedEndingTensor lam k J L K 7 x*gradientColumns (fderiv ℝ u x)).col j i=_
      rw [hg]

lemma endingJoin_normal_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    {s : Fin 3 → ℝ} {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hD : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s) :
    ∀ᵐ x : Coord3,∀ j : Fin 2,
      deriv endingJoinCutoff (x 0)=0 ∨ matchingFlux D u j x 0=delayedPairFlux lam k J L K 7 j x 0 := by
  filter_upwards [delayedPairFlux_constitution_ae (lam:=lam) (R:=7) hk.ne' hJ hL hK] with x hx
  intro j
  by_cases hb : x 0∈Icc (6:ℝ) 7
  · right
    have he := endingJoin_overlap (L:=L) (K:=K) hk hJ hu hb
    rw [←hx j,matchingFlux,hD x hb,matrix_product_col_eq_mulVec,matrix_product_col_eq_mulVec,
      normal_flux_of_symm (flatBackgroundTensor_symm s) (flatBackgroundTensor_normal s)]
    rw [show delayedEndingTensor lam k J L K 7 x=alignedEndingTensor lam k J L K (x-Pi.single 0 7) from rfl,
      normal_flux_of_symm (alignedEndingTensor_symm _ _ _ _ _ _) (alignedEndingTensor_normal _ _ _ _ _ _),he.fderiv_eq]
  · exact Or.inl (endingJoinCutoff_deriv_zero hb)

end ScalarConductivity

end
end

end OAI
