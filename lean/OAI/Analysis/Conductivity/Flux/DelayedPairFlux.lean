import Mathlib
import OAI.Analysis.Conductivity.Flux.AxialFluxBlend

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real

lemma matrix_product_col_eq_mulVec {m n l : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n l ℝ) (j : l) : (A*B).col j=A*ᵥB.col j := rfl

def delayedPairFlux (lam k J L K R : ℝ) (j : Fin 2) (x : Coord3) : Coord3 :=
  if j=0 then Pi.single 0 1 else potentialCurl (delayedEndingPotential lam k J L K R) x

lemma delayedPairFlux_C1 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) :
    ContDiff ℝ 1 (delayedPairFlux lam k J L K R j) := by
  unfold delayedPairFlux
  split_ifs
  · exact contDiff_const
  · exact delayedEndingFlux_C1 hJ hL hK

lemma delayedPairFlux_divergence {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) (x : Coord3) :
    coordinateDivergence (delayedPairFlux lam k J L K R j) x=0 := by
  unfold delayedPairFlux
  split_ifs
  · simp [coordinateDivergence]
  · exact delayedEndingFlux_divergence hJ hL hK x

lemma delayedPairFlux_constitution_ae {lam k J L K R : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3,∀ j : Fin 2,
      (delayedEndingTensor lam k J L K R x*gradientColumns
        (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col j=delayedPairFlux lam k J L K R j x := by
  filter_upwards [delayedEnding_constitution_ae (lam:=lam) (R:=R) hk hJ hL hK] with x hx
  have hd := (delayedEndingValue_C2 (lam:=lam) (k:=k) (R:=R) hJ hL hK).differentiable (by norm_num) x
  intro j
  rw [matrix_product_col_eq_mulVec]
  fin_cases j
  · change delayedEndingTensor lam k J L K R x*ᵥ(gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 0=Pi.single 0 1
    have hh : (gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 0=Pi.single 0 1 := by
      funext i
      simpa only [Pi.single_apply,eq_comm] using axialPair_gradient_zero hd i
    rw [hh]
    exact alignedEndingTensor_normal _ _ _ _ _ _
  · change delayedEndingTensor lam k J L K R x*ᵥ(gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 1=potentialCurl (delayedEndingPotential lam k J L K R) x
    have hh : (gradientColumns (fderiv ℝ (axialPair (delayedEndingValue lam k J L K R)) x)).col 1=
        fun i => direction (Pi.single i 1) (delayedEndingValue lam k J L K R) x :=
      funext (axialPair_gradient_one hd)
    rw [hh]
    exact hx

end ScalarConductivity

end
end

end OAI
