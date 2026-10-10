import Mathlib
import OAI.Analysis.Conductivity.Branching.AlignedEndingRegularity

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real

lemma endingJoin_overlap {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    {x : Coord3} (hx : x 0∈Icc (6:ℝ) 7) :
    u=ᶠ[𝓝 x] axialPair (delayedEndingValue lam k J L K 7) := by
  have h1 : ∀ᶠ y : Coord3 in 𝓝 x,4<y 0 :=
    (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds (show 4<x 0 by linarith [hx.1])
  have h2 : ∀ᶠ y : Coord3 in 𝓝 x,k*(y 0-7)<1 :=
    (isOpen_lt (continuous_const.mul ((continuous_apply 0).sub continuous_const)) continuous_const).mem_nhds (show k*(x 0-7)<1 by
      have hh := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hx.2)
      linarith)
  filter_upwards [h1,h2] with y hy1 hy2
  rw [hu y hy1.le]
  simp only [axialPair,delayedEndingValue_initial_of_bound hk hJ y hy2.le]

lemma matchedEndingPair_overlap {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ} {x : Coord3}
    (he : u=ᶠ[𝓝 x] axialPair (delayedEndingValue lam k J L K 7)) :
    matchedEndingPair u lam k J L K=ᶠ[𝓝 x] u := by
  filter_upwards [he] with y hy
  dsimp only [matchedEndingPair]
  split_ifs
  · rfl
  · exact hy.symm

lemma matchedEndingPair_left_deriv {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ} {x : Coord3}
    (hx : x 0<13/2) :
    fderiv ℝ (matchedEndingPair u lam k J L K) x=fderiv ℝ u x :=
  (axial_paste_eventually_left (f:=u) (g:=axialPair (delayedEndingValue lam k J L K 7))
    (continuous_apply 0) hx).fderiv_eq

lemma matchedEndingPair_right_deriv {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ} {x : Coord3}
    (hx : 13/2<x 0) :
    fderiv ℝ (matchedEndingPair u lam k J L K) x=fderiv ℝ (axialPair (delayedEndingValue lam k J L K 7)) x :=
  (axial_paste_eventually_right (f:=u) (g:=axialPair (delayedEndingValue lam k J L K 7))
    (continuous_apply 0) hx).fderiv_eq

end ScalarConductivity

end

end OAI
