import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem clm_derivWithin {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) {f : ℝ → A} {f' : A} {t : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun r => L (f r)) (L f') s t :=
  L.hasFDerivAt.comp_hasDerivWithinAt t h

end

end OAI
