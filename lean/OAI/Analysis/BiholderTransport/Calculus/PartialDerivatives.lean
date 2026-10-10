import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ContDiffAt.partial_snd_fderiv {f : Q → E → F} {q:Q} {h:E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q,h)) :
    ContDiffAt ℝ ∞ (fun z : Q × E => fderiv ℝ (f z.1) z.2) (q,h) := by
  have H : ContDiffAt ℝ ∞ (Function.uncurry (fun z : Q × E => f z.1)) ((q,h),h) := by
    exact hf.comp ((q,h),h) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact H.fderiv contDiffAt_snd (by simp)

lemma ContDiffAt.partial_snd_fderiv_two {f : Q → E → F} {q:Q} {h:E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q,h)) :
    ContDiffAt ℝ ∞ (fun z : Q × E => fderiv ℝ (fderiv ℝ (f z.1)) z.2) (q,h) := by
  apply ContDiffAt.partial_snd_fderiv (f := fun q => fderiv ℝ (f q))
  exact ContDiffAt.partial_snd_fderiv hf

end WeakMTWTransport

end

end OAI
