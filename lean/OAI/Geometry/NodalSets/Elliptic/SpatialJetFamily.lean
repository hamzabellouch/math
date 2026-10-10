import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_spatial_fderiv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun z : P × E ↦ fderiv ℝ (f z.1) z.2) := by
  have h : ContDiff ℝ ∞ (fun z : (P × E) × E ↦ f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

theorem smooth_spatial_iteratedFDeriv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ContDiff ℝ ∞ (fun z : P × E ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hf
  | succ k ih =>
    have h := smooth_spatial_fderiv (fun p x ↦ iteratedFDeriv ℝ k (f p) x) ih
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F).symm.contDiff.comp h

variable {T : Type*} [TopologicalSpace T]

theorem continuous_spatial_jets_of_smooth_family (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (p : T → P) (hp : Continuous p) (k : ℕ) :
    Continuous (fun z : T × E ↦ iteratedFDeriv ℝ k (f (p z.1)) z.2) :=
  (smooth_spatial_iteratedFDeriv f hf k).continuous.comp
    ((hp.comp continuous_fst).prodMk continuous_snd)

end
end Yau.Geometry

end OAI
