import OAI.Geometry.NodalSets.Elliptic.QuadraticFamily
import OAI.Geometry.NodalSets.Elliptic.SpatialJetFamily

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_spatial_fderiv_at (f : P → E → F) (p : P) (x : E)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) :
    ContDiffAt ℝ ∞ (fun z : P × E ↦ fderiv ℝ (f z.1) z.2) (p,x) := by
  have h : ContDiffAt ℝ ∞ (fun z : (P × E) × E ↦ f z.1.1 z.2) ((p,x),x) := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (ContDiffAt.comp (g := Function.uncurry f)
        (f := fun z : (P × E) × E ↦ (z.1.1,z.2)) ((p,x),x) hf
        (contDiffAt_fst.fst.prodMk contDiffAt_snd))
  exact h.fderiv contDiffAt_snd (by simp)

lemma smooth_spatial_iteratedFDeriv_at (f : P → E → F) (p : P) (x : E)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z : P × E ↦ iteratedFDeriv ℝ k (f z.1) z.2) (p,x) := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.contDiffAt.comp (p,x) hf
  | succ k ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F).symm.contDiff.contDiffAt.comp
      (p,x) (smooth_spatial_fderiv_at (fun p x ↦ iteratedFDeriv ℝ k (f p) x) p x ih)

variable [CompleteSpace E]

def inversePulledForm (g : E → E →L[ℝ] E →L[ℝ] ℝ) (p : QuadParam E) (x : E) :
    (E →L[ℝ] ℝ) →L[ℝ] E := ContinuousLinearMap.inverse (pulledForm g p x)

theorem inversePulledForm_smooth_at (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : QuadParam E) (x : E)
    (m : E ≃L[ℝ] E →L[ℝ] ℝ) (hm : pulledForm g p x = m.toContinuousLinearMap) :
    ContDiffAt ℝ ∞ (Function.uncurry (inversePulledForm g)) (p,x) := by
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E))
      (pulledForm g p x) := by
    rw [hm]
    exact contDiffAt_map_inverse m
  exact hi.comp (p,x) (pulledForm_smooth g hg).contDiffAt

variable {T : Type*} [TopologicalSpace T]

theorem inverse_pulled_spatial_jets_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : T → QuadParam E) (hp : Continuous p) (t : T) (x : E)
    (m : E ≃L[ℝ] E →L[ℝ] ℝ) (hm : pulledForm g (p t) x = m.toContinuousLinearMap) (k : ℕ) :
    ContinuousAt (fun z : T × E ↦ iteratedFDeriv ℝ k (inversePulledForm g (p z.1)) z.2) (t,x) :=
  ContinuousAt.comp (x := (t,x))
    (g := fun z : QuadParam E × E ↦ iteratedFDeriv ℝ k (inversePulledForm g z.1) z.2)
    (f := fun z : T × E ↦ (p z.1,z.2))
    (smooth_spatial_iteratedFDeriv_at (inversePulledForm g) (p t) x
      (inversePulledForm_smooth_at g hg (p t) x m hm) k).continuousAt
    ((hp.comp continuous_fst).prodMk continuous_snd).continuousAt

end
end Yau.Geometry

end OAI
