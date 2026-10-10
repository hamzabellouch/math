import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma partialJet_affine (f g : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) (ds : List ι) :
    partialJet (fun x ↦ f x+t*g x) ds =
      fun x ↦ partialJet f ds x+t*partialJet g ds x := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    funext x
    change fderiv ℝ (partialJet (fun y ↦ f y+t*g y) ds) x (Pi.single i 1) = _
    rw [ih, fderiv_fun_add ((partialJet_smooth f hf ds).differentiable (by simp) x)
      ((contDiff_const.mul (partialJet_smooth g hg ds)).differentiable (by simp) x),
      fderiv_const_mul ((partialJet_smooth g hg ds).differentiable (by simp) x)]
    rfl

theorem affine_partialJet_joint_continuous {T : Type*} [TopologicalSpace T]
    (s : T → ℝ) (hs : Continuous s) (f g : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ds : List ι) :
    Continuous (fun z : T × (ι → ℝ) ↦ partialJet (fun x ↦ f x+s z.1*g x) ds z.2) := by
  simp_rw [partialJet_affine f g hf hg]
  exact ((partialJet_smooth f hf ds).continuous.comp continuous_snd).add
    ((hs.comp continuous_fst).mul ((partialJet_smooth g hg ds).continuous.comp continuous_snd))

end
end Yau.Analysis

end OAI
