import Mathlib
import OAI.Probability.LogConcave.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace
open MeasureTheory

def directional {d : ℕ} (v : Point d) (f : Point d → ℝ) : Point d → ℝ :=
  fun x => fderiv ℝ f x v

lemma directional_smooth {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Point d) :
    ContDiff ℝ (⊤ : ℕ∞) (directional v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma directional_mul {d : ℕ} {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Point d) :
    directional v (fun x => f x*g x)=fun x => directional v f x*g x+f x*directional v g x := by
  funext x
  unfold directional
  change (fderiv ℝ (f*g) x) v=_
  rw [((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma directional_add {d : ℕ} {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Point d) :
    directional v (fun x => f x+g x)=fun x => directional v f x+directional v g x := by
  funext x
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v) ((hf x).hasFDerivAt.add (hg x).hasFDerivAt).fderiv

lemma directional_neg {d : ℕ} {f : Point d → ℝ} (hf : Differentiable ℝ f) (v : Point d) :
    directional v (fun x => -f x)=fun x => -directional v f x := by
  funext x
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v) ((hf x).hasFDerivAt.neg).fderiv

lemma directional_sum {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀ i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => ∑ i∈s,f i x)=fun x => ∑ i∈s,directional v (f i) x := by
  funext x
  have hh := HasFDerivAt.fun_sum (u:=s) (fun i hi => (hf i hi x).hasFDerivAt)
  simpa only [directional,sum_apply] using
    congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh.fderiv

lemma directional_directional {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v x : Point d) :
    directional u (directional v f) x=(fderiv ℝ (fderiv ℝ f) x u) v := by
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  unfold directional
  rw [fderiv_clm_apply (hdf.differentiable (by norm_num) x) (differentiableAt_const _)]
  simp

lemma directional_commute {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v : Point d) :
    directional u (directional v f)=directional v (directional u f) := by
  funext x
  rw [directional_directional hf,directional_directional hf]
  exact ((hf.contDiffAt (x:=x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))).eq u v

lemma directional_gradient {d : ℕ} (H : Point d → ℝ) (v x : Point d) :
    directional v H x=inner ℝ (gradient H x) v := by
  rw [directional,←toDual_gradient,InnerProductSpace.toDual_apply_apply]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
