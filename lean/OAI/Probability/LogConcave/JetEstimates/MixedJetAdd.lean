import Mathlib
import OAI.Probability.LogConcave.JetEstimates.NormalizedLaplace

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling.JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*}

lemma mixedJet_add {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) :
    mixedJet v w l k (fun x => f (x.1+x.2)) =
      jet (Sum.elim v w) (l.map Sum.inl++k.map Sum.inr) f 0 := by
  let A : E × E →L[ℝ] E := ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E
  have hh := congrFun (jet_comp_affine hf A 0
    (Sum.elim (fun i => (v i,(0:E))) (fun j => ((0:E),w j)))
    (l.map Sum.inl++k.map Sum.inr)) 0
  have hdir : (fun i => A (Sum.elim (fun i => (v i,(0:E)))
      (fun j => ((0:E),w j)) i))=Sum.elim v w := by
    funext i
    cases i <;> simp [A]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E => f (x.1+x.2)) :=
    hf.comp (contDiff_fst.add contDiff_snd)
  rw [mixedJet_eq_joint hs]
  rw [hdir] at hh
  simpa [A] using hh

end LogConcaveSampling.JetCalculus

namespace LogConcaveSampling.JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

lemma dir_dir {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w : E) :
    dir v (dir w f)=dir w (dir v f) := by
  funext x
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : Differentiable ℝ (fderiv ℝ f) := hs.differentiable (by simp)
  change (fderiv ℝ (fun y => fderiv ℝ f y w) x) v =
    (fderiv ℝ (fun y => fderiv ℝ f y v) x) w
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _),
    fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.map_zero,zero_add,
    ContinuousLinearMap.flip_apply,fderiv_const_apply] using
    ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))).eq v w

lemma jet_perm {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) {l k : List ι} (hp : l.Perm k) : jet v l f=jet v k f := by
  induction hp with
  | nil => rfl
  | cons i hp ih => simp only [jet,ih]
  | swap i j l => exact dir_dir (smooth_jet hf v l) (v j) (v i)
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

lemma dir_smul (v : E) (c : ℝ) (f : E → ℝ) :
    dir (c • v) f=fun x => c*dir v f x := by
  funext x
  simp only [dir,map_smul,smul_eq_mul]

lemma jet_smul {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (l : List ι) (c : ℝ) :
    jet (fun i => c • v i) l f=fun x => c^l.length*jet v l f x := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    simp only [jet,ih,List.length_cons]
    rw [dir_const_mul ((smooth_jet hf v l).differentiable (by simp)),dir_smul]
    funext x
    simp only [pow_succ,dir]
    ring

end LogConcaveSampling.JetCalculus

end UpperProof
end
end
end

end OAI
