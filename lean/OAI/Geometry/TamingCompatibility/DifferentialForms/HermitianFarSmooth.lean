import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffSupported

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma parameter_fderiv_contDiffAt {f : P → E → F} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (fun x : P × E => f x.1 x.2) q) :
    ContDiffAt ℝ ∞ (fun x : P × E => fderiv ℝ (f x.1) x.2) q := by
  have h : ContDiffAt ℝ ∞ (fun x : (P × E) × E => f x.1.1 x.2) (q,q.2) :=
    hf.comp (q,q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact h.fderiv contDiffAt_snd (by simp)

lemma parameter_dc_contDiffAt {f : P → E → ℝ} {J : E → E →L[ℝ] E} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (fun x : P × E => f x.1 x.2) q)
    (hJ : ContDiffAt ℝ ∞ J q.2) :
    ContDiffAt ℝ ∞ (fun x : P × E => dc J (f x.1) x.2) q := by
  exact ((parameter_fderiv_contDiffAt hf).clm_comp
    (hJ.comp q contDiffAt_snd)).neg.continuousLinearMap_comp
      (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

lemma parameter_ddc_contDiffAt {f : P → E → ℝ} {J : E → E →L[ℝ] E} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (fun x : P × E => f x.1 x.2) q)
    (hJ : ContDiffAt ℝ ∞ J q.2) :
    ContDiffAt ℝ ∞ (fun x : P × E => extDeriv (dc J (f x.1)) x.2) q := by
  have hd : ContDiffAt ℝ ∞ (fun x : P × E => fderiv ℝ (dc J (f x.1)) x.2) q :=
    parameter_fderiv_contDiffAt (f := fun a => dc J (f a))
      (parameter_dc_contDiffAt hf hJ)
  exact hd.continuousLinearMap_comp (alternatizeUncurryFinCLM (n := 1) ℝ E ℝ)
end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.HermitianRadial
open RadialPotential Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]
variable (W : E → E →L[ℝ] E) (hW : ContDiff ℝ ∞ W) (R : ℝ)

include hW in
lemma translatedCutoffLog_joint_smooth {q : (ℝ × E) × E}
    (hq : 0 < q.1.1^2 + ‖q.2-q.1.2‖^2) :
    ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E => translatedCutoffLog W R x.1.1 x.1.2 x.2) q := by
  have hz : ContDiff ℝ ∞ (fun x : (ℝ × E) × E => x.2-x.1.2) := contDiff_snd.sub contDiff_fst.snd
  have hden : ContDiff ℝ ∞ (fun x : (ℝ × E) × E =>
      x.1.1^2 + ‖x.2-x.1.2‖^2 + ‖W x.1.2 (x.2-x.1.2)‖^2) :=
    ((contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp hz)).add
      ((contDiff_norm_sq ℝ).comp ((hW.comp contDiff_fst.snd).clm_apply hz))
  have hp : 0 < q.1.1^2 + ‖q.2-q.1.2‖^2 + ‖W q.1.2 (q.2-q.1.2)‖^2 := by positivity
  simpa only [translatedCutoffLog,cutoffLogPotential,hermitianLogPotential,
    logPotential,hermitianGraph_norm_sq,add_assoc,Function.comp_def] using
    ((scaledCutoff_smooth R).comp hz).contDiffAt.mul
      (contDiffAt_const.mul (hden.contDiffAt.log hp.ne'))

include hW in
lemma translatedCutoffSqrt_joint_smooth {q : (ℝ × E) × E}
    (hq : 0 < q.1.1^2 + ‖q.2-q.1.2‖^2) :
    ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E => translatedCutoffSqrt W R x.1.1 x.1.2 x.2) q := by
  have hz : ContDiff ℝ ∞ (fun x : (ℝ × E) × E => x.2-x.1.2) := contDiff_snd.sub contDiff_fst.snd
  have hden : ContDiff ℝ ∞ (fun x : (ℝ × E) × E =>
      x.1.1^2 + ‖x.2-x.1.2‖^2 + ‖W x.1.2 (x.2-x.1.2)‖^2) :=
    ((contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp hz)).add
      ((contDiff_norm_sq ℝ).comp ((hW.comp contDiff_fst.snd).clm_apply hz))
  have hp : 0 < q.1.1^2 + ‖q.2-q.1.2‖^2 + ‖W q.1.2 (q.2-q.1.2)‖^2 := by positivity
  simpa only [translatedCutoffSqrt,cutoffSqrtPotential,hermitianSqrtPotential,
    sqrtPotential,hermitianGraph_norm_sq,add_assoc,Function.comp_def] using
    ((scaledCutoff_smooth R).comp hz).contDiffAt.mul (hden.contDiffAt.sqrt hp.ne')
end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open RadialPotential ExteriorForms ContinuousAlternatingMap Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]
variable (W : E → E →L[ℝ] E) (hW : ContDiff ℝ ∞ W)
  (J : E → E →L[ℝ] E) (U : Set E) (hU : IsOpen U) (hJ : ContDiffOn ℝ ∞ J U)
  (R : ℝ) (K₀ L : Set E) (hK₀ : IsCompact K₀) (hL : IsCompact L) (hLU : L ⊆ U)
  (ε : ℝ) (hε : 0 < ε)

include hK₀ hL in
omit [InnerProductSpace ℝ E] [HasContDiffBump E] in
lemma far_parameter_compact : IsCompact
    {q : (ℝ × E) × E | q.1.1 ∈ Icc (0:ℝ) (2*R) ∧ q.1.2 ∈ K₀ ∧ q.2 ∈ L ∧
      ε ≤ q.1.1+‖q.2-q.1.2‖} := by
  have hclosed : _root_.IsClosed {q : (ℝ × E) × E | ε ≤ q.1.1+‖q.2-q.1.2‖} :=
    isClosed_le continuous_const (continuous_fst.fst.add (continuous_snd.sub continuous_fst.snd).norm)
  convert ((isCompact_Icc.prod hK₀).prod hL).inter_right hclosed using 1
  ext q
  simp only [mem_inter_iff,mem_prod,mem_ofPred_eq]
  tauto

include hW hU hJ hK₀ hL hLU hε in
lemma cutoffLog_ddc_far_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) (2*R),
    ∀ b ∈ K₀, ∀ y ∈ L, ε ≤ s+‖y-b‖ →
      ‖extDeriv (dc J (translatedCutoffLog W R s b)) y‖ ≤ C := by
  let S := {q : (ℝ × E) × E | q.1.1 ∈ Icc (0:ℝ) (2*R) ∧ q.1.2 ∈ K₀ ∧ q.2 ∈ L ∧
      ε ≤ q.1.1+‖q.2-q.1.2‖}
  have hS : IsCompact S := far_parameter_compact R K₀ L hK₀ hL ε
  have hcont : ContinuousOn (fun q : (ℝ × E) × E =>
      extDeriv (dc J (translatedCutoffLog W R q.1.1 q.1.2)) q.2) S := by
    intro q hq
    have hp : 0 < q.1.1^2+‖q.2-q.1.2‖^2 := by
      have h := hq.2.2.2
      nlinarith [sq_nonneg (q.1.1-‖q.2-q.1.2‖)]
    have hf : ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E =>
        translatedCutoffLog W R x.1.1 x.1.2 x.2) q :=
      translatedCutoffLog_joint_smooth W hW R hp
    have hj : ContDiffAt ℝ ∞ J q.2 := hJ.contDiffAt (hU.mem_nhds (hLU hq.2.2.1))
    have hd : ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E =>
        extDeriv (dc J (translatedCutoffLog W R x.1.1 x.1.2)) x.2) q :=
      parameter_ddc_contDiffAt (f := fun a : ℝ × E => translatedCutoffLog W R a.1 a.2)
        (J := J) (q := q) hf hj
    exact hd.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hcont
  exact ⟨max C 0,le_max_right _ _,fun s hs b hb y hy hf =>
    (hC ((s,b),y) ⟨hs,hb,hy,hf⟩).trans (le_max_left _ _)⟩

include hW hU hJ hK₀ hL hLU hε in
lemma cutoffSqrt_ddc_far_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) (2*R),
    ∀ b ∈ K₀, ∀ y ∈ L, ε ≤ s+‖y-b‖ →
      ‖extDeriv (dc J (translatedCutoffSqrt W R s b)) y‖ ≤ C := by
  let S := {q : (ℝ × E) × E | q.1.1 ∈ Icc (0:ℝ) (2*R) ∧ q.1.2 ∈ K₀ ∧ q.2 ∈ L ∧
      ε ≤ q.1.1+‖q.2-q.1.2‖}
  have hS : IsCompact S := far_parameter_compact R K₀ L hK₀ hL ε
  have hcont : ContinuousOn (fun q : (ℝ × E) × E =>
      extDeriv (dc J (translatedCutoffSqrt W R q.1.1 q.1.2)) q.2) S := by
    intro q hq
    have hp : 0 < q.1.1^2+‖q.2-q.1.2‖^2 := by
      have h := hq.2.2.2
      nlinarith [sq_nonneg (q.1.1-‖q.2-q.1.2‖)]
    have hf : ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E =>
        translatedCutoffSqrt W R x.1.1 x.1.2 x.2) q :=
      translatedCutoffSqrt_joint_smooth W hW R hp
    have hj : ContDiffAt ℝ ∞ J q.2 := hJ.contDiffAt (hU.mem_nhds (hLU hq.2.2.1))
    have hd : ContDiffAt ℝ ∞ (fun x : (ℝ × E) × E =>
        extDeriv (dc J (translatedCutoffSqrt W R x.1.1 x.1.2)) x.2) q :=
      parameter_ddc_contDiffAt (f := fun a : ℝ × E => translatedCutoffSqrt W R a.1 a.2)
        (J := J) (q := q) hf hj
    exact hd.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hcont
  exact ⟨max C 0,le_max_right _ _,fun s hs b hb y hy hf =>
    (hC ((s,b),y) ⟨hs,hb,hy,hf⟩).trans (le_max_left _ _)⟩
include hK₀ hL hε in
omit [InnerProductSpace ℝ E] [HasContDiffBump E] in
lemma log_distance_far_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) (2*R),
    ∀ b ∈ K₀, ∀ y ∈ L, ε ≤ s+‖y-b‖ → |Real.log (s+‖y-b‖)| ≤ C := by
  let S := {q : (ℝ × E) × E | q.1.1 ∈ Icc (0:ℝ) (2*R) ∧ q.1.2 ∈ K₀ ∧ q.2 ∈ L ∧
      ε ≤ q.1.1+‖q.2-q.1.2‖}
  have hS : IsCompact S := far_parameter_compact R K₀ L hK₀ hL ε
  have hcont : ContinuousOn (fun q : (ℝ × E) × E => Real.log (q.1.1+‖q.2-q.1.2‖)) S := by
    intro q hq
    have hp : 0 < q.1.1+‖q.2-q.1.2‖ := hε.trans_le hq.2.2.2
    exact ((continuous_fst.fst.add (continuous_snd.sub continuous_fst.snd).norm).continuousAt.log
      hp.ne').continuousWithinAt
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s hs b hb y hy hf
  exact (hC ((s,b),y) ⟨hs,hb,hy,hf⟩).trans (le_max_left _ _)
end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
