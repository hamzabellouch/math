import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.NearActiveMaximum

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def propagationGamma (B : ℝ) : ℝ := B/(16*(11/10:ℝ)^5)

lemma propagationGamma_pos {B : ℝ} (hB : 0<B) : 0<propagationGamma B := by
  unfold propagationGamma
  positivity

lemma propagationBarrier_two_sided {B r : ℝ} (hB : 0≤B) (hr : 0<r)
    {x : Position} (hx : r≤‖x‖) :
    (7/8:ℝ)*B/‖x‖^4≤propagationBarrier B r x ∧ propagationBarrier B r x≤B/‖x‖^4 := by
  have hd := hr.trans_le hx
  have ht : 0≤r/(8*‖x‖) := by positivity
  have ht' : r/(8*‖x‖)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hx])
  rw [propagationBarrier_eq]
  constructor
  · have H := mul_le_mul_of_nonneg_left (show (7/8:ℝ)≤1-r/(8*‖x‖) by linarith only [ht'])
      (div_nonneg hB (pow_pos hd 4).le)
    calc
      _=(B/‖x‖^4)*(7/8:ℝ) := by ring
      _≤_ := H
  · have H := mul_le_mul_of_nonneg_left (show 1-r/(8*‖x‖)≤1 by linarith only [ht])
      (div_nonneg hB (pow_pos hd 4).le)
    simpa only [mul_one] using H

lemma propagationBarrier_positive {B r : ℝ} (hB : 0<B) (hr : 0<r)
    {x : Position} (hx : r≤‖x‖) : 0<propagationBarrier B r x := by
  have hd := hr.trans_le hx
  exact (by positivity : (0:ℝ)<(7/8:ℝ)*B/‖x‖^4).trans_le (propagationBarrier_two_sided hB.le hr hx).1

lemma propagationBarrier_normalized {B r : ℝ} {x : Position} (hx : x≠0) :
    ‖x‖^4*propagationBarrier B r x=B*(1-r/(8*‖x‖)) := by
  rw [propagationBarrier_eq]
  have hn := norm_ne_zero_iff.mpr hx
  field_simp

lemma propagationBarrier_gap {B r : ℝ} (hB : 0<B) (hr : 0<r)
    {x : Position} (hx : 2*r≤‖x‖) (hx' : ‖x‖≤(11/10)*(2*r)) :
    propagationGamma B/(2*r)^4≤propagationBarrier B r x-propagationBarrier B (2*r) x := by
  have hd : 0<‖x‖ := (by positivity : (0:ℝ)<2*r).trans_le hx
  have he : (propagationBarrier B r x-propagationBarrier B (2*r) x)*(2*r)^4=
      B*(2*r)^5/(16*‖x‖^5) := by
    rw [propagationBarrier_eq,propagationBarrier_eq]
    field_simp
    ring
  apply (div_le_iff₀ (pow_pos (mul_pos (by norm_num) hr) 4)).mpr
  rw [he]
  apply (le_div_iff₀ (by positivity : 0<16*‖x‖^5)).mpr
  have hp := pow_le_pow_left₀ hd.le hx' 5
  have hmul := mul_le_mul_of_nonneg_left hp hB.le
  unfold propagationGamma
  norm_num
  nlinarith only [hmul]

lemma tfReaction_div_fourth (v : ℝ) {d : ℝ} (hd : 0<d) :
    tfReaction (v/d^4)=tfReaction v/d^6 := by
  rw [tfReaction_eq_scalar,tfReaction_eq_scalar,Coulomb.tfScalarDensity_scale v hd]
  ring

lemma propagationBarrier_reaction_bound {B r : ℝ} (hB : 0<B) (hr : 0<r)
    {x : Position} (hx : r≤‖x‖) :
    tfReaction (propagationBarrier B r x)≤(4*Real.pi*kTF*Real.sqrt B)*B/‖x‖^6 := by
  have hd := hr.trans_le hx
  have H := tfReaction_monotone (propagationBarrier_two_sided hB.le hr hx).2
  rw [tfReaction_div_fourth B hd] at H
  have hb : B^(3/2:ℝ)=B*Real.sqrt B := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hB,Real.rpow_one,Real.sqrt_eq_rpow]
  have he : tfReaction B=(4*Real.pi*kTF*Real.sqrt B)*B := by
    unfold tfReaction
    rw [max_eq_left hB.le,hb]
    ring
  rw [he] at H
  exact H

theorem propagationBarrier_laplacian_ge_reaction {B r : ℝ} (hB : 0<B) (hr : 0<r)
    (hsmall : 4*Real.pi*kTF*Real.sqrt B≤19/2) {x : Position} (hx : r≤‖x‖) :
    tfReaction (propagationBarrier B r x)≤coordinateLaplacian (propagationBarrier B r) x := by
  have hd := hr.trans_le hx
  have hx0 : x≠0 := norm_pos_iff.mp hd
  have hfrac : 5*r/(2*‖x‖)≤5/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hx])
  rw [laplacian_propagationBarrier hx0]
  calc
    _≤(4*Real.pi*kTF*Real.sqrt B)*B/‖x‖^6 := propagationBarrier_reaction_bound hB hr hx
    _≤(19/2:ℝ)*B/‖x‖^6 := by gcongr
    _≤B/‖x‖^6*(12-5*r/(2*‖x‖)) := by
      have H := mul_le_mul_of_nonneg_left (show (19/2:ℝ)≤12-5*r/(2*‖x‖) by linarith only [hfrac])
        (by positivity : 0≤B/‖x‖^6)
      calc
        _=(B/‖x‖^6)*(19/2:ℝ) := by ring
        _≤_ := H
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma WeakLaplacianGE.of_classical {f q : Position → ℝ} {U : Set Position}
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) (hq : LocallyIntegrableOn q U)
    (hle : ∀ x ∈ U, q x ≤ coordinateLaplacian f x) : WeakLaplacianGE f U q := by
  intro φ hφ hc ht hp
  rw [integral_mul_coordinateLaplacian_eq (fun x hx => hf x (ht hx)) hφ hc]
  apply integral_mono (integrable_mul_test_on hq hφ.continuous hc ht)
    (integrable_mul_compact_of_continuousAt
      (fun x hx => continuousAt_coordinateLaplacian (hf x (ht hx))) hφ.continuous hc)
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hle x (ht hx)) (hp x)
  · simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,le_refl]

lemma WeakLaplacianGE.to_nuclear_away {f q : Position → ℝ} {U : Set Position}
    (hw : WeakLaplacianGE f U q) (h0 : (0:Position) ∉ U) (Z : ℝ) :
    WeakNuclearSubsolution f Z U q := by
  intro φ hφ hc ht hp
  have hz := image_eq_zero_of_notMem_tsupport (show (0:Position) ∉ tsupport φ from fun h => h0 (ht h))
  simpa only [hz,mul_zero,neg_zero,zero_add] using hw φ hφ hc ht hp

lemma WeakNuclearSubsolution.congr_on {f g q r : Position → ℝ} {U : Set Position} {Z : ℝ}
    (hw : WeakNuclearSubsolution f Z U q) (he : ∀ x ∈ U, f x=g x) (hq : ∀ x ∈ U, q x=r x) :
    WeakNuclearSubsolution g Z U r := by
  intro φ hφ hc ht hp
  have H := hw φ hφ hc ht hp
  have hleft : (fun x => q x*φ x)=(fun x => r x*φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hq x (ht hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (fun x => f x*coordinateLaplacian φ x)=(fun x => g x*coordinateLaplacian φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [he x (ht hx)]
    · simp [coordinateLaplacian_eq_zero_of_notMem_tsupport hx]
  simpa only [hleft,hright] using H

lemma WeakNuclearSubsolution.mono_domain {f q : Position → ℝ} {U V : Set Position} {Z : ℝ}
    (hw : WeakNuclearSubsolution f Z U q) (hVU : V ⊆ U) : WeakNuclearSubsolution f Z V q :=
  fun φ hφ hc ht hp => hw φ hφ hc (ht.trans hVU) hp

lemma WeakNuclearSubsolution.of_local {f q : Position → ℝ} {U : Set Position} {Z : ℝ}
    (hf : Continuous f) (hq : LocallyIntegrable q volume)
    (hw : ∀ x ∈ U, ∃ V : Set Position, x ∈ V ∧ IsOpen V ∧
      WeakNuclearSubsolution (fun y => Z*coulombKernel y+f y) Z V q) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U q := by
  apply (weakNuclearSubsolution_offset_iff hf).2
  apply WeakLaplacianGE.of_local hf.locallyIntegrable hq
  intro x hx
  obtain ⟨V,hxV,hV,hWV⟩ := hw x hx
  exact ⟨V,hxV,hV,(weakNuclearSubsolution_offset_iff hf).1 hWV⟩

lemma WeakLaplacianGE.sub_const {f q : Position → ℝ} {U : Set Position}
    (hf : Continuous f) (hw : WeakLaplacianGE f U q) (c : ℝ) :
    WeakLaplacianGE (fun x => f x-c) U q := by
  intro φ hφ hc ht hp
  have hi := integrable_mul_compact_of_continuousAt (fun x _ => hf.continuousAt)
    (contDiff_coordinateLaplacian hφ).continuous (hasCompactSupport_coordinateLaplacian hc)
  have hi' : Integrable (fun x => c*coordinateLaplacian φ x) := ((contDiff_coordinateLaplacian hφ).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_coordinateLaplacian hc)).const_mul c
  simp_rw [sub_mul]
  rw [integral_sub hi hi',integral_const_mul,integral_coordinateLaplacian hφ hc,mul_zero,sub_zero]
  exact hw φ hφ hc ht hp

lemma WeakNuclearSubsolution.sub_offset_const {f q : Position → ℝ} {U : Set Position} {Z : ℝ}
    (hf : Continuous f) (hw : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U q) (c : ℝ) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+(f x-c)) Z U q :=
  (weakNuclearSubsolution_offset_iff (hf.sub continuous_const)).2
    (((weakNuclearSubsolution_offset_iff hf).1 hw).sub_const hf c)

end NeutralAtom

end

end OAI
