import Mathlib
import OAI.Analysis.AffineBernstein.TubeSecondForm
import OAI.Analysis.AffineBernstein.SupportVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
lemma support_identities_variation {H G : S × E → ℝ} {Y Z : S × E → E} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (heH : H =ᶠ[𝓝 q] (fun p => inner ℝ p.2 (Y p)))
    (heG : G =ᶠ[𝓝 q] (fun p => inner ℝ p.2 (Z p)))
    (hgH : ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ H p (0,v) = inner ℝ (Y p) v)
    (hgG : ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ G p (0,v) = inner ℝ (Z p) v)
    (t : ℝ) :
    (fun p => H p+t*G p) =ᶠ[𝓝 q] (fun p => inner ℝ p.2 (Y p+t • Z p)) ∧
    ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ (fun r => H r+t*G r) p (0,v) =
      inner ℝ (Y p+t • Z p) v := by
  constructor
  · filter_upwards [heH,heG] with p hpH hpG
    simp [hpH,hpG,inner_add_right,real_inner_smul_right]
  · filter_upwards [hgH,hgG,
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      (hG.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)] with p hpH hpG hdH hdG v
    have hh := hdH.differentiableAt (by norm_num)
    have hg := hdG.differentiableAt (by norm_num)
    rw [fderiv_fun_add hh (hg.const_mul t),fderiv_const_mul hg t]
    simp [hpH v,hpG v,inner_add_left,real_inner_smul_left]

lemma flatSupportVariation_support_identities (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    flatSupportVariation ℓ q₀ C η =ᶠ[𝓝 q]
      (fun p => inner ℝ p.2 (supportGradient (flatSupportVariation ℓ q₀ C η) p)) ∧
    ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ (flatSupportVariation ℓ q₀ C η) p (0,v) =
      inner ℝ (supportGradient (flatSupportVariation ℓ q₀ C η) p) v := by
  have hn : ∀ᶠ p in 𝓝 q, ℓ p.2 ≠ 0 :=
    ((ℓ.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hne))
  constructor
  · filter_upwards [hn] with p hp
    exact flatSupportVariation_euler ℓ q₀ C hη hp
  · filter_upwards [hn] with p hp v
    exact supportGradient_angular
      ((contDiffAt_flatSupportVariation ℓ q₀ C hη hp).differentiableAt (by simp)) v

omit [CompleteSpace E] in
lemma supportParam_variation (Y Z : S × E → E) (t : ℝ) (q : S × E) :
    supportParam (fun p => Y p+t • Z p) q = supportParam Y q+t • ((0 : S),Z q) := by
  simp [supportParam]

lemma supportConormal_variation_continuous {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q) (t : ℝ) (v : S × E) :
    ContinuousAt (fun p : ℝ × (S × E) => supportConormal
      (fun r => H r+p.1*G r) p.2 v) (t,q) := by
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × (S × E) => H p.2+p.1*G p.2) (t,q) :=
    (hH.comp (t,q) contDiffAt_snd).add
      (contDiffAt_fst.mul (hG.comp (t,q) contDiffAt_snd))
  have hd := contDiffAt_fiberGradient hF
  have ha := (hd.clm_apply (contDiffAt_const (c := (v.1,0)))).continuousAt
  have hb : ContinuousAt (fun p : ℝ × (S × E) => inner ℝ p.2.2 v.2) (t,q) :=
    continuousAt_snd.snd.inner continuousAt_const
  exact ha.sub hb

lemma supportConormal_flat_transverse {H : S × E → ℝ} {q : S × E} {d : E}
    (hd : inner ℝ q.2 d = 1) : supportConormal H q ((0 : S),-d) = 1 := by
  simp [supportConormal,show ((0,0) : S × E) = 0 from rfl,hd]

lemma supportConormal_flat_variation_tangent {H G : S × E → ℝ} {Y Z : S × E → E}
    (q₀ : S × E) (J : F →L[ℝ] S × E) {x : F}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x)) (hG : ContDiffAt ℝ ∞ G (q₀+J x))
    (hY : ContDiffAt ℝ ∞ Y (q₀+J x)) (hZ : ContDiffAt ℝ ∞ Z (q₀+J x))
    (heH : H =ᶠ[𝓝 (q₀+J x)] (fun p => inner ℝ p.2 (Y p)))
    (heG : G =ᶠ[𝓝 (q₀+J x)] (fun p => inner ℝ p.2 (Z p)))
    (hgH : ∀ᶠ p in 𝓝 (q₀+J x), ∀ v : E, fderiv ℝ H p (0,v) = inner ℝ (Y p) v)
    (hgG : ∀ᶠ p in 𝓝 (q₀+J x), ∀ v : E, fderiv ℝ G p (0,v) = inner ℝ (Z p) v)
    (t : ℝ) :
    (supportConormal (fun r => H r+t*G r) (q₀+J x)).comp
      (fderiv ℝ (fun y => supportParam Y (q₀+J y)+t • ((0 : S),Z (q₀+J y))) x) = 0 := by
  obtain ⟨he,hg⟩ := support_identities_variation hH hG heH heG hgH hgG t
  have hHt : ContDiffAt ℝ ∞ (fun r => H r+t*G r) (q₀+J x) := hH.add (contDiffAt_const.mul hG)
  have hYt : ContDiffAt ℝ ∞ (fun r => Y r+t • Z r) (q₀+J x) := hY.add (hZ.const_smul t)
  have heq : (fun y => supportParam Y (q₀+J y)+t • ((0 : S),Z (q₀+J y))) =
      (fun y => supportParam (fun r => Y r+t • Z r) (q₀+J y)) := by
    funext y
    exact (supportParam_variation Y Z t _).symm
  rw [heq]
  have hpY : ContDiffAt ℝ ∞ (supportParam (fun r => Y r+t • Z r)) (q₀+J x) :=
    contDiffAt_fst.prodMk hYt
  have hp := (hpY.differentiableAt (by simp)).hasFDerivAt.comp
    (f := fun y => q₀+J y) x (J.hasFDerivAt.const_add q₀)
  have hdf : fderiv ℝ (fun y => supportParam (fun r => Y r+t • Z r) (q₀+J y)) x = _ := hp.fderiv
  rw [hdf]
  ext v
  exact supportConormal_tangent (hHt.differentiableAt (by simp))
    (hYt.differentiableAt (by simp)) he hg.self_of_nhds (J v)

end AffineBernstein
end

end OAI
