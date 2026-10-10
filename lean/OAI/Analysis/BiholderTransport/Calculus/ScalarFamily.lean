import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

def modifiedScalar (α D : ℝ) (B : ℝ → ℝ) (p : ℝ×ℝ) : ℝ :=
  p.2+p.1*B ((p.2-α)/D)

lemma modifiedScalar_contDiff {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B) (α D : ℝ) :
    ContDiff ℝ ∞ (modifiedScalar α D B) :=
  contDiff_snd.add (contDiff_fst.mul (hB.comp ((contDiff_snd.sub contDiff_const).div_const D)))

lemma scalar_family_hasDeriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (p:ℝ×ℝ) :
    HasDerivAt (fun s=>Φ (p.1,s)) (fderiv ℝ Φ p (0,1)) p.2 := by
  have H := (hΦ.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact H

lemma continuous_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.continuous.clm_apply continuous_const

lemma scalar_family_derivable {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (p:ℝ×ℝ) :
    HasDerivAt (fun s=>Φ (p.1,s)) (deriv (fun s=>Φ (p.1,s)) p.2) p.2 :=
  (scalar_family_hasDeriv hΦ p).differentiableAt.hasDerivAt

end WeakMTWTransport

end

end OAI
