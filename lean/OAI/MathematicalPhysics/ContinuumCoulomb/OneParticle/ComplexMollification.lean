import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealMollification

namespace OAI

/-! Componentwise mollification preserves the actual complex weak derivatives.
All estimates here are unconditional. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace ContinuumCoulomb

private theorem re_memLp {n : ℕ} {u : Configuration n → ℂ} (hu : MemLp u 2) :
    MemLp (fun x => (u x).re) 2 := Complex.reCLM.comp_memLp' hu

private theorem im_memLp {n : ℕ} {u : Configuration n → ℂ} (hu : MemLp u 2) :
    MemLp (fun x => (u x).im) 2 := Complex.imCLM.comp_memLp' hu

def complexMollification {n : ℕ} (u : Configuration n → ℂ) (k : ℕ) :
    Configuration n → ℂ := fun x =>
  (realMollification (fun y => (u y).re) k x : ℂ)+
    Complex.I*(realMollification (fun y => (u y).im) k x : ℂ)

@[simp] theorem complexMollification_re {n : ℕ} (u : Configuration n → ℂ) (k : ℕ)
    (x : Configuration n) :
    (complexMollification u k x).re = realMollification (fun y => (u y).re) k x := by
  simp [complexMollification]

@[simp] theorem complexMollification_im {n : ℕ} (u : Configuration n → ℂ) (k : ℕ)
    (x : Configuration n) :
    (complexMollification u k x).im = realMollification (fun y => (u y).im) k x := by
  simp [complexMollification]

theorem complexMollification_smooth {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (complexMollification u k) :=
  (Complex.ofRealCLM.contDiff.comp (realMollification_smooth (re_memLp hu) k)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (realMollification_smooth (im_memLp hu) k)))

theorem complexMollification_memLp {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) (k : ℕ) : MemLp (complexMollification u k) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (complexMollification_smooth hu k).continuous.aestronglyMeasurable).mpr
  simp_rw [Coulomb.complex_norm_sq_components,complexMollification_re,complexMollification_im]
  exact ((realMollification_contraction (re_memLp hu) k).1.integrable_sq).add
    ((realMollification_contraction (im_memLp hu) k).1.integrable_sq)

theorem complexMollification_error {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∫ x, ‖u x-complexMollification u k x‖^2) < ε := by
  have hr := realMollification_error (re_memLp hu) (half_pos hε)
  have hi := realMollification_error (im_memLp hu) (half_pos hε)
  filter_upwards [hr,hi] with k hkr hki
  have he : (∫ x, ‖u x-complexMollification u k x‖^2) =
      (∫ x, (realMollification (fun y => (u y).re) k x-(u x).re)^2)+
      (∫ x, (realMollification (fun y => (u y).im) k x-(u x).im)^2) := by
    have hR : Integrable (fun x =>
        (realMollification (fun y => (u y).re) k x-(u x).re)^2) := by
      simpa only [Pi.sub_apply] using
        ((realMollification_contraction (re_memLp hu) k).1.sub (re_memLp hu)).integrable_sq
    have hI : Integrable (fun x =>
        (realMollification (fun y => (u y).im) k x-(u x).im)^2) := by
      simpa only [Pi.sub_apply] using
        ((realMollification_contraction (im_memLp hu) k).1.sub (im_memLp hu)).integrable_sq
    rw [← integral_add hR hI]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [Coulomb.complex_norm_sq_components]
    simp only [Complex.sub_re,Complex.sub_im,complexMollification_re,complexMollification_im]
    ring
  rw [he]
  linarith

theorem complexMollification_partial {n : ℕ} {u g : Configuration n → ℂ}
    (hu : MemLp u 2) (hg : MemLp g 2) (v : Configuration n)
    (hw : ∀ (φ : Configuration n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x*(fderiv ℝ φ x v:ℂ)) = -(∫ x, g x*(φ x:ℂ)))
    (k : ℕ) (x : Configuration n) :
    fderiv ℝ (complexMollification u k) x v = complexMollification g k x := by
  have hd (L : ℂ →L[ℝ] ℝ) :
      fderiv ℝ (realMollification (fun y => L (u y)) k) x v =
        realMollification (fun y => L (g y)) k x :=
    Coulomb.weak_convolution_partial _ _ _ v
      ((L.comp_memLp' hu).locallyIntegrable (by norm_num))
      (Coulomb.hardyMollifier k).contDiff_normed
      (Coulomb.hardyMollifier k).hasCompactSupport_normed
      (Coulomb.weak_complex_component u g hu hg v hw L) x
  have hc := (complexMollification_smooth hu k).differentiable (by simp)
  have hp (L : ℂ →L[ℝ] ℝ) :
      fderiv ℝ (fun y => L (complexMollification u k y)) x v =
        L (fderiv ℝ (complexMollification u k) x v) :=
    congrArg (fun A : Configuration n →L[ℝ] ℝ => A v)
      (L.hasFDerivAt.comp x (hc x).hasFDerivAt).fderiv
  apply Complex.ext
  · have h := hp Complex.reCLM
    simp only [Complex.reCLM_apply,complexMollification_re] at h
    have hderiv := hd Complex.reCLM
    simp only [Complex.reCLM_apply] at hderiv
    change fderiv ℝ (realMollification (fun y => (u y).re) k) x v = _ at h
    rw [hderiv] at h
    simpa only [Complex.reCLM_apply,complexMollification_re] using h.symm
  · have h := hp Complex.imCLM
    simp only [Complex.imCLM_apply,complexMollification_im] at h
    have hderiv := hd Complex.imCLM
    simp only [Complex.imCLM_apply] at hderiv
    change fderiv ℝ (realMollification (fun y => (u y).im) k) x v = _ at h
    rw [hderiv] at h
    simpa only [Complex.imCLM_apply,complexMollification_im] using h.symm

end ContinuumCoulomb

end

end OAI
