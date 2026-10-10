import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenmode
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling
import Mathlib.Analysis.ODE.PicardLindelof

namespace OAI

/-! # Smooth exterior regularity of projected eigenfunctions

The C² angular coefficients satisfy a smooth first-order system away from
zero. The ODE regularity theorem supplies all higher derivatives.
-/

open Set
open scoped ContDiff

namespace DefocusingNLS

local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def harmonicRadialState (f g : ℝ → ℂ) (r : ℝ) : E₄ :=
  ((f r, deriv f r), (g r, deriv g r))

theorem harmonicRadialState_hasDerivAt (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (eta lam : ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (heq : IsHarmonicRadialEigenpair a b m Q eta lam f g) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (harmonicRadialState f g)
      (spectralPhysicalCircularField (-2 * (a : ℂ) + 2 * Complex.I * (b : ℂ) - 2 * lam)
        (-2 * (a : ℂ) - 2 * Complex.I * (b : ℂ) - 2 * lam) eta m (Q r) r
        (harmonicRadialState f g r)) r := by
  have hfd := ((hf.deriv' : ContDiff ℝ 1 (deriv f)).differentiable one_ne_zero r).hasDerivAt
  have hgd := ((hg.deriv' : ContDiff ℝ 1 (deriv g)).differentiable one_ne_zero r).hasDerivAt
  have hd := (((hf.differentiable (by norm_num) r).hasDerivAt.prodMk hfd).prodMk
    ((hg.differentiable (by norm_num) r).hasDerivAt.prodMk hgd))
  apply hd.congr_deriv
  obtain ⟨hp, hm⟩ := heq r hr
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · dsimp only [harmonicRadialState, spectralPhysicalCircularField,
      spectralDiagonalCoefficient, spectralCrossCoefficient]
    push_cast at hp ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) Complex.I * hp
  · rfl
  · dsimp only [harmonicRadialState, spectralPhysicalCircularField,
      spectralDiagonalCoefficient, spectralCrossCoefficient]
    push_cast at hm ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) -Complex.I * hm

theorem spectralPhysicalCircularField_contDiffOn (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (s : Set ℝ) (hQ : ContDiffOn ℝ ∞ Q s)
    (hs : ∀ r ∈ s, r ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E₄ =>
      spectralPhysicalCircularField νp νm eta m (Q p.1) p.1 p.2) (s ×ˢ univ) := by
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => (p.1 : ℂ)) (s ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_fst.contDiffOn
  have hq : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => Q p.1) (s ×ˢ univ) :=
    hQ.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  have hr0 (p : ℝ × E₄) (hp : p ∈ s ×ˢ univ) : (p.1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hs p.1 hp.1)
  have h11 : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => 11 / (p.1 : ℂ)) (s ×ˢ univ) := by
    simpa only [div_eq_mul_inv] using
      (contDiffOn_const.mul (hr.inv hr0) : ContDiffOn ℝ ∞
        (fun p : ℝ × E₄ => 11 * (p.1 : ℂ)⁻¹) (s ×ˢ univ))
  have hη : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => eta / (p.1 : ℂ) ^ 2) (s ×ˢ univ) := by
    simpa only [div_eq_mul_inv] using
      (contDiffOn_const.mul ((hr.pow 2).inv (fun p hp => pow_ne_zero 2 (hr0 p hp))) :
        ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => eta * ((p.1 : ℂ) ^ 2)⁻¹) (s ×ˢ univ))
  have hI : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => Complex.I * (p.1 : ℂ) / 2)
      (s ×ˢ univ) := (contDiffOn_const.mul hr).div_const (2 : ℂ)
  have hqs : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => star (Q p.1)) (s ×ˢ univ) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hq
  have hD := ((contDiffOn_const.mul (hq.pow m)).mul (hqs.pow m) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E₄ =>
      ((m + 1 : ℕ) : ℂ) * Q p.1 ^ m * star (Q p.1) ^ m) (s ×ˢ univ))
  have hC := ((contDiffOn_const.mul (hq.pow (m + 1))).mul (hqs.pow (m - 1)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E₄ =>
      (m : ℂ) * Q p.1 ^ (m + 1) * star (Q p.1) ^ (m - 1)) (s ×ˢ univ))
  have hDs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hD
  have hCs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hC
  have hf₀ : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.1.1) (s ×ˢ univ) := by fun_prop
  have hf₁ : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.1.2) (s ×ˢ univ) := by fun_prop
  have hg₀ : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.2.1) (s ×ˢ univ) := by fun_prop
  have hg₁ : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.2.2) (s ×ˢ univ) := by fun_prop
  exact (hf₁.prodMk ((((h11.add hI).neg.mul hf₁).sub
    ((contDiffOn_const.sub hη).mul hf₀)).add (hD.mul hf₀) |>.add (hC.mul hg₀))).prodMk
    (hg₁.prodMk ((((h11.sub hI).neg.mul hg₁).sub
    ((contDiffOn_const.sub hη).mul hg₀)).add (hDs.mul hg₀) |>.add (hCs.mul hf₀)))

theorem harmonicRadialEigenpair_contDiffOn (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (eta lam : ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (heq : IsHarmonicRadialEigenpair a b m Q eta lam f g)
    (R : ℝ) (hR : 0 ≤ R) (hQ : ContDiffOn ℝ ∞ Q (Ioi R)) :
    ContDiffOn ℝ ∞ f (Ioi R) ∧ ContDiffOn ℝ ∞ g (Ioi R) := by
  have hstate : ContDiffOn ℝ ∞ (harmonicRadialState f g) (Ioi R) := by
    intro r hr
    simp only [mem_Ioi] at hr
    let α := (R + r) / 2
    let β := r + 1
    have hα : R < α := by dsimp only [α]; linarith
    have hαr : α < r := by dsimp only [α]; linarith
    have hrβ : r < β := by dsimp only [β]; linarith
    have hsub : Icc α β ⊆ Ioi R := fun t ht => hα.trans_le ht.1
    have hv : ContDiffOn ℝ ∞ (harmonicRadialState f g) (Icc α β) := by
      apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
        (f := fun t U => spectralPhysicalCircularField
          (-2 * (a : ℂ) + 2 * Complex.I * (b : ℂ) - 2 * lam)
          (-2 * (a : ℂ) - 2 * Complex.I * (b : ℂ) - 2 * lam) eta m (Q t) t U)
        (u := (univ : Set E₄))
      · exact spectralPhysicalCircularField_contDiffOn _ _ eta m Q _ (hQ.mono hsub)
          (fun t ht => (hR.trans_lt (hsub ht)).ne')
      · intro t ht
        exact (harmonicRadialState_hasDerivAt a b m Q f g eta lam hf hg heq t
          (hR.trans_lt (hsub ht))).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
    exact (hv.contDiffAt (Icc_mem_nhds hαr hrβ)).contDiffWithinAt
  exact ⟨hstate.fst.fst, hstate.snd.fst⟩

end DefocusingNLS

end OAI
