import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoing
import Mathlib.Analysis.ODE.PicardLindelof

namespace OAI

/-! # Smoothness of actual exterior ODE solutions on their open tail -/

open Set
open scoped ContDiff

namespace DefocusingNLS

theorem radialExteriorODEField_contDiff (ν : ℂ) (n : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (radialExteriorODEField ν n)) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × (ℂ × ℂ) => z.2.1) := contDiff_snd.fst
  have hg : ContDiff ℝ ∞ (fun z : ℝ × (ℂ × ℂ) => z.2.2) := contDiff_snd.snd
  have he : ContDiff ℝ ∞ (fun z : ℝ × (ℂ × ℂ) =>
      ((Real.exp (2 * z.1) / 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).div_const 2)
  have hN := ((contDiff_oddPowerNonlinearity n).of_le
    (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).comp hf
  unfold Function.uncurry radialExteriorODEField
  exact hg.prodMk (((((contDiff_const.add (contDiff_const.mul he)).neg).mul hg).sub
    (contDiff_const.mul hf)).add hN)

theorem radialExteriorODE_solution_contDiffOn (ν : ℂ) (n : ℕ)
    (Z : ℝ → ℂ × ℂ) (L : ℝ)
    (hZ : ∀ t, L < t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t) :
    ContDiffOn ℝ ∞ Z (Ioi L) := by
  intro r hr
  change L < r at hr
  have hI : Icc ((r + L) / 2) (r + 1) ⊆ Ioi L := fun t ht => by
    change L < t
    linarith [ht.1]
  have hF : ContDiffOn ℝ ∞ (Function.uncurry (radialExteriorODEField ν n))
      ((Icc ((r + L) / 2) (r + 1)) ×ˢ (univ : Set (ℂ × ℂ))) :=
    (radialExteriorODEField_contDiff ν n).contDiffOn
  have hh := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hF
    (fun t ht => (hZ t (hI ht)).hasDerivWithinAt) (fun _ _ => mem_univ _)
  exact (hh r ⟨by linarith, by linarith⟩).contDiffAt
    (Icc_mem_nhds (by linarith) (by linarith)) |>.contDiffWithinAt

theorem radialExteriorODE_position_contDiffOn (ν : ℂ) (n : ℕ)
    (Z : ℝ → ℂ × ℂ) (L : ℝ)
    (hZ : ∀ t, L < t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t) :
    ContDiffOn ℝ ∞ (fun t => (Z t).1) (Ioi L) :=
  (radialExteriorODE_solution_contDiffOn ν n Z L hZ).fst

end DefocusingNLS

end OAI
