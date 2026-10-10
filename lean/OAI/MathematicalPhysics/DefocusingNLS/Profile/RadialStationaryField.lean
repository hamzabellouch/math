import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.ODE.PicardLindelof

namespace OAI

/-! The smooth first-order stationary radial field away from the origin. -/

open scoped ContDiff
open Set
namespace DefocusingNLS

noncomputable def radialStationaryField (k : ℕ) (a b r : ℝ) (W : ℂ × ℂ) : ℂ × ℂ :=
  (W.2,-(11/r : ℝ)*W.2-Complex.I*((r/2 : ℝ)*W.2+(a : ℂ)*W.1)-
    (b : ℂ)*W.1+oddPowerNonlinearity k W.1)

theorem radialStationaryField_contDiffAt (k : ℕ) (a b : ℝ) (x : ℝ × (ℂ × ℂ))
    (hx : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (radialStationaryField k a b)) x := by
  have hN := ((contDiff_oddPowerNonlinearity k).of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffAt.comp x
    (contDiffAt_snd.fst : ContDiffAt ℝ ∞ (fun t : ℝ × (ℂ × ℂ) => t.2.1) x)
  have hQ : ContDiffAt ℝ ∞ (fun t : ℝ × (ℂ × ℂ) => ((11/t.1 : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_const.div contDiffAt_fst hx)
  have hR : ContDiffAt ℝ ∞ (fun t : ℝ × (ℂ × ℂ) => ((t.1/2 : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_fst.div_const 2)
  have hF : ContDiffAt ℝ ∞ (fun t : ℝ × (ℂ × ℂ) => t.2.1) x := contDiffAt_snd.fst
  have hD : ContDiffAt ℝ ∞ (fun t : ℝ × (ℂ × ℂ) => t.2.2) x := contDiffAt_snd.snd
  have hI : ContDiffAt ℝ ∞ (fun t : ℝ × (ℂ × ℂ) =>
      Complex.I*((t.1/2 : ℝ)*(t.2.2)+(a : ℂ)*t.2.1)) x :=
    contDiffAt_const.mul ((hR.mul hD).add (contDiffAt_const.mul hF))
  unfold Function.uncurry radialStationaryField
  exact hD.prodMk ((((hQ.neg.mul hD).sub hI).sub (contDiffAt_const.mul hF)).add hN)

theorem radialStationaryField_contDiffOn (k : ℕ) (a b : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (radialStationaryField k a b))
      ((Ioi 0) ×ˢ (univ : Set (ℂ × ℂ))) := by
  intro x hx
  exact (radialStationaryField_contDiffAt k a b x hx.1.ne').contDiffWithinAt

theorem radialStationarySolution_contDiffOn (k : ℕ) (a b : ℝ) (W : ℝ → ℂ × ℂ)
    (hW : ∀ r, 0 < r → HasDerivAt W (radialStationaryField k a b r (W r)) r) :
    ContDiffOn ℝ ∞ W (Ioi 0) := by
  intro r hr
  change 0 < r at hr
  have hI : Icc (r/2) (r+1) ⊆ Ioi 0 := fun t ht => by
    change 0 < t
    linarith [ht.1]
  have hF := (radialStationaryField_contDiffOn k a b).mono
    (Set.prod_mono hI (Subset.refl _))
  have hh := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hF
    (fun t ht => (hW t (hI ht)).hasDerivWithinAt) (fun _ _ => mem_univ _)
  exact (hh r ⟨by linarith,by linarith⟩).contDiffAt
    (Icc_mem_nhds (by linarith) (by linarith)) |>.contDiffWithinAt

end DefocusingNLS

end OAI
