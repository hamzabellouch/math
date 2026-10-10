import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import OAI.Analysis.CoulombRadii.Packets.CoulombKernel

namespace OAI

/-!
# The Coulomb fundamental solution with finite smoothness

The manufactured planar well in the unit-charge paper has bounded continuous
derivatives through a finite order. Its density synthesis therefore needs
the fundamental-solution identity for compactly supported C² functions.
This extends the smooth-test identity by the same regularized
kernel argument, using only two integrations by parts.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem integral_mul_laplacian_C2 (f phi : Position → ℝ)
    (hf : ContDiff ℝ 2 f) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, f x * coordinateLaplacian phi x) = ∫ x, coordinateLaplacian f x * phi x := by
  have hp (g : Position → ℝ) (hg : ContDiff ℝ 2 g) (v : Position) :
      ContDiff ℝ 1 (dirPartial g v) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const
  have hpp (g : Position → ℝ) (hg : ContDiff ℝ 2 g) (v : Position) :
      Continuous (dirPartial (dirPartial g v) v) :=
    (((hp g hg v).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).clm_apply
      contDiff_const).continuous
  have hpc (v : Position) : HasCompactSupport (dirPartial phi v) :=
    NeutralAtom.hasCompactSupport_partial hc v
  have hppc (v : Position) : HasCompactSupport (dirPartial (dirPartial phi v) v) :=
    NeutralAtom.hasCompactSupport_partial (hpc v) v
  have hleft (v : Position) : Integrable (fun x => f x * dirPartial (dirPartial phi v) v x) :=
    (hf.continuous.mul (hpp phi hphi v)).integrable_of_hasCompactSupport (hppc v).mul_left
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x * phi x) :=
    ((hpp f hf v).mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x * dirPartial phi v x) :=
    ((hp f hf v).continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfg (v : Position) : Integrable (fun x => f x * dirPartial phi v x) :=
    (hf.continuous.mul (hp phi hphi v).continuous).integrable_of_hasCompactSupport
      (hpc v).mul_left
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x * phi x) :=
    ((hp f hf v).continuous.mul hphi.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hby (v : Position) :
      (∫ x, f x * dirPartial (dirPartial phi v) v x) =
        ∫ x, dirPartial (dirPartial f v) v x * phi x := by
    calc
      _ = -(∫ x, dirPartial f v x * dirPartial phi v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x _ => hf.differentiable (by norm_num) x)
          (fun x _ => (hp phi hphi v).differentiable (by norm_num) x)
      _ = _ := by
        have h : (∫ x, dirPartial f v x * dirPartial phi v x) =
            -(∫ x, dirPartial (dirPartial f v) v x * phi x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x _ => (hp f hf v).differentiable (by norm_num) x)
            (fun x _ => hphi.differentiable (by norm_num) x)
        rw [h, neg_neg]
  have hphi_eq (x : Position) : coordinateLaplacian phi x =
      ∑ a : Fin 3, dirPartial (dirPartial phi (axis a)) (axis a) x :=
    NeutralAtom.coordinateLaplacian_eq_partials hphi.contDiffAt
  have hf_eq (x : Position) : coordinateLaplacian f x =
      ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x :=
    NeutralAtom.coordinateLaplacian_eq_partials hf.contDiffAt
  simp_rw [hphi_eq, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hleft (axis a))]
  simp_rw [hby]
  rw [← integral_finsetSum _ (fun a _ => hright (axis a))]
  simp_rw [hf_eq, Finset.sum_mul]

theorem coulomb_laplacian_C2 (phi : Position → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ x, Coulomb.coulombKernel x * coordinateLaplacian phi x) =
      -(4 * Real.pi * phi 0) := by
  let epsilon : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hepsilon (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have hlim : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hl := NeutralAtom.regularizedKernel_integral_tendsto hepsilon hlim
    (NeutralAtom.continuous_coordinateLaplacian hphi)
    (NeutralAtom.hasCompactSupport_coordinateLaplacian hc)
  have hr := (NeutralAtom.regularizedCharge_tendsto_dirac hepsilon hlim hphi.continuous hc).neg
  have heq : (fun n => ∫ x, NeutralAtom.regularizedKernel (epsilon n) x *
      coordinateLaplacian phi x) =
      (fun n => -(∫ x, NeutralAtom.regularizedCharge (epsilon n) x * phi x)) := by
    funext n
    rw [integral_mul_laplacian_C2 _ _
      ((NeutralAtom.contDiff_regularizedKernel (hepsilon n).ne').of_le (by simp)) hphi hc]
    simp_rw [NeutralAtom.laplacian_regularizedKernel (hepsilon n).ne', neg_mul, integral_neg]
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem coulomb_translated_laplacian_C2 (phi : Position → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (a : Position) :
    (∫ x, Coulomb.coulombKernel (x - a) * coordinateLaplacian phi x) =
      -(4 * Real.pi * phi a) := by
  have ht : ContDiff ℝ 2 (fun z => phi (z + a)) := hphi.comp (contDiff_id.add contDiff_const)
  have htc : HasCompactSupport (fun z => phi (z + a)) :=
    hc.comp_homeomorph (Homeomorph.addRight a)
  have h := coulomb_laplacian_C2 _ ht htc
  simp only [NeutralAtom.coordinateLaplacian_translate, zero_add] at h
  rw [← integral_add_right_eq_self
    (fun x => Coulomb.coulombKernel (x - a) * coordinateLaplacian phi x) a]
  simpa only [add_sub_cancel_right] using h

def manufacturedCharge (V : Position → ℝ) (x : Position) : ℝ :=
  coordinateLaplacian V x / (4 * Real.pi)

theorem manufacturedCharge_integral_zero (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hc : HasCompactSupport V) : (∫ x, manufacturedCharge V x) = 0 := by
  have h := integral_mul_laplacian_C2 (fun _ => (1 : ℝ)) V contDiff_const hV hc
  have hconst (x : Position) : coordinateLaplacian (fun _ => (1 : ℝ)) x = 0 := by
    simp [coordinateLaplacian]
  simp only [one_mul, hconst, zero_mul, integral_zero] at h
  simp only [manufacturedCharge, integral_div, h, zero_div]

/-- Exact Green identity, with the sign for an attractive positive density. -/
theorem manufacturedCharge_potential (V : Position → ℝ) (hV : ContDiff ℝ 2 V)
    (hc : HasCompactSupport V) (y : Position) :
    -(∫ x, Coulomb.coulombKernel (y - x) * manufacturedCharge V x) = V y := by
  have h := coulomb_translated_laplacian_C2 V hV hc y
  have heq : (fun x => Coulomb.coulombKernel (y - x) * manufacturedCharge V x) =
      (fun x => (Coulomb.coulombKernel (x - y) * coordinateLaplacian V x) / (4 * Real.pi)) := by
    funext x
    dsimp [manufacturedCharge, Coulomb.coulombKernel]
    rw [norm_sub_rev]
    ring
  rw [heq, integral_div, h]
  field_simp

end ContinuumCoulomb

end

end OAI
