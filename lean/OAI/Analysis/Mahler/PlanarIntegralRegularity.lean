import OAI.Analysis.Mahler.PlanarDensity
import OAI.Analysis.Mahler.CompactIntegral

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The fixed-interval parametrization of the entire vertical segment. -/
def segmentPoint (p : ℂ × ℝ) : ℂ := (p.1.re : ℂ) + (p.2 * p.1.im : ℝ) * I

def segmentParameterDomain : Set (ℂ × ℝ) := segmentPoint ⁻¹' MahlerConformal.Omega

def planarSegmentDomain : Set ℂ := CompactIntegral.tube segmentParameterDomain

lemma contDiff_segmentPoint : ContDiff ℝ ∞ segmentPoint := by
  exact (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_fst)).add
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_snd.mul (Complex.imCLM.contDiff.comp contDiff_fst))).mul contDiff_const)

lemma isOpen_segmentParameterDomain : IsOpen segmentParameterDomain :=
  MahlerConformal.isOpen_Omega.preimage contDiff_segmentPoint.continuous

lemma isOpen_planarSegmentDomain : IsOpen planarSegmentDomain :=
  CompactIntegral.isOpen_tube isOpen_segmentParameterDomain

/-- The exact original integral under t=s*xi; the equality also holds at xi=0
and for negative xi, using oriented interval integration. -/
theorem planarPrimitive_eq_fixedIntegral (m : ℕ) (u : ℂ) :
    planarPrimitive m u.re u.im =
      u.im * ∫ s in Icc (0 : ℝ) 1, planarDensity m (segmentPoint (u,s)) := by
  have h := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => planarDensity m ((u.re : ℂ)+(t : ℂ)*I)) (a := 0) (b := 1) u.im
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  simpa [planarPrimitive,segmentPoint,smul_eq_mul] using h.symm

/-- The density on the fixed interval is jointly smooth on its actual open domain. -/
lemma contDiffOn_segmentDensity (m : ℕ) :
    ContDiffOn ℝ ∞ (fun p => planarDensity m (segmentPoint p)) segmentParameterDomain := by
  intro p hp
  exact ((contDiffAt_planarDensity m hp).comp p contDiff_segmentPoint.contDiffAt).contDiffWithinAt

/-- Joint C∞ regularity of the primitive on the open
segment-containment domain, including its real diameter. -/
theorem contDiffOn_planarPrimitive_segment (m : ℕ) :
    ContDiffOn ℝ ∞ (fun u : ℂ => planarPrimitive m u.re u.im) planarSegmentDomain := by
  have hi := CompactIntegral.contDiffOn_integral isOpen_segmentParameterDomain
    (contDiffOn_segmentDensity m)
  have him : ContDiffOn ℝ ∞ (fun u : ℂ => u.im) planarSegmentDomain :=
    Complex.imCLM.contDiff.contDiffOn
  exact (him.mul hi).congr (fun u _ => planarPrimitive_eq_fixedIntegral m u)

end SymmetricMahler

end OAI
