import OAI.Geometry.SurfaceImmersion.Geometry.CompactNormalTriple
import OAI.Geometry.SurfaceImmersion.Geometry.ActualSecondFormFrame

namespace OAI

/-! Normal frames and scaled second-form coefficients are smooth functions of
exactly the five derivative components retained by the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

abbrev BoundaryProfile := Fin 5 → Vec

def profileNormalPart (J : BoundaryProfile) : Vec :=
  realNormalPart (J 0) (J 1) (J 2)

def profilePreferred (J : BoundaryProfile) : Vec :=
  VelocityFrame.normalize (profileNormalPart J)

def profileComplement (J : BoundaryProfile) : Vec :=
  unitPerp (J 0) (J 1) (profilePreferred J)

def regularBoundaryProfiles : Set BoundaryProfile :=
  {J | gramDet (J 0) (J 1) ≠ 0 ∧ profileNormalPart J ≠ 0}

/-- The coordinates are `S`, `D`, `N`, and `z L`. The xx entry in the input
has already been multiplied by the fast scale. -/
def profileCoefficients (J : BoundaryProfile) : Fin 4 → ℝ :=
  ![Real.sqrt (profileNormalPart J ⬝ᵥ profileNormalPart J),
    J 3 ⬝ᵥ profilePreferred J, J 3 ⬝ᵥ profileComplement J,
    J 4 ⬝ᵥ profileComplement J]

def profileGeometry (J : BoundaryProfile) : (Vec × Vec) × (Fin 4 → ℝ) :=
  ((profilePreferred J,profileComplement J),profileCoefficients J)

lemma contDiffAt_profileNormalPart {J : BoundaryProfile}
    (hJ : gramDet (J 0) (J 1) ≠ 0) : ContDiffAt ℝ ∞ profileNormalPart J := by
  exact contDiffAt_realNormalPart
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 2 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt hJ

lemma contDiffAt_profilePreferred {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profilePreferred J :=
  normalize_smoothAt (contDiffAt_profileNormalPart hJ.1) hJ.2

lemma contDiffAt_profileComplement {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileComplement J := by
  have hn := realNormalPart_perp (J 0) (J 1) (J 2) hJ.1
  exact contDiffAt_unitPerp
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (contDiffAt_profilePreferred hJ) hJ.1 (normalize_nonzero hJ.2)
    (dot_normalize_zero hn.1) (dot_normalize_zero hn.2)

lemma isOpen_regularBoundaryProfiles : IsOpen regularBoundaryProfiles := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : BoundaryProfile => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_profileNormalPart hJ.1).continuousAt.eventually_ne hJ.2)

lemma contDiffAt_profileCoefficients {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileCoefficients J := by
  have hslot (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : BoundaryProfile => K i) J :=
    (ContinuousLinearMap.proj i : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
  have hdot {f g : BoundaryProfile → Vec}
      (hf : ContDiffAt ℝ ∞ f J) (hg : ContDiffAt ℝ ∞ g J) :
      ContDiffAt ℝ ∞ (fun K => f K ⬝ᵥ g K) J :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hf i).mul (contDiffAt_pi.mp hg i))
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (hdot (contDiffAt_profileNormalPart hJ.1)
      (contDiffAt_profileNormalPart hJ.1)).sqrt (dot_self_pos hJ.2).ne'
  · exact hdot (hslot 3) (contDiffAt_profilePreferred hJ)
  · exact hdot (hslot 3) (contDiffAt_profileComplement hJ)
  · exact hdot (hslot 4) (contDiffAt_profileComplement hJ)

lemma contDiffAt_profileGeometry {J : BoundaryProfile}
    (hJ : J ∈ regularBoundaryProfiles) : ContDiffAt ℝ ∞ profileGeometry J :=
  ((contDiffAt_profilePreferred hJ).prodMk (contDiffAt_profileComplement hJ)).prodMk
    (contDiffAt_profileCoefficients hJ)

/-- Uniformly transfer all five derivative estimates to the actual normal
frame and its scaled coefficients on a compact family of regular profiles. -/
theorem compact_boundary_profile_stability {K : Set BoundaryProfile}
    (hK : IsCompact K) (hregular : K ⊆ regularBoundaryProfiles) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ K, ∀ H : BoundaryProfile,
      ‖H-J‖ < δ → H ∈ regularBoundaryProfiles ∧
        ‖profileGeometry H-profileGeometry J‖ < ε := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open
    isOpen_regularBoundaryProfiles hregular
  have hc : ContinuousOn profileGeometry (Metric.cthickening r K) :=
    fun J hJ => (contDiffAt_profileGeometry (hsub hJ)).continuousAt.continuousWithinAt
  have hu := hK.cthickening.uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro J hJ H hHJ
  have hH : H ∈ Metric.cthickening r K :=
    Metric.thickening_subset_cthickening r K
      (Metric.mem_thickening_iff.mpr ⟨J,hJ,by
        simpa only [dist_eq_norm] using hHJ.trans_le (min_le_left r d)⟩)
  refine ⟨hsub hH,?_⟩
  have hJ' : J ∈ Metric.cthickening r K := Metric.self_subset_cthickening K hJ
  simpa only [dist_eq_norm] using hclose H hH J hJ'
    (by simpa only [dist_eq_norm] using hHJ.trans_le (min_le_right r d))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
