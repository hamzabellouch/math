import OAI.Analysis.LipschitzHilbert.Trees.SourceLocalLabelEnergy
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarFixedScaleEnergy

namespace OAI

/-! Local angular multiplicity controls vector-valued label sums with
no dependence on the number of frequency coordinates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem equal_length_label_vector_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (theta : ι → ℝ)
    (ell w cStar cEta CEta : ℝ) (hell : 0<ell) (hw : 0<w) (hcEta : 0<cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ theta (w/ell) M)
    (hspectrum : ∀ i k xi eta, planarAngularFourier (f i k) (xi,eta)≠0 →
      |xi+theta i*eta|≤cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∫ z, ‖∑ i, (WithLp.toLp 2 (fun k => f i k z) : EuclideanSpace ℂ κ)‖^2
      ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*∑ i,
        ∫ z, ‖(WithLp.toLp 2 (fun k => f i k z) : EuclideanSpace ℂ κ)‖^2
          ∂volume.prod volume := by
  have hi (i : ι) (k : κ) : Integrable (fun z => ‖f i k z‖^2) (volume.prod volume) :=
    ((f i k).memLp 2 (volume.prod volume)).integrable_norm_pow (by decide)
  have hs (k : κ) : Integrable (fun z => ‖∑ i, f i k z‖^2) (volume.prod volume) := by
    have h := ((∑ i, f i k : SchwartzMap (ℝ×ℝ) ℂ).memLp 2
      (volume.prod volume)).integrable_norm_pow (by decide : 2 ≠ 0)
    simpa only [sum_apply] using h
  simp only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_sum,Finset.sum_apply]
  rw [integral_finsetSum _ (fun k _ => hs k)]
  calc
    _ ≤ ∑ k, (((2*Q+1)*M:ℕ):ℝ)*∑ i,
        ∫ z, ‖f i k z‖^2 ∂volume.prod volume := by
      apply Finset.sum_le_sum
      intro k _
      exact equal_length_label_energy (fun i => f i k) theta ell w cStar cEta CEta
        hell hw hcEta M Q hQ hmultiplicity (fun i => hspectrum i k)
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun k _ => hi i k)).symm

end LipschitzHilbert

end

end OAI
