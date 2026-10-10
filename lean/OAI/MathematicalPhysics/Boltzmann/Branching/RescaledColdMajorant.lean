import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedNonaxialLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds

namespace OAI

/-! # The actual cold dilation is bounded by the selected core and two remainders -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.rescaled_cold_majorant {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (z : KineticPhase) (ht : r*z.1.1 ∈ Ioc 0 T) :
    ENNReal.ofReal (r*(H q z.2*F.coldTotal
      (r*z.1.1,(JetPeriodicDatum.spatialMap (r • z.1.2),z.2)))) ≤
      selectedCoreDensity r s₀ η K α γ d₀ N z+
      selectedRemainderDensity r s₀ η K α γ d₀ N z+
      ENNReal.ofReal (r*(H q z.2*F.escapedTotal ((r*z.1.1,r • z.1.2),z.2))) := by
  classical
  by_cases hmain : ∃ i, z.1 ∈ mainCoreRegion s₀ η r N i
  · obtain ⟨i,hi⟩ := hmain
    rw [selectedCoreDensity_eq hs₀ hsmax hη hηmax K α γ d₀ hi,
      selectedRemainderDensity_eq hs₀ hsmax hη hηmax K α γ d₀ hi,
      copyCoreDensity_eq hr.ne']
    have hb := F.cold_free_majorant_at_main hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hT hTmax ((r*z.1.1,r • z.1.2),z.2) ht i hi.1 hi.2.2
    let a := JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η i.annulus)
      (d₀*JetGeometry.jetScale s₀ η i.annulus^10) (r*z.1.1) i.positive
      (WeightedTranslation.shift (displacement i.lattice)
        (JetPeriodicDatum.spatialMap (r • z.1.2),z.2))
    let b := JetRemainderSheet.remainder η K α γ (JetGeometry.jetScale s₀ η i.annulus)
      (d₀*JetGeometry.jetScale s₀ η i.annulus^10) (r*z.1.1) i.positive
      (JetPeriodicDatum.spatialMap (r • z.1.2)-displacement i.lattice) z.2
    let c := H q z.2*F.escapedTotal ((r*z.1.1,r • z.1.2),z.2)
    change ENNReal.ofReal (r*_ ) ≤ ENNReal.ofReal r*ENNReal.ofReal a+
      ENNReal.ofReal r*ENNReal.ofReal b+ENNReal.ofReal (r*c)
    change H q z.2*F.coldTotal _ ≤ a+b+c at hb
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb hr.le)).trans
    rw [mul_add,mul_add]
    exact (ENNReal.ofReal_add_le.trans
      (add_le_add ENNReal.ofReal_add_le le_rfl)).trans_eq (by
        rw [ENNReal.ofReal_mul hr.le,ENNReal.ofReal_mul hr.le])
  · have he := F.coldTotal_eq_escaped_of_no_main hs₀ hsmax hη hηmax hK hd₀.le hq hT
      ((r*z.1.1,r • z.1.2),z.2) (fun i hi hx =>
        hmain ⟨i,hi,ht.2.trans hTmax,hx⟩)
    rw [he]
    exact le_add_of_nonneg_left (by positivity)

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
