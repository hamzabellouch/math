import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularMatching
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeLowAngularSpectrum

namespace OAI

/-! High-angular exclusion for the actual outgoing matching determinant. -/

open Matrix
namespace DefocusingNLS

theorem free_high_angular_nonzero (ell : ℕ) (b Z : ℝ) (z : ℂ)
    (hell : 4 ≤ ell) (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000)
    (hz : -(1/32 : ℝ) ≤ z.re) : spectralSlowDeterminant ell b Z z ≠ 0 := by
  let qp := spectralQ ell 1 b z
  let qm := spectralQ ell (-1) b z
  have hq (h : ℝ) : -1 < (spectralQ ell h b z).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hZ0 : Z ≠ 0 := by linarith
  intro hdet
  obtain ⟨c,hc⟩ := matchingColumnDeterminant_eq_zero_imp_smul
    (slowBoundaryColumn qp (ell+6) (Complex.I*Z))
    (slowBoundaryColumn qm (ell+6) (-Complex.I*Z))
    (slowBoundaryColumn_ne_zero qp (ell+6) (Complex.I*Z) (hq 1) (by simp) (by simpa using hZ0)) hdet
  rw [slowBoundaryColumn_eq_jet qp (ell+6) (Complex.I*Z) (hq 1) (by simp) (by simpa using hZ0),
    slowBoundaryColumn_eq_jet qm (ell+6) (-Complex.I*Z) (hq (-1)) (by simp) (by simpa using hZ0)] at hc
  have hH := congrFun hc 0
  have hD := congrFun hc 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul,neg_neg,
    neg_mul] at hH hD
  have hD' : deriv (regularizedSlowSolution qm (ell+6)) (Complex.I*Z) =
      c*deriv (regularizedSlowSolution qp (ell+6)) (-Complex.I*Z) := by
    simpa only [neg_mul,mul_neg,neg_inj] using hD
  have hσ (h : ℝ) : -(1/32 : ℝ) ≤ 3-((((ell+5 : ℕ) : ℂ)+1)/2-spectralQ ell h b z).re := by
    simp only [Complex.sub_re,Complex.div_re,Complex.add_re,Complex.natCast_re,
      spectralQ_re]
    norm_num
    linarith
  apply highAngular_matched_jets_impossible qp qm (ell+5) Z (hq 1) (hq (-1)) (by omega)
    (hσ 1) (hσ (-1)) hZ hZ' c
  · simpa only [show ell+5+1=ell+6 by omega,neg_mul] using hH
  · simpa only [show ell+5+1=ell+6 by omega] using hD'

theorem free_high_angular_nonzero_on_disk (ell : ℕ) (b Z : ℝ) (z : ℂ)
    (hell : 4 ≤ ell) (hD : (b,Z) ∈ freeMatchingDisk)
    (hz : -(1/32 : ℝ) ≤ z.re) : spectralSlowDeterminant ell b Z z ≠ 0 := by
  obtain ⟨_,hZ⟩ := freeMatchingDisk_subset_certificate_box hD
  obtain ⟨hlo,hhi⟩ := abs_le.mp hZ
  exact free_high_angular_nonzero ell b Z z hell (by linarith) (by linarith) hz

end DefocusingNLS

end OAI
