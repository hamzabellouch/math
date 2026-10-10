import OAI.Analysis.Mahler.EuclideanSpecialMap
import OAI.Analysis.Mahler.StripRegularLevels

namespace OAI

namespace SymmetricMahler
open Set Filter
open scoped Topology
variable {n N : ℕ}

noncomputable def euclideanRealCoordinates : Mahler.ComplexEuclidean n ≃L[ℝ]
    ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).trans complexRealEquiv

lemma euclideanTau_eq_real (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Mahler.ComplexEuclidean n) :
    Mahler.tau (euclideanSpecialMap A m) z = stripTau A m (euclideanRealCoordinates z) := by
  rw [euclideanSpecialTau,specialTau_eq_stripTau]
  rfl

lemma euclideanDomain_eq_real (A : Matrix (Fin N) (Fin n) ℝ) :
    euclideanStripDomain A = euclideanRealCoordinates ⁻¹' stripDomain A := by
  ext z
  change euclideanCoordinates z ∈ complexStripDomain A ↔ _
  rw [complexStripDomain_eq_preimage]
  rfl

/-- Every positive level remains regular in the exact Euclidean coordinates
used by the mass theorem. This uses the actual special map, without Sard. -/
theorem euclideanSpecial_positive_regular (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) {z : Mahler.ComplexEuclidean n}
    (hz : z ∈ euclideanStripDomain A) (hlevel : Mahler.tau (euclideanSpecialMap A m) z = R) :
    Function.Surjective (fderiv ℝ (Mahler.tau (euclideanSpecialMap A m)) z) := by
  have hzr : euclideanRealCoordinates z ∈ stripDomain A := by
    simpa only [euclideanDomain_eq_real,mem_preimage] using hz
  have hder := (differentiableAt_stripTau A m hzr).hasFDerivAt.comp z
    euclideanRealCoordinates.hasFDerivAt
  have he : Mahler.tau (euclideanSpecialMap A m) =
      fun w => stripTau A m (euclideanRealCoordinates w) := funext (euclideanTau_eq_real A m)
  have hder' : HasFDerivAt (Mahler.tau (euclideanSpecialMap A m))
      ((fderiv ℝ (stripTau A m) (euclideanRealCoordinates z)).comp
        euclideanRealCoordinates.toContinuousLinearMap) z := by
    simpa only [Function.comp_def,← euclideanTau_eq_real] using! hder
  rw [hder'.fderiv]
  have hr := stripTau_positive_regular A hA hm hR hzr
    (by simpa only [euclideanTau_eq_real] using hlevel)
  exact hr.comp euclideanRealCoordinates.surjective

end SymmetricMahler

end OAI
