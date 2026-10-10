import OAI.Analysis.Mahler.EuclideanSpecialMap
import OAI.Analysis.Mahler.SpecialMassBridge

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set MeasureTheory
open scoped Topology ENNReal
variable {n N : ℕ}

lemma euclideanSpecial_jacobian (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : Mahler.ComplexEuclidean n} (hz : z ∈ euclideanStripDomain A) :
    Mahler.jacobian (euclideanSpecialMap A m) z
      (fun i => EuclideanSpace.single i (1 : ℂ)) =
        specialJacobianMatrix A m (euclideanCoordinates z) := by
  ext j k
  have hj := hasFDerivAt_pi.mp (hasFDerivAt_specialMap A m hz) j
  have hd := hj.comp z euclideanCoordinates.hasFDerivAt
  change HasFDerivAt (euclideanSpecialMap A m j) _ z at hd
  change fderiv ℂ (euclideanSpecialMap A m j) z (EuclideanSpace.single k 1) = _
  rw [hd.fderiv]
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    euclideanCoordinates,PiLp.coe_continuousLinearEquiv,PiLp.ofLp_single] using!
      specialJacobianMatrix_derivative A m (euclideanCoordinates z) j k

/-- The complex Hessian has precisely the
n! times Gram-determinant density used in the finite-strip mass bridge. -/
theorem euclideanSpecial_massDensity (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : Mahler.ComplexEuclidean n} (hz : z ∈ euclideanStripDomain A) :
    Mahler.massDensity (euclideanSpecialMap A m) z =
      (Nat.factorial n : ℝ) * specialGramDet A m (euclideanCoordinates z) := by
  unfold Mahler.massDensity Mahler.sourceHessian
  rw [Matrix.det_transpose,Mahler.complexHessian_energy_eq_gram_of_open
    (fun i => EuclideanSpace.single i (1 : ℂ))
    ((isOpen_complexStripDomain A).preimage euclideanCoordinates.continuous) hz
    (differentiableOn_euclideanSpecialMap A m),euclideanSpecial_jacobian A m hz]
  rfl

/-- Measure transport converts the complex Euclidean mass integral
to the real-coordinate integral. The integrands and domains are
those of the general mass theorem and the finite-strip construction. -/
theorem euclideanSpecial_massIntegral
    (hvolume : MeasurePreserving (euclideanCoordinates (n := n)))
    (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    Mahler.massIntegral (euclideanStripDomain A) (euclideanSpecialMap A m) =
      ∫⁻ z in specialSublevel A m,
        ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m z) := by
  have hset : euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < 1} =
      euclideanCoordinates ⁻¹' specialSublevel A m := by
    ext z
    simp only [euclideanStripDomain,specialSublevel,euclideanSpecialTau,
      mem_inter_iff,Set.mem_preimage,mem_ofPred_eq]
  have hmeas : MeasurableSet (euclideanStripDomain A ∩
      {z | Mahler.tau (euclideanSpecialMap A m) z < 1}) := by
    rw [hset,specialSublevel_eq_preimage]
    exact (isOpen_stripSublevel A m).measurableSet.preimage
      (complexRealEquiv.continuous.comp euclideanCoordinates.continuous).measurable
  unfold Mahler.massIntegral
  calc
    _ = ∫⁻ z in euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < 1},
        ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m (euclideanCoordinates z)) := by
      apply setLIntegral_congr_fun hmeas
      intro z hz
      dsimp only
      rw [euclideanSpecial_massDensity A m hz.1]
    _ = _ := by
      rw [hset]
      simpa using! hvolume.setLIntegral_comp_preimage_emb
        euclideanCoordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun z => ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m z))
        (specialSublevel A m)

end SymmetricMahler

end OAI
