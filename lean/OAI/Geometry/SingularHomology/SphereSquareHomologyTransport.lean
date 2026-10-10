import OAI.Dynamics.EntropyCounterexample.SphereDoublingCharts
import OAI.Geometry.SingularHomology.SkewProductHomology
import OAI.Dynamics.EntropyCounterexample.RawSpectrumFactor
import OAI.Dynamics.EntropyCounterexample.ClockModel
import OAI.Geometry.SingularHomology.HomologyConjugacy
import OAI.Dynamics.EntropyCounterexample.SpectralRadius

namespace OAI

noncomputable section

namespace Problem340

theorem rawSphereSquare_eq_conjugate_standard :
    rawSphereSquare = conjugateMap complexSphereHomeomorph.symm SphereDoubling.sphereMap := by
  funext z
  apply complexSphereHomeomorph.injective
  simpa only [conjugateMap, Homeomorph.symm_symm, Homeomorph.apply_symm_apply,
    rawSphereSquare] using (sphereDoubling_complexSphereHomeomorph z).symm

theorem rawSphereSquare_eigenvector_of_standard (n : ℕ) (c : ℝ)
    (v : RealSingularHomology n StandardSphere2) (hv : v ≠ 0)
    (heig : realHomologyMap n SphereDoubling.sphereMap
      SphereDoubling.continuous_sphereMap v = c • v) :
    ∃ w : RealSingularHomology n (OnePoint ℂ), w ≠ 0 ∧
      realHomologyMap n rawSphereSquare continuous_rawSphereSquare w = c • w := by
  obtain ⟨w, hw, he⟩ := realHomologyMap_eigenvector_conjugateMap n
    complexSphereHomeomorph.symm SphereDoubling.continuous_sphereMap c v hv heig
  exact ⟨w, hw, by simpa only [← rawSphereSquare_eq_conjugate_standard] using he⟩

abbrev StandardBase := StandardClock × StandardSphere2

def standardBaseSquare (x : StandardBase) : StandardBase :=
  (x.1, SphereDoubling.sphereMap x.2)

theorem continuous_standardBaseSquare : Continuous standardBaseSquare :=
  continuous_fst.prodMk (SphereDoubling.continuous_sphereMap.comp continuous_snd)

def baseHomeomorph : RawBase ≃ₜ StandardBase :=
  ClockModel.clockHomeomorph.prodCongr complexSphereHomeomorph

theorem rawBaseSquare_eq_conjugate_standard :
    rawBaseSquare = conjugateMap baseHomeomorph.symm standardBaseSquare := by
  funext x
  apply baseHomeomorph.injective
  change baseHomeomorph (rawBaseSquare x) =
    baseHomeomorph (baseHomeomorph.symm (standardBaseSquare (baseHomeomorph x)))
  rw [Homeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (sphereDoubling_complexSphereHomeomorph x.2).symm

theorem bddAbove_rawBaseSquare_of_standard
    (hB : BddAbove (homologyEigenvalueRadii standardBaseSquare continuous_standardBaseSquare)) :
    BddAbove (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare) := by
  apply hB.mono
  intro r hr
  rcases hr with ⟨n, a, b, u, v, huv, hu, hv, hr⟩
  obtain ⟨u', v', huv', hu', hv'⟩ := realHomologyMap_complexPair_conjugateMap n
    baseHomeomorph continuous_rawBaseSquare a b u v huv hu hv
  have heq : conjugateMap baseHomeomorph rawBaseSquare = standardBaseSquare := by
    rw [rawBaseSquare_eq_conjugate_standard]
    exact conjugateMap_symm baseHomeomorph.symm standardBaseSquare
  exact ⟨n, a, b, u', v', huv', by simpa only [heq] using hu',
    by simpa only [heq] using hv', hr⟩

end Problem340

end

end OAI
