import OAI.Analysis.FiniteFactor.CrossedProduct.Transport
import OAI.Analysis.FiniteFactor.CrossedProduct.ScalarCommutant

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

def sourceCommutantRotation (θ : SourceCoordinate → ℝ) (n : ℤ) := sourceTransport θ n n

theorem sourceCommutantRotation_star (θ : SourceCoordinate → ℝ) (n : ℤ) :
    star (sourceCommutantRotation θ n) = sourceCommutantRotation θ (-n) :=
  sourceTransport_star θ n n

theorem sourceCommutantRotation_pi (θ : SourceCoordinate → ℝ) (n : ℤ)
    (g : SourceBaseFunction) :
    sourceCommutantRotation θ n * sourcePi θ g = sourcePi θ g * sourceCommutantRotation θ n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourcePi_apply_ae θ g f)
  filter_upwards [sourceTransport_apply_ae θ n n (sourcePi θ g f),
    sourcePi_apply_ae θ g (sourceTransport θ n n f), sourceTransport_apply_ae θ n n f,
    ht] with z h1 h2 h3 h4
  change (sourceTransport θ n n (sourcePi θ g f)) z = (sourcePi θ g (sourceTransport θ n n f)) z
  rw [h1,h2,h3,h4]
  have he : sourcePiSymbol θ g (sourceTransportIndex θ n n z) = sourcePiSymbol θ g z := by
    unfold sourcePiSymbol sourceTransportIndex
    dsimp only
    rw [coordinateRotate_add]
    congr 2
    omega
  rw [he]

theorem sourceTransport_shift (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceTransport θ n m * sourceShift SourceCoordinate =
      sourceShift SourceCoordinate * sourceTransport θ n m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n m).quasiMeasurePreserving.ae
    (sourceShift_apply_ae f)
  have hs := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ n m f)
  filter_upwards [sourceTransport_apply_ae θ n m (sourceShift SourceCoordinate f),
    sourceShift_apply_ae (sourceTransport θ n m f), ht, hs] with z h1 h2 h3 h4
  change (sourceTransport θ n m (sourceShift SourceCoordinate f)) z =
    (sourceShift SourceCoordinate (sourceTransport θ n m f)) z
  rw [h1,h2,h3,h4]
  congr 1
  apply Prod.ext
  · rfl
  · dsimp [sourceTransportIndex, sourceShiftIndex]; omega

theorem sourceCommutantRotation_mem (θ : SourceCoordinate → ℝ) (n : ℤ) :
    sourceCommutantRotation θ n ∈ StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ)) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro A hA
  rcases hA with hA | ⟨g,rfl⟩
  · obtain rfl : A = sourceShift SourceCoordinate := hA
    refine ⟨(sourceTransport_shift θ n n).symm, ?_⟩
    have hs := congrArg star (sourceTransport_shift θ (-n) (-n))
    have he : star (sourceTransport θ (-n) (-n)) = sourceTransport θ n n := by
      rw [sourceTransport_star]; simp
    simpa only [star_mul, he, sourceCommutantRotation] using hs
  · exact ⟨(sourceCommutantRotation_pi θ n g).symm, by
      rw [sourcePi_star]
      exact (sourceCommutantRotation_pi θ n (sourceBaseStar g)).symm⟩

theorem sourceAlgebra_commutes_rotation (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (n : ℤ) :
    sourceCommutantRotation θ n * H = H * sourceCommutantRotation θ n := by
  change H ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))) at hH
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hH _
    (sourceCommutantRotation_mem θ n)).1

end
end FiniteFactor

end OAI
