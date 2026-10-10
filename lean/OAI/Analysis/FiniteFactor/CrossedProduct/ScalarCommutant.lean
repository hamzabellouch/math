import OAI.Analysis.FiniteFactor.CrossedProduct.MultiplicationAdjoint

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Scalar base multiplication, independent of the fiber coordinate. -/
def sourceScalar (g : SourceBaseFunction) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  sourcePi (fun _ => 0) g

theorem sourceScalar_star (g : SourceBaseFunction) :
    star (sourceScalar g) = sourceScalar (sourceBaseStar g) :=
  sourcePi_star _ _

theorem sourceShift_apply_ae (f : SourceHilbert SourceCoordinate) :
    sourceShift SourceCoordinate f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => f (sourceShiftIndex z) :=
  Lp.coeFn_compMeasurePreserving f (sourceShiftIndex_preserving _)

theorem sourceScalar_shift_commute (g : SourceBaseFunction) :
    sourceScalar g * sourceShift SourceCoordinate =
      sourceShift SourceCoordinate * sourceScalar g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hg := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourcePi_apply_ae (fun _ => 0) g f)
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g (sourceShift SourceCoordinate f),
    sourceShift_apply_ae f, sourceShift_apply_ae (sourceScalar g f), hg] with z h1 h2 h3 h4
  change (sourcePi (fun _ => 0) g (sourceShift SourceCoordinate f)) z =
    (sourceShift SourceCoordinate (sourceScalar g f)) z
  rw [h1, h2, h3]
  change _ = (sourcePi (fun _ => 0) g f) (sourceShiftIndex z)
  rw [h4]
  have he : sourcePiSymbol (fun _ => 0) g z =
      sourcePiSymbol (fun _ => 0) g (sourceShiftIndex z) := by
    unfold sourcePiSymbol
    congr 1
    funext i
    simp [coordinateRotate, sourceShiftIndex]
  rw [he]

/-- The scalar multipliers commute with the generators and their adjoints. -/
theorem sourceScalar_mem_generator_commutant (θ : SourceCoordinate → ℝ)
    (g : SourceBaseFunction) :
    sourceScalar g ∈ StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ)) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro A hA
  rcases hA with hA | ⟨h, rfl⟩
  · obtain rfl : A = sourceShift SourceCoordinate := hA
    refine ⟨(sourceScalar_shift_commute g).symm, ?_⟩
    have hs := congrArg star (sourceScalar_shift_commute (sourceBaseStar g))
    have hg : star (sourceScalar (sourceBaseStar g)) = sourceScalar g := by
      rw [← sourceScalar_star, star_star]
    simpa only [star_mul, hg] using hs
  · exact ⟨sourcePi_commute θ _ h g, by
      rw [sourcePi_star]
      exact sourcePi_commute θ _ (sourceBaseStar h) g⟩

/-- The commutation holds for every element of the actual double commutant. -/
theorem sourceAlgebra_commutes_scalar (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (g : SourceBaseFunction) :
    sourceScalar g * H = H * sourceScalar g := by
  change H ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))) at hH
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hH _
    (sourceScalar_mem_generator_commutant θ g)).1

end
end FiniteFactor

end OAI
