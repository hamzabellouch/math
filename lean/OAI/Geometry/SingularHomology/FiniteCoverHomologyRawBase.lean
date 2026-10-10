import OAI.Geometry.SingularHomology.FiniteCoverHomology
import OAI.Dynamics.EntropyCounterexample.RawBaseGoodCover

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.FiniteCoverHomology

theorem rawBase_finiteHomology
    [QuasiIso (SingularSmallChains.inclusion CoordinateGoodCover.rawBaseGoodCover.carrier)] :
    FiniteGoodCover.FiniteHomology (realSingularChainComplex RawBase) :=
  finiteHomology_of_goodCover CoordinateGoodCover.rawBaseGoodCover

theorem rawBase_homologyEigenvalueRadii_bddAbove
    [QuasiIso (SingularSmallChains.inclusion CoordinateGoodCover.rawBaseGoodCover.carrier)] :
    BddAbove (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare) :=
  bddAbove_homologyEigenvalueRadii_of_goodCover
    CoordinateGoodCover.rawBaseGoodCover rawBaseSquare continuous_rawBaseSquare

theorem rawBase_homology_pairRadii_bddAbove
    [QuasiIso (SingularSmallChains.inclusion CoordinateGoodCover.rawBaseGoodCover.carrier)] :
    BddAbove (⋃ n, PolynomialSpectrum.pairRadii
      (realHomologyMap n rawBaseSquare continuous_rawBaseSquare)) := by
  have h := rawBase_homologyEigenvalueRadii_bddAbove
  simpa only [homologyEigenvalueRadii, PolynomialSpectrum.pairRadii,
    Set.iUnion_ofPred] using h

end Problem340.FiniteCoverHomology

end

end OAI
