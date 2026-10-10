import OAI.MeasureTheory.Falconer.Fourier.WeightedDistanceFourier
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem minimalMask_eq_source_product (d : PositiveDistanceData) (z : Plane × Plane) :
    d.minimalMask z = ∏ b ∈
      policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t,
      (descriptorSpatialMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b
        z.1 (sourceRadialUnit z.2 z.1) *
       descriptorSpatialMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b
        z.2 (sourceRadialUnit z.2 z.1)) := by
  exact (Finset.prod_mul_distrib).symm

theorem weightedDistance_fourier_integrable (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (r : ℝ) :
    Integrable (fun z : Plane × Plane => (d.spatialWeight z : ℂ) *
      Complex.exp ((r*dist z.1 z.2:ℝ)*Complex.I)) d.cellPair := by
  apply (integrable_const (1:ℝ)).mono
  · exact ((Complex.continuous_ofReal.measurable.comp d.measurable_spatialWeight).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [d.ae_cellPair_mem] with z hz
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (d.spatialWeight_nonneg hQ z),Complex.norm_exp,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,sub_zero,Real.exp_zero,mul_one,norm_one]
    exact d.spatialWeight_le_one hQ hs hz.1 hz.2

theorem weightedDistance_fourier_iterated (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (r : ℝ) :
    charFun d.weightedDistance r = (d.levelMass^(-2:ℤ):ℝ) •
      ∫ x in (d.Q.descendant d.X).carrier, ∫ y in (d.Q.descendant d.Y).carrier,
        (d.spatialWeight (x,y):ℂ)*Complex.exp ((r*dist x y:ℝ)*Complex.I) ∂d.ρ ∂d.ρ := by
  rw [d.weightedDistance_fourier hQ]
  congr 1
  exact integral_prod _ (d.weightedDistance_fourier_integrable hQ hs r)

end PositiveDistanceData

end PlanarFalconer

end OAI
