import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.CompletedProduct
import OAI.Geometry.PrescribedPotential.GlobalMetricEntries
import OAI.Geometry.PrescribedPotential.RegularityCutoffs
import OAI.Geometry.PrescribedPotential.RegularityJets
import OAI.Geometry.PrescribedPotential.SobolevDetDifferential

namespace OAI

/-! Nonlinear Remainder. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def regularityMetric (p : ι) (i j : Fin d) : Smooth A :=
  chartFunction (D.patch p).index (D.regularityCutoff p)
    (fun y => g.matrix (D.patch p).index (coordinateEquiv d y) i j)
    (contDiffOn_pi.mp (contDiffOn_pi.mp (metric_euclidean_smooth g (D.patch p).index) i) j)

def regularityInverseDet (p : ι) : Smooth A :=
  chartFunction (D.patch p).index (D.regularityCutoff p)
    (fun y => (g.matrix (D.patch p).index (coordinateEquiv d y)).det⁻¹)
    (inverseDet_euclidean_smooth g (D.patch p).index)

def regularityMatrix (k : ℕ) (p : ι) (u : D.localizers.Sobolev ((k : ℝ)+2)) :
    Matrix (Fin d) (Fin d) (D.localizers.Sobolev (k : ℝ)) :=
  fun i j => D.localizers.embed (k : ℝ) (D.regularityMetric p i j) +
    D.completedRegularityHessian k p i j u

def regularityErrorMatrix (k : ℕ) (p : ι) (v : EC d)
    (u : D.localizers.Sobolev ((k : ℝ)+2)) :
    Matrix (Fin d) (Fin d) (D.localizers.Sobolev (k : ℝ)) :=
  fun i j => D.completedRegularityError k p v i j u -
    D.localizers.embed (k : ℝ) (D.localizedDerivative p v (D.regularityMetric p i j))

def nonlinearRemainder (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (p : ι) (v : EC d)
    (u : D.localizers.Sobolev ((k : ℝ)+2)) : D.localizers.Sobolev (k : ℝ) :=
  D.product k hk (D.localizers.embed (k : ℝ) (D.regularityInverseDet p))
    (D.detDifferential k hk d (D.regularityMatrix k p u) (D.regularityErrorMatrix k p v u)) -
  D.product k hk (D.localizers.embed (k : ℝ)
    (D.localizedDerivative p v (D.regularityInverseDet p)))
    (D.determinant k hk d (D.regularityMatrix k p u))

lemma regularityMatrix_contDiff (k : ℕ) (p : ι) : ContDiff ℝ ∞ (D.regularityMatrix k p) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_const.add (D.completedRegularityHessian k p i j).contDiff

lemma regularityErrorMatrix_contDiff (k : ℕ) (p : ι) (v : EC d) :
    ContDiff ℝ ∞ (D.regularityErrorMatrix k p v) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (D.completedRegularityError k p v i j).contDiff.sub contDiff_const

lemma nonlinearRemainder_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (p : ι) (v : EC d) :
    ContDiff ℝ ∞ (D.nonlinearRemainder k hk p v) := by
  apply ContDiff.sub
  · exact (D.product k hk (D.localizers.embed (k : ℝ) (D.regularityInverseDet p))).contDiff.comp
      (((D.detDifferential_contDiff k hk d).comp (D.regularityMatrix_contDiff k p)).clm_apply
        (D.regularityErrorMatrix_contDiff k p v))
  · exact (D.product k hk (D.localizers.embed (k : ℝ)
      (D.localizedDerivative p v (D.regularityInverseDet p)))).contDiff.comp
      ((D.determinant_map_contDiff k hk d).comp (D.regularityMatrix_contDiff k p))

end GluingData
end GlobalElliptic

end
end

end OAI
