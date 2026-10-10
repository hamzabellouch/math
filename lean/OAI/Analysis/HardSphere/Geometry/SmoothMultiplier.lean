import Mathlib
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath
import OAI.Analysis.HardSphere.Geometry.CoordinateLine

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
structure SmoothMultiplier (N : ℕ) (L : Length) where
  toFun : Configuration N L → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ toFun (project N L X))
  memLp_top : MemLp toFun ∞ (volume : Measure (Configuration N L))
  partial_memLp_top : ∀ p : Direction N, MemLp (coordDerivative N L toFun p) ∞ volume

def SmoothMultiplier.mul {N : ℕ} {L : Length} (f g : SmoothMultiplier N L) :
    SmoothMultiplier N L where
  toFun := f.toFun * g.toFun
  smooth := f.smooth.mul g.smooth
  memLp_top := f.memLp_top.mul g.memLp_top
  partial_memLp_top := by
    intro p
    rw [coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp))]
    exact (f.memLp_top.mul (g.partial_memLp_top p)).add
      (g.memLp_top.mul (f.partial_memLp_top p))

def SmoothTest.multiply {N : ℕ} {L : Length} {a : ℝ} (f : SmoothMultiplier N L)
    (g : SmoothTest N L a) : SmoothTest N L a where
  toFun := f.toFun * g.toFun
  smooth := f.smooth.mul g.smooth
  compact := g.compact.mul_left
  support_allowed := tsupport_mul_subset_right.trans g.support_allowed
  memLp := f.memLp_top.mul g.memLp
  partial_memLp := by
    intro p
    rw [coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp))]
    exact (f.memLp_top.mul (g.partial_memLp p)).add
      (g.memLp.mul (f.partial_memLp_top p))

def SmoothMultiplier.onScalar {N : ℕ} {L : Length} (f : SmoothMultiplier N L) :
    ScalarL2 N L →L[ℂ] ScalarL2 N L := L2Multiplier.clm f.toFun f.memLp_top

def SmoothMultiplier.onJet {N : ℕ} {L : Length} (f : SmoothMultiplier N L) :
    Jet N L →L[ℂ] Jet N L :=
  (f.onScalar.comp (.fst ℂ _ _)).prod (.pi fun p ↦
    f.onScalar.comp ((ContinuousLinearMap.proj p).comp (ContinuousLinearMap.snd ℂ _ _)) +
    (L2Multiplier.clm _ (f.partial_memLp_top p)).comp (.fst ℂ _ _))

lemma SmoothTest.jet_multiply {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) (g : SmoothTest N L a) :
    (g.multiply f).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.multiply f).memLp, MemLp.coeFn_toLp g.memLp,
      L2Multiplier.coe_clm f.toFun f.memLp_top g.jet.1] with X h1 h2 h3
    change _ = (f.onScalar g.jet.1) X
    exact h1.trans (by simpa only [SmoothTest.multiply, Pi.mul_apply, SmoothTest.jet,
      SmoothMultiplier.onScalar, h2] using h3.symm)
  · funext p
    apply Lp.ext
    have hder := coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp)) p
    filter_upwards [MemLp.coeFn_toLp ((g.multiply f).partial_memLp p),
      MemLp.coeFn_toLp g.memLp, MemLp.coeFn_toLp (g.partial_memLp p),
      L2Multiplier.coe_clm f.toFun f.memLp_top (g.jet.2 p),
      L2Multiplier.coe_clm _ (f.partial_memLp_top p) g.jet.1,
      Lp.coeFn_add (f.onScalar (g.jet.2 p))
        (L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1)] with X h1 h2 h3 h4 h5 h6
    change _ = (f.onScalar (g.jet.2 p) + L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1) X
    rw [h6, Pi.add_apply, SmoothMultiplier.onScalar, h4, h5]
    simp only [SmoothTest.jet]
    rw [h1]
    change coordDerivative N L (f.toFun * g.toFun) p X = _
    rw [hder]
    simp only [Pi.add_apply, Pi.mul_apply, h2, h3]
    ring

lemma SmoothMultiplier.onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    f.onJet u ∈ dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g, rfl⟩
  exact ⟨g.multiply f, g.jet_multiply f⟩

end HardSphere

end

end OAI
