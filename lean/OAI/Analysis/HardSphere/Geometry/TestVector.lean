import Mathlib
import OAI.Analysis.HardSphere.Geometry.CoordinateLine
import OAI.Analysis.HardSphere.Geometry.NormSqLpIntegral
import OAI.Analysis.HardSphere.Operators.Regularize

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
section

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

def testVector (F : I → SmoothTest N L a) (X : Configuration N L) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i ↦ (F i).toFun X)

lemma testVector_smooth (F : I → SmoothTest N L a) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration N ↦ testVector F (project N L R)) :=
  (contDiff_piLp 2).mpr (fun i ↦ (F i).smooth)

lemma testVector_continuous (F : I → SmoothTest N L a) : Continuous (testVector F) :=
  continuous_of_continuous_lift (testVector_smooth F).continuous

lemma testVector_derivative (F : I → SmoothTest N L a) (X : Configuration N L) (p : Direction N) (i : I) :
    (fderiv ℝ (fun R : LiftedConfiguration N ↦ testVector F (project N L R)) (representative N L X)
      (Pi.single p.1 (Pi.single p.2 1))) i = coordDerivative N L (F i).toFun p X := by
  have hF := (testVector_smooth F).differentiable (by simp) (representative N L X)
  have hi := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
    (testVector F (project N L (representative N L X))) i).comp (representative N L X) hF.hasFDerivAt).fderiv
  exact (congrArg (fun d ↦ d (Pi.single p.1 (Pi.single p.2 1))) hi).symm

def rmsTestFun (F : I → SmoothTest N L a) (ε : ℝ) (X : Configuration N L) : ℂ :=
  HilbertRegularization.regularize ε (testVector F X)

lemma rmsTest_smooth (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration N ↦ rmsTestFun F ε (project N L R)) :=
  (HilbertRegularization.smooth hε).comp (testVector_smooth F)

lemma rmsTest_support (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    tsupport (rmsTestFun F ε)⊆allowed N L a := by
  have hs : tsupport (rmsTestFun F ε)⊆⋃ i,tsupport (F i).toFun := by
    apply closure_minimal ?_ (isClosed_iUnion_of_finite (fun i ↦ isClosed_tsupport (F i).toFun))
    intro X hX
    by_contra hn
    have hz : testVector F X=0 := by
      ext i
      change (F i).toFun X=0
      exact image_eq_zero_of_notMem_tsupport (fun hi ↦ hn (Set.mem_iUnion.mpr ⟨i,hi⟩))
    exact hX (by change HilbertRegularization.regularize ε (testVector F X)=0; rw [hz,HilbertRegularization.zero hε.le])
  intro X hX
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs hX)
  exact (F i).support_allowed hi

def SmoothTest.rms (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) : SmoothTest N L a where
  toFun := rmsTestFun F ε
  smooth := rmsTest_smooth F hε
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := rmsTest_support F hε
  memLp := (continuous_of_continuous_lift (rmsTest_smooth F hε).continuous).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  partial_memLp := fun p ↦ (continuous_coordDerivative (rmsTest_smooth F hε) p).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rmsTest_derivative_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε)
    (X : Configuration N L) (p : Direction N) :
    ‖coordDerivative N L (SmoothTest.rms F hε).toFun p X‖^2≤
      ∑ i : I, ‖coordDerivative N L (F i).toFun p X‖^2 := by
  have he : (fun R : LiftedConfiguration N ↦ (SmoothTest.rms F hε).toFun (project N L R))=
      HilbertRegularization.regularize ε ∘ (fun R ↦ testVector F (project N L R)) := rfl
  change ‖fderiv ℝ (fun R ↦ (SmoothTest.rms F hε).toFun (project N L R)) (representative N L X)
    (Pi.single p.1 (Pi.single p.2 1))‖^2≤_
  rw [he,fderiv_comp _ ((HilbertRegularization.smooth hε).differentiable (by simp)).differentiableAt
    ((testVector_smooth F).differentiable (by simp)).differentiableAt,
    HilbertRegularization.fderiv_eq hε,ContinuousLinearMap.comp_apply,project_representative]
  calc
    _ ≤ ‖fderiv ℝ (fun R ↦ testVector F (project N L R)) (representative N L X)
        (Pi.single p.1 (Pi.single p.2 1))‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.differential_apply_le ε _ _) 2
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]; simp only [testVector_derivative]

end

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma rmsTest_energy_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    energy (SmoothTest.rms F hε).jet ≤ ∑ i,energy (F i).jet := by
  classical
  change (∑ p, ‖(SmoothTest.rms F hε).jet.2 p‖^2)≤∑ i,∑ p,‖(F i).jet.2 p‖^2
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [← integral_finsetSum (f := fun i X ↦ ‖coordDerivative N L (F i).toFun p X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  apply integral_mono
  · exact ((SmoothTest.rms F hε).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro X
    exact rmsTest_derivative_le F hε X p

lemma rmsTest_norm_limit (F : I → SmoothTest N L a) {e : ℕ → ℝ}
    (he : ∀ k,0<e k) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖(SmoothTest.rms F (he k)).jet.1‖^2) atTop
      (𝓝 (∑ i,‖(F i).jet.1‖^2)) := by
  classical
  have hint : Integrable (fun X ↦ ‖testVector F X‖^2) (volume : Measure (Configuration N L)) :=
    ((testVector_continuous F).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlim := tendsto_integral_of_dominated_convergence (fun X ↦ ‖testVector F X‖^2)
    (fun k ↦ ((SmoothTest.rms F (he k)).continuous.norm.pow 2).aestronglyMeasurable)
    hint (fun k ↦ ae_of_all _ (fun X ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.norm_le (he k) (testVector F X)) 2))
    (ae_of_all _ (fun X ↦ (HilbertRegularization.tendsto_regularize (testVector F X) he0).norm.pow 2))
  have hI : (∫ X : Configuration N L, ‖(‖testVector F X‖ : ℂ)‖^2) =
      ∑ i,‖(F i).jet.1‖^2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    simp only [EuclideanSpace.norm_sq_eq,testVector]
    rw [integral_finsetSum (f := fun i X ↦ ‖(F i).toFun X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [hI] at hlim
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral,SmoothTest.rms,rmsTestFun] at hlim ⊢
  exact hlim
end HardSphere

end

end OAI
