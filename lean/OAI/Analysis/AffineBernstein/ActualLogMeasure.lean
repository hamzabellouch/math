import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogInequality
import OAI.Analysis.AffineBernstein.LogTubeMeasure

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

def tubeLogMassWeight {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E) : ℝ :=
  1+∑ i : Fin k, tubeBasePair H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (fun z => Real.log (z.1 i)) (fun z => Real.log (z.1 i)) q

/- Joint regularity and positivity of the actual source logarithmic density. -/
omit [MeasurableSpace E] [BorelSpace E] in
lemma affineEpigraph_logWeight_regular {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
    let T := tubeLogMassWeight H
    ContinuousOn M (tubeOpenSet D) ∧ ContinuousOn T (tubeOpenSet D) ∧
      ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ T (s,e) := by
  dsimp only
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let A := fun (i : Fin k) (q : Space k × E) => Real.log (q.1 i)
  have hH (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : Space k × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 b bE
  have hA (i : Fin k) (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q := by
    have hpj : ContDiff ℝ ∞ (fun s : Space k => s i) := (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).contDiff
    have hh : ContDiffAt ℝ ∞ (fun z : Space k × E => z.1 i) q := (hpj.comp contDiff_fst).contDiffAt
    exact hh.log (hDpos hq.1 i).ne'
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact (continuousAt_tubeMeasureDensity (hH q hq) b bE (hpos q hq).2.2).continuousWithinAt
  · apply continuousOn_const.add
    apply continuousOn_finsetSum
    intro i _ q hq
    exact (contDiffAt_tubeBasePair (hH q hq) (hA i q hq) (hA i q hq) b
      (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  · intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    refine ⟨(tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le,?_⟩
    apply add_nonneg zero_le_one
    exact Finset.sum_nonneg fun i _ => tubeBasePair_nonneg b hz.2.2.le hz.1 (A i)

/- The paper's sigma measure, pushed to logarithmic coordinates. This definition
uses the actual affine epigraph support function, not an abstract model metric. -/
def affineEpigraphLogMeasure {n k : ℕ} (μ : Measure (Space k)) (D : Set (Space k))
    (Ω : Set (Space n)) (u : Space n → ℝ) (a : Space n × ℝ)
    (L : (Space k × E) ≃L[ℝ] (Space n × ℝ)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    Measure (Space k) :=
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  logTubeMeasure μ D (fun q => tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE q *
    tubeLogMassWeight H q)

/- Actual measure form of Proposition log-inequality, with the Euclidean
operator norm of the true derivative in logarithmic coordinates. -/
theorem affineMaximal_logMeasure_poincare {n k : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    (hk : 2 ≤ k) (hkn : k ≤ n) {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ logSpace '' D) :
    (∫ x, φ x^2 ∂affineEpigraphLogMeasure μ D Ω u a L bE) ≤
      (4194304+(n : ℝ)*1358954512) *
        ∫ x, ‖fderiv ℝ φ x‖^2 ∂affineEpigraphLogMeasure μ D Ω u a L bE := by
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let M := tubeMeasureDensity n H b bE
  let T := tubeLogMassWeight H
  obtain ⟨hM,hT,hpos⟩ := affineEpigraph_logWeight_regular hΩ hcv hu hp a L hD hDpos hK hzero bE
  have hi (ψ : Space k → ℝ) (hψ : StronglyMeasurable ψ) (hs : tsupport ψ ⊆ logSpace '' D) :
      (∫ x, ψ x ∂affineEpigraphLogMeasure μ D Ω u a L bE) = tubeIntegral μ M (logPullback ψ) T :=
    integral_logTubeMeasure_mul hD.measurableSet hDpos hM hT
      (fun s hs e he => (hpos s hs e he).1) (fun s hs e he => (hpos s hs e he).2) hψ hs
  have hgS : tsupport (euclideanGradientSquare φ) ⊆ logSpace '' D :=
    (tsupport_euclideanGradientSquare φ).trans hφD
  have hsqS : tsupport (fun x => φ x^2) ⊆ logSpace '' D := by
    apply (tsupport_comp_subset (g := fun x : ℝ => x^2) (by simp) φ).trans hφD
  rw [hi (fun x => φ x^2) (hφ.continuous.pow 2).stronglyMeasurable hsqS,logPullback_sq]
  simp_rw [← euclideanGradientSquare_eq_norm]
  rw [hi _ (contDiff_euclideanGradientSquare hφ).continuous.stronglyMeasurable hgS]
  have hh := affineMaximal_logarithmic_inequality hn hn9 hk hkn hΩ hcv hu hp hm a L
    hD hDpos hK hzero bE hφ hc hφD (μ := μ)
  apply hh.trans_eq
  apply congrArg ((4194304+(n : ℝ)*1358954512) * ·)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by
    dsimp only [M,T,H,b,tubeLogMassWeight,tubeLift]
    ring

end AffineBernstein
end

end OAI
