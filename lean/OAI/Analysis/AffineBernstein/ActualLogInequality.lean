import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogMeasureEnergy
import OAI.Analysis.AffineBernstein.EuclideanChain
import OAI.Analysis.AffineBernstein.TubeSupportedIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- Proposition log-inequality for the actual affine-epigraph tube. The positive-
orthant pullback is extended by zero, and both sides are literal product integrals
with the source logarithmic density. No tube-metric completeness is required. -/
theorem affineMaximal_logarithmic_inequality {n k : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    (hk : 2 ≤ k) (hkn : k ≤ n) {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ logSpace '' D) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let M := tubeMeasureDensity n H b bE
    let T := fun q => 1+∑ i : Fin k,
      tubeBasePair H b (fun z => Real.log (z.1 i)) (fun z => Real.log (z.1 i)) q
    tubeIntegral μ M (fun s => logPullback φ s^2) T ≤
      (4194304+(n : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1)
        (fun q => logPullback (euclideanGradientSquare φ) q.1*T q) := by
  dsimp only
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let M := tubeMeasureDensity n H b bE
  let A := fun (i : Fin k) (q : Space k × E) => Real.log (q.1 i)
  let T := fun q => 1+∑ i : Fin k, tubeBasePair H b (A i) (A i) q
  let σ := logPullback φ
  let V := fun q : Space k × E => σ q.1
  let W := logPullback (euclideanGradientSquare φ)
  let Q := tubeBasePair H b V V
  let K := expSpace '' tsupport φ
  have hKc : IsCompact K := hc.isCompact.image contDiff_expSpace.continuous
  have hKD : K ⊆ D := by
    rintro s ⟨x,hx,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hφD hx
    simpa only [expSpace_logSpace (hDpos hy)] using hy
  have hσ : ContDiff ℝ ∞ σ := contDiff_logPullback hφ hc
  have hcσ : HasCompactSupport σ := hasCompactSupport_logPullback hc
  have hσD : tsupport σ ⊆ D := tsupport_logPullback_subset_logDomain hDpos hc hφD
  have hW : Continuous W := (contDiff_logPullback (contDiff_euclideanGradientSquare hφ)
    (compactSupport_euclideanGradientSquare hc)).continuous
  have hH (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : Space k × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 b bE
  have hA (i : Fin k) (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q :=
    by
      have hpj : ContDiff ℝ ∞ (fun s : Space k => s i) := (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).contDiff
      have hh : ContDiffAt ℝ ∞ (fun z : Space k × E => z.1 i) q :=
        (hpj.comp contDiff_fst).contDiffAt
      exact hh.log (hDpos hq.1 i).ne'
  have hV (q : Space k × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ V q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) b bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : Space k × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H b f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) b
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hT : ContinuousOn T (tubeOpenSet D) := continuousOn_const.add
    (continuousOn_finsetSum _ fun i _ => hpair (A i) (A i) (hA i) (hA i))
  have hQ : ContinuousOn Q (tubeOpenSet D) := hpair V V hV hV
  have hQzero (s : Space k) (hs : s ∉ K) (e : E) : Q (s,e) = 0 := by
    have hsσ : s ∉ tsupport σ := fun h => hs (tsupport_logPullback_subset hc h)
    have hd : fderiv ℝ V (s,e) = 0 := by
      dsimp only [V]
      rw [show (fun q : Space k × E => σ q.1) = σ ∘ Prod.fst by rfl,
        fderiv_comp (s,e) (hσ.differentiable (by simp) s) differentiableAt_fst,
        fderiv_of_notMem_tsupport ℝ hsσ]
      simp
    simp [Q,tubeBasePair,flatInversePair,dirDeriv,hd]
  have hWzero (s : Space k) (hs : s ∉ K) : W s = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hs (logPullback_gradient_support hc h))
  have hMn (s : Space k) (hs : s ∈ D) (e : E) (he : ‖e‖ = 1) : 0 ≤ M (s,e) := by
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    exact (tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le
  have hQI : 0 ≤ tubeIntegral μ M (fun _ => 1) Q := by
    apply tubeIntegral_supported_nonneg hKD hQzero
    intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    exact ⟨hMn s hs e he,tubeBasePair_nonneg b hz.2.2.le hz.1 V⟩
  have hcomp : tubeIntegral μ M (fun _ => 1) Q ≤
      tubeIntegral μ M (fun _ => 1) (fun q => W q.1*T q) := by
    apply tubeIntegral_supported_mono hKc hKD hM hQ ((hW.comp continuous_fst).continuousOn.mul hT)
      hQzero (fun s hs _ => by simp [hWzero s hs]) hMn
    intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    let c := fun i : Fin k => fderiv ℝ φ (logSpace s) ((EuclideanSpace.basisFun (Fin k) ℝ) i)
    have hcb := tubeBasePair_linearCombination b hz.2.2.le hz.1 V A c
      (fun i => logPullback_fderiv_chain hφ (hDpos hs) (b i,(0:E)))
    change Q (s,e) ≤ (∑ i, c i^2)*(∑ i, tubeBasePair H b (A i) (A i) (s,e)) at hcb
    have hWeq : W s = ∑ i, c i^2 := logPullback_of_positive _ (hDpos hs)
    change Q (s,e) ≤ W s*(1+∑ i, tubeBasePair H b (A i) (A i) (s,e))
    rw [hWeq]
    nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (c i))]
  have he := affineMaximal_tube_log_measure_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L hD hK hzero
    b bE (by simpa using hk) (fun i => EuclideanSpace.proj i) (fun i s hs => hDpos hs i) hσ hcσ hσD
  change tubeIntegral μ M (fun s => σ s^2) T ≤
    (4194304+(Fintype.card (Fin k) : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1) Q at he
  have hco : 4194304+(Fintype.card (Fin k) : ℝ)*1358954512 ≤ 4194304+(n : ℝ)*1358954512 := by
    simp only [Fintype.card_fin]
    have hknr : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  have hcn : 0 ≤ 4194304+(n : ℝ)*1358954512 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hco hQI).trans
    (mul_le_mul_of_nonneg_left hcomp hcn))

end AffineBernstein
end

end OAI
