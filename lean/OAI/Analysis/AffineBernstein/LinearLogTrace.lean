import Mathlib
import OAI.Analysis.AffineBernstein.ActualGlobalCoercive

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section LinearLogTrace
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma flatInverseTrace_linear (ℓ : V →L[ℝ] ℝ) (A : Matrix ι ι ℝ) (v : ι → V) (x : V) :
    flatInverseTrace A v ℓ x = 0 := by
  have hh (w : V) : dirDeriv w ℓ = fun _ => ℓ w := by
    funext y
    simp only [dirDeriv,ContinuousLinearMap.fderiv]
  simp only [flatInverseTrace,hh,dirDeriv,fderiv_const_apply,zero_apply,mul_zero,Finset.sum_const_zero]

lemma flatInverseTrace_log_linear (ℓ : V →L[ℝ] ℝ) (A : Matrix ι ι ℝ) (v : ι → V)
    {x : V} (hx : 0 < ℓ x) :
    flatInverseTrace A v (fun y => Real.log (ℓ y)) x =
      -flatInversePair A v (fun y => Real.log (ℓ y)) (fun y => Real.log (ℓ y)) x := by
  have hh := flat_log_hessian_trace (isOpen_lt continuous_const ℓ.continuous)
    ℓ.contDiff.contDiffOn (fun y hy => hy) hx A v
  rw [flatInverseTrace_linear] at hh
  have he : flatInverseTrace A v (fun y => Real.log (ℓ y)) x+
      flatInversePair A v (fun y => Real.log (ℓ y)) (fun y => Real.log (ℓ y)) x = 0 :=
    (mul_eq_zero.mp hh.symm).resolve_left hx.ne'
  linarith

end LinearLogTrace

section ActualLogCoordinate
open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Compact product base IBP on the actual tube, rather than a formal drift identity. -/
theorem affineEpigraph_global_log_coordinate_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (ℓ : S →L[ℝ] ℝ) (hℓ : ∀ s ∈ D, 0 < ℓ s)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    let A := fun q : S × E => Real.log (ℓ q.1)
    tubeIntegral μ M (fun s => σ s^2) (fun q => tubeBasePair H bS A A q+
      (n : ℝ)*tubeBasePair H bS P A q+(((n : ℝ)+2)/2)*tubeBasePair H bS F A q) =
      2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) A) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let A := fun q : S × E => Real.log (ℓ q.1)
  have hA (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ A q :=
    (ℓ.contDiff.contDiffAt.comp q contDiffAt_fst).log (hℓ q.1 hq.1).ne'
  have htrace (q : S × E) (hq : q ∈ tubeOpenSet D) :
      tubeBaseTrace H bS A q = -tubeBasePair H bS A A q := by
    have ht := flatInverseTrace_log_linear (ℓ.comp (ContinuousLinearMap.fst ℝ S E))
      (tubeBaseMatrix H q bS) (fun i => (bS i,(0:E))) (hℓ q.1 hq.1)
    change flatInverseTrace (tubeBaseMatrix H q bS) (fun i => (bS i,(0:E))) A q =
      -flatInversePair (tubeBaseMatrix H q bS) (fun i => (bS i,(0:E))) A A q at ht
    unfold tubeBaseTrace tubeBasePair
    rw [ht,mul_neg]
  have hb := affineEpigraph_global_base_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero bS bE hσ hc hσD hA
  change tubeIntegral μ M (fun s => σ s^2) (fun q => tubeBaseTrace H bS A q-
    (n : ℝ)*tubeBasePair H bS P A q-(((n : ℝ)+2)/2)*tubeBasePair H bS F A q) =
    -2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) A) at hb
  have hcI := tubeIntegral_congr_on (μ := μ) (M := M) (σ := fun s => σ s^2)
    (f := fun q => tubeBaseTrace H bS A q-(n : ℝ)*tubeBasePair H bS P A q-
      (((n : ℝ)+2)/2)*tubeBasePair H bS F A q)
    (g := fun q => (-1)*(tubeBasePair H bS A A q+(n : ℝ)*tubeBasePair H bS P A q+
      (((n : ℝ)+2)/2)*tubeBasePair H bS F A q))
    (tsupport_sq_subset.trans hσD) (fun q hq => by rw [htrace q hq]; ring)
  rw [hcI,tubeIntegral_smul] at hb
  change tubeIntegral μ M (fun s => σ s^2) (fun q => tubeBasePair H bS A A q+
      (n : ℝ)*tubeBasePair H bS P A q+(((n : ℝ)+2)/2)*tubeBasePair H bS F A q) =
      2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) A)
  linarith

end ActualLogCoordinate

/- The coordinate-log Young estimate, with constants uniform for 3≤n≤9. -/
theorem tube_log_cutoff_absorption {n v PP DD EE AA Q PA DA RA : ℝ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hP : 0 ≤ PP) (hD : 0 ≤ DD) (hE : 0 ≤ EE)
    (hA : 0 ≤ AA) (hQ : 0 ≤ Q) (hPA : PA^2 ≤ AA*PP) (hDA : DA^2 ≤ AA*DD)
    (hRA : RA^2 ≤ AA*Q) :
    v^2*AA ≤ 4*v^2*(AA+n*PA+((n+2)/2)*DA)-8*v*RA+
      324*v^2*(1+PP+DD+EE)+16*Q := by
  have hpa := mul_le_mul_of_nonneg_left hPA (sq_nonneg v)
  have hda := mul_le_mul_of_nonneg_left hDA (sq_nonneg v)
  have hra := mul_le_mul_of_nonneg_left hRA (sq_nonneg v)
  have hp := cauchy_young (show 0 ≤ v^2*AA by positivity) hP
    (show (v*PA)^2 ≤ (v^2*AA)*PP by nlinarith [hpa]) (a := -n*v) (by norm_num : (0:ℝ) < 1/4)
  have hd := cauchy_young (show 0 ≤ v^2*AA by positivity) hD
    (show (v*DA)^2 ≤ (v^2*AA)*DD by nlinarith [hda]) (a := -((n+2)/2)*v) (by norm_num : (0:ℝ) < 1/4)
  have hr := cauchy_young (show 0 ≤ v^2*AA by positivity) hQ
    (show (v*RA)^2 ≤ (v^2*AA)*Q by nlinarith [hra]) (a := 2) (by norm_num : (0:ℝ) < 1/4)
  norm_num at hp hd hr
  have hnq : 0 ≤ 81-n^2 := by nlinarith [mul_nonneg (show 0 ≤ 9-n by linarith) (show 0 ≤ 9+n by linarith)]
  have hcq : 0 ≤ 81-((n+2)/2)^2 := by nlinarith [mul_nonneg (show 0 ≤ 18-(n+2) by linarith) (show 0 ≤ 18+(n+2) by linarith)]
  have hrem : 0 ≤ v^2*((81-n^2)*PP+(81-((n+2)/2)^2)*DD+81*(1+EE)) := by positivity
  nlinarith [hp,hd,hr,hrem]

end AffineBernstein
end

end OAI
