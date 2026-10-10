import Mathlib
import OAI.Analysis.AffineBernstein.ActualRoundFEquation
import OAI.Analysis.AffineBernstein.TubeMetricPositivity
import OAI.Analysis.AffineBernstein.ActualGlobalBase
import OAI.Analysis.AffineBernstein.ActualGlobalAngular

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_global_d_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2) (fun q => ((n : ℝ)/2)*
      (tubeBasePair H bS F F q+tubeAngularPair H bE F F q)+
      ((n : ℝ)+2)*(tubeBasePair H bS P P q+tubeBasePair H bS P F q)-
      ((n : ℝ)-2*Fintype.card ι)) =
      -2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) F) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let B := fun q => tubeBaseTrace H bS F q-(n : ℝ)*tubeBasePair H bS P F q-
      (((n : ℝ)+2)/2)*tubeBasePair H bS F F q
  let A := fun q => tubeAngularTrace H bE F q+2*tubeAngularPair H bE P F q+
      (((n : ℝ)+2)/2)*tubeAngularPair H bE F F q
  let J := fun q => ((n : ℝ)/2)*(tubeBasePair H bS F F q+tubeAngularPair H bE F F q)+
      ((n : ℝ)+2)*(tubeBasePair H bS P P q+tubeBasePair H bS P F q)-((n : ℝ)-2*Fintype.card ι)
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hQ (q : S × E) (hq : q ∈ tubeOpenSet D) : tubeAngularDensity H q bE ≠ 0 := (hpos q hq).2.1.ne'
  have hB : ContinuousOn B (tubeOpenSet D) := fun q hq =>
    (((contDiffAt_tubeBaseTrace (hH q hq) (hF q hq) bS (hpos q hq).1.det_pos.ne').sub
      (contDiffAt_const.mul (contDiffAt_tubeBasePair (hH q hq) (hP q hq) (hF q hq) bS (hpos q hq).1.det_pos.ne'))).sub
      (contDiffAt_const.mul (contDiffAt_tubeBasePair (hH q hq) (hF q hq) (hF q hq) bS (hpos q hq).1.det_pos.ne'))).continuousAt.continuousWithinAt
  have hA : ContinuousOn A (tubeOpenSet D) :=
    ((continuousOn_tubeAngularTrace hH hF bE hQ).add
      (continuousOn_const.mul (continuousOn_tubeAngularPair hH hP hF bE hQ))).add
      (continuousOn_const.mul (continuousOn_tubeAngularPair hH hF hF bE hQ))
  have hpoint (s : S) (hs : s ∈ D) (e : E) (he : ‖e‖ = 1) : J (s,e) = B (s,e)+A (s,e) := by
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hq : (s,e) ∈ tubeOpenSet D := ⟨hs,hen⟩
    have eq := affineMaximal_round_tube_f_equation hΩ hcv hu hp hm a L hD hK hzero hs he bS bE
    dsimp only at eq
    have ha := tubeBasePair_add_self bS ((hF (s,e) hq).differentiableAt (by simp))
      ((hP (s,e) hq).differentiableAt (by simp)) (hpos (s,e) hq).1
    have hsym := tubeBasePair_symm bS (hpos (s,e) hq).1 F P
    dsimp only [J,B,A,tubeBasePair,tubeBaseTrace,tubeAngularPair,tubeAngularTrace] at ha hsym ⊢
    dsimp only [H,P,F] at ha hsym ⊢
    linear_combination -eq - ((n : ℝ)+1)*ha - 2*((n : ℝ)+1)*hsym
  have hgb := affineEpigraph_global_base_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero bS bE hσ hc hσD hF
  have hga := affineEpigraph_global_angular_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero bS bE hσ hc hσD
  change tubeIntegral μ M (fun s => σ s^2) B = -2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) F) at hgb
  change tubeIntegral μ M (fun s => σ s^2) A = 0 at hga
  change tubeIntegral μ M (fun s => σ s^2) J = _
  rw [tubeIntegral_congr_sphere (g := fun q => B q+A q) (tsupport_sq_subset.trans hσD) hpoint,
    tubeIntegral_add (σ := fun s => σ s^2) (by fun_prop) (compactSupport_sq hc) (tsupport_sq_subset.trans hσD) hM hB hA,hgb,hga,add_zero]

end AffineBernstein
end

end OAI
