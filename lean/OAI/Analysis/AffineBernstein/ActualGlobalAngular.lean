import Mathlib
import OAI.Analysis.AffineBernstein.ActualWeightedAngularFurther
import OAI.Analysis.AffineBernstein.TubeCompactIntegral

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

theorem affineEpigraph_global_angular_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
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
    tubeIntegral μ M (fun s => σ s^2) (fun q => tubeAngularTrace H bE F q+
        2*tubeAngularPair H bE P F q+(((n : ℝ)+2)/2)*tubeAngularPair H bE F F q) = 0 := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let A := tubeAngularTrace H bE F
  let Jp := tubeAngularPair H bE P F
  let Je := tubeAngularPair H bE F F
  let J := fun q => A q+2*Jp q+(((n : ℝ)+2)/2)*Je q
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
  have hA : ContinuousOn A (tubeOpenSet D) := continuousOn_tubeAngularTrace hH hF bE hQ
  have hJp : ContinuousOn Jp (tubeOpenSet D) := continuousOn_tubeAngularPair hH hP hF bE hQ
  have hJe : ContinuousOn Je (tubeOpenSet D) := continuousOn_tubeAngularPair hH hF hF bE hQ
  have hJ : ContinuousOn J (tubeOpenSet D) :=
    (hA.add (continuousOn_const.mul hJp)).add (continuousOn_const.mul hJe)
  have hinner (s : S) (hs : s ∈ D) :
      (∫ e : sphere (0:E) 1, M (s,e)*J (s,e) ∂volume.toSphere) = 0 := by
    have hi (g : S × E → ℝ) (hg : ContinuousOn g (tubeOpenSet D)) :
        Integrable (fun e : sphere (0:E) 1 => M (s,e)*g (s,e)) volume.toSphere := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      exact (hM.mul hg).comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun e => tubeLift_mem (s,e) hs)
    have hiA := hi A hA
    have hip := hi Jp hJp
    have hie := hi Je hJe
    have hh := affineEpigraph_angular_literal_drift hΩ hcv hu hp a L hD hK hzero hs bS bE
    dsimp only at hh
    have hh' : (∫ e : sphere (0:E) 1, M (s,e)*A (s,e) ∂volume.toSphere)+
        2*(∫ e : sphere (0:E) 1, M (s,e)*Jp (s,e) ∂volume.toSphere)+
        (∫ e : sphere (0:E) 1, M (s,e)*Je (s,e) ∂volume.toSphere) =
        (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, M (s,e)*Je (s,e) ∂volume.toSphere) := by
      simpa only [A,Jp,Je,M,H,P,F,tubeAngularTrace,tubeAngularPair,div_eq_mul_inv,mul_assoc] using hh
    have hsplit : (∫ e : sphere (0:E) 1, M (s,e)*J (s,e) ∂volume.toSphere) =
        (∫ e : sphere (0:E) 1, M (s,e)*A (s,e) ∂volume.toSphere)+
        2*(∫ e : sphere (0:E) 1, M (s,e)*Jp (s,e) ∂volume.toSphere)+
        (((n : ℝ)+2)/2)*(∫ e : sphere (0:E) 1, M (s,e)*Je (s,e) ∂volume.toSphere) := by
      calc
        _ = ∫ e : sphere (0:E) 1, (M (s,e)*A (s,e)+2*(M (s,e)*Jp (s,e)))+
            (((n : ℝ)+2)/2)*(M (s,e)*Je (s,e)) ∂volume.toSphere := by
          apply integral_congr_ae; exact Filter.Eventually.of_forall fun _ => by dsimp [J]; ring
        _ = (∫ e : sphere (0:E) 1, M (s,e)*A (s,e)+2*(M (s,e)*Jp (s,e)) ∂volume.toSphere)+
            (∫ e : sphere (0:E) 1, (((n : ℝ)+2)/2)*(M (s,e)*Je (s,e)) ∂volume.toSphere) := by
          exact integral_add (hiA.add (hip.const_mul 2)) (hie.const_mul _)
        _ = _ := by rw [integral_add hiA (hip.const_mul 2),integral_const_mul,integral_const_mul]
    rw [hsplit]
    linarith
  change tubeIntegral μ M (fun s => σ s^2) J = 0
  rw [tubeIntegral_angular (σ := fun s => σ s^2) (by fun_prop) (compactSupport_sq hc) (tsupport_sq_subset.trans hσD) hM hJ]
  have hz : (fun s => σ s^2*(∫ e : sphere (0:E) 1, M (s,e)*J (s,e) ∂volume.toSphere)) = fun _ => 0 := by
    funext s
    by_cases hs : s ∈ tsupport σ
    · rw [hinner s (hσD hs),mul_zero]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  rw [hz,integral_zero]

end AffineBernstein
end

end OAI
