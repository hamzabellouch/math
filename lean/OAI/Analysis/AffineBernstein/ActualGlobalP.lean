import Mathlib
import OAI.Analysis.AffineBernstein.ActualWeightedLog
import OAI.Analysis.AffineBernstein.TubeMetricPositivity
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

/- The actual p-identity, with all compact product integrations justified. -/
theorem affineEpigraph_global_p_identity {n : ℕ} {Ω : Set (Space n)}
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
    tubeIntegral μ M (fun s => σ s^2) (fun q => (Fintype.card ι : ℝ)+
      ((n : ℝ)+1)*tubeBasePair H bS P P q+(((n : ℝ)+2)/2)*tubeBasePair H bS P F q) =
      2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) P) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let J := fun q => (Fintype.card ι : ℝ)+((n : ℝ)+1)*tubeBasePair H bS P P q+
      (((n : ℝ)+2)/2)*tubeBasePair H bS P F q
  let R := tubeBasePair H bS (fun q => σ q.1) P
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
  have hJ : ContinuousOn J (tubeOpenSet D) := fun q hq =>
    ((contDiffAt_const.add
      (contDiffAt_const.mul (contDiffAt_tubeBasePair (hH q hq) (hP q hq) (hP q hq) bS (hpos q hq).1.det_pos.ne'))).add
      (contDiffAt_const.mul (contDiffAt_tubeBasePair (hH q hq) (hP q hq) (hF q hq) bS (hpos q hq).1.det_pos.ne'))).continuousAt.continuousWithinAt
  have hR : ContinuousOn R (tubeOpenSet D) := fun q hq =>
    (contDiffAt_tubeBasePair (hH q hq) (hσ.contDiffAt.comp q contDiffAt_fst) (hP q hq) bS
      (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  change tubeIntegral μ M (fun s => σ s^2) J = 2*tubeIntegral μ M σ R
  rw [tubeIntegral_base (σ := fun s => σ s^2) (by fun_prop) (compactSupport_sq hc) (tsupport_sq_subset.trans hσD) hM hJ,
    tubeIntegral_base hσ.continuous hc hσD hM hR,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  have he : ‖(e:E)‖ = 1 := mem_sphere_zero_iff_norm.1 e.property
  have hen : (e:E) ≠ 0 := by intro hz; simp [hz] at he
  have hh := affineEpigraph_base_p_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero he bS bE hσ hc hσD
  dsimp only at hh
  convert hh using 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hq : (s,(e:E)) ∈ tubeOpenSet D := ⟨hσD hs,hen⟩
      unfold J
      rw [tubeBasePair_symm bS (hpos (s,e) hq).1 P F]
      unfold tubeBasePair
      rw [← flatInversePair_prod_left ((hP (s,e) hq).differentiableAt (by simp)) ((hP (s,e) hq).differentiableAt (by simp)),
        ← flatInversePair_prod_left ((hF (s,e) hq).differentiableAt (by simp)) ((hP (s,e) hq).differentiableAt (by simp))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hs]
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hq : (s,(e:E)) ∈ tubeOpenSet D := ⟨hσD hs,hen⟩
      unfold R tubeBasePair
      rw [← flatInversePair_prod_left (f := fun q : S × E => σ q.1) ((hσ.contDiffAt.comp (s,(e:E)) contDiffAt_fst).differentiableAt (by simp))
        ((hP (s,e) hq).differentiableAt (by simp))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hs]

end AffineBernstein
end

end OAI
