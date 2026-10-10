import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogEnergy
import OAI.Analysis.AffineBernstein.TubeSumIntegral

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

theorem affineMaximal_tube_log_measure_energy {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hk : 2 ≤ Fintype.card ι)
    (ℓ : ι → S →L[ℝ] ℝ) (hℓ : ∀ i, ∀ s ∈ D, 0 < ℓ i s)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2)
      (fun q => 1+∑ i, tubeBasePair H bS (fun q => Real.log (ℓ i q.1))
        (fun q => Real.log (ℓ i q.1)) q) ≤
      (4194304+(Fintype.card ι : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1)) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let V := fun q : S × E => σ q.1
  let A := fun i (q : S × E) => Real.log (ℓ i q.1)
  have hA (i : ι) (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q :=
    ((ℓ i).contDiff.contDiffAt.comp q contDiffAt_fst).log (hℓ i q.1 hq.1).ne'
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hV (q : S × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ V q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : S × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H bS f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) bS
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hEE : ContinuousOn (tubeAngularPair H bE F F) (tubeOpenSet D) :=
    continuousOn_tubeAngularPair hH hF hF bE (fun q hq => (hpos q hq).2.1.ne')
  have he := affineMaximal_tube_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L hD hK hzero
    bS bE hk hσ hc hσD
  have ha (i : ι) := affineMaximal_tube_log_coordinate_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L
    hD hK hzero bS bE hk (ℓ i) (hℓ i) hσ hc hσD
  let Q := tubeBasePair H bS V V
  have h1 : tubeIntegral μ M (fun s => σ s^2) (fun _ => 1) ≤
      4194304*tubeIntegral μ M (fun _ => 1) Q := by
    apply le_trans (tubeIntegral_mono_sq hσ.continuous hc hσD hM continuousOn_const
      (((continuousOn_const.add (hpair P P hP hP)).add (hpair F F hF hF)).add hEE) ?_ ?_) he
    · intro s hs e he
      have hen : e ≠ 0 := by intro hz; simp [hz] at he
      have hz := hpos (s,e) ⟨hs,hen⟩
      exact (tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le
    · intro s hs e he
      have hen : e ≠ 0 := by intro hz; simp [hz] at he
      have hz := hpos (s,e) ⟨hs,hen⟩
      have hp0 := tubeBasePair_nonneg bS hz.2.2.le hz.1 P
      have hf0 := tubeBasePair_nonneg bS hz.2.2.le hz.1 F
      have he0 := affineEpigraph_tube_angular_pair_nonneg hΩ hcv hu hp a L hD hK hzero hs he bS bE
        ((hF (s,e) ⟨hs,hen⟩).differentiableAt (by simp))
      change 0 ≤ tubeBasePair H bS P P (s,e) at hp0
      change 0 ≤ tubeBasePair H bS F F (s,e) at hf0
      change 0 ≤ tubeAngularPair H bE F F (s,e) at he0
      change 1 ≤ 1+tubeBasePair H bS P P (s,e)+tubeBasePair H bS F F (s,e)+tubeAngularPair H bE F F (s,e)
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)
  change (∑ i, tubeIntegral μ M (fun s => σ s^2) (tubeBasePair H bS (A i) (A i))) ≤
    ∑ i : ι, 1358954512*tubeIntegral μ M (fun _ => 1) Q at hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  change tubeIntegral μ M (fun s => σ s^2) (fun q => 1+∑ i, tubeBasePair H bS (A i) (A i) q) ≤ _
  rw [tubeIntegral_add (σ := fun s => σ s^2) (hσ.continuous.pow 2) (compactSupport_sq hc) (tsupport_sq_subset.trans hσD)
    hM continuousOn_const (continuousOn_finsetSum _ fun i _ => hpair (A i) (A i) (hA i) (hA i))]
  rw [tubeIntegral_sum Finset.univ (σ := fun s => σ s^2) (hσ.continuous.pow 2) (compactSupport_sq hc)
    (tsupport_sq_subset.trans hσD) hM (fun i _ => hpair (A i) (A i) (hA i) (hA i))]
  change _ ≤ (4194304+(Fintype.card ι : ℝ)*1358954512)*tubeIntegral μ M (fun _ => 1) Q
  nlinarith

end AffineBernstein
end

end OAI
