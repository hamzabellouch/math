import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeEnergy
import OAI.Analysis.AffineBernstein.WeightedLogEnergy

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

theorem affineMaximal_tube_log_coordinate_energy {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hk : 2 ≤ Fintype.card ι)
    (ℓ : S →L[ℝ] ℝ) (hℓ : ∀ s ∈ D, 0 < ℓ s)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2)
      (tubeBasePair H bS (fun q => Real.log (ℓ q.1)) (fun q => Real.log (ℓ q.1))) ≤
      1358954512*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1)) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let V := fun q : S × E => σ q.1
  let A := fun q : S × E => Real.log (ℓ q.1)
  have hA (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ A q :=
    (ℓ.contDiff.contDiffAt.comp q contDiffAt_fst).log (hℓ q.1 hq.1).ne'
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
  have hQzero (s : S) (hs : s ∉ tsupport σ) (e : E) : tubeBasePair H bS V V (s,e) = 0 := by
    have hd : fderiv ℝ V (s,e) = 0 := by
      dsimp only [V]
      rw [show (fun q : S × E => σ q.1) = σ ∘ Prod.fst by rfl,
        fderiv_comp (s,e) (hσ.differentiable (by simp) s) differentiableAt_fst,
        fderiv_of_notMem_tsupport ℝ hs]
      simp
    simp [tubeBasePair,flatInversePair,dirDeriv,hd]
  have hid := affineEpigraph_global_log_coordinate_identity (μ := μ)
    hΩ hcv hu hp a L hD hK hzero bS bE ℓ hℓ hσ hc hσD
  have he := affineMaximal_tube_energy (μ := μ) hn hn9 hΩ hcv hu hp hm a L hD hK hzero
    bS bE hk hσ hc hσD
  apply tube_compact_log_energy_of_identity (n := (n : ℝ))
    (by exact_mod_cast hn) (by exact_mod_cast hn9)
    hσ.continuous hc hσD hM (hpair P P hP hP) (hpair F F hF hF) hEE
    (hpair A A hA hA) (hpair P A hP hA) (hpair F A hF hA)
    (hpair V V hV hV) (hpair V A hV hA) hQzero _ hid he
  intro s hs e he
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  have hq : (s,e) ∈ tubeOpenSet D := ⟨hs,hen⟩
  have hz := hpos (s,e) hq
  refine ⟨(tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 P,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 F,
    affineEpigraph_tube_angular_pair_nonneg hΩ hcv hu hp a L hD hK hzero hs he bS bE
      ((hF (s,e) hq).differentiableAt (by simp)),
    tubeBasePair_nonneg bS hz.2.2.le hz.1 A,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 V, ?_, ?_, ?_⟩
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 P A
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 F A
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 V A

end AffineBernstein
end

end OAI
