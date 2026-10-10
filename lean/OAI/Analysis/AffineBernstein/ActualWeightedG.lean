import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeWeights
import OAI.Analysis.AffineBernstein.BaseLogIdentity
import OAI.Analysis.AffineBernstein.ActualWeightedBase

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The genuine base integration formula, now with literal μ₀ and inverse-base metric. -/
theorem affineEpigraph_base_g_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ g : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hσD : tsupport σ ⊆ D) (hg : ContDiffOn ℝ ∞ g D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun s => Real.log (H (s,e))
    let F := fun s => invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)
    let B := fun s => tubeBaseMatrix H (s,e) bS
    let M := fun s => tubeMeasureDensity n H bS bE (s,e)
    (∫ s, M s*σ s^2*H (s,e)*(flatInverseTrace (B s) bS g s-
        (n : ℝ)*flatInversePair (B s) bS P g s-
        (((n : ℝ)+2)/2)*flatInversePair (B s) bS F g s) ∂μ) =
      -2*(∫ s, M s*σ s*H (s,e)*flatInversePair (B s) bS σ g s ∂μ) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun s => Real.log (H (s,e))
  let F := fun s => invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)
  let B := fun s => tubeBaseMatrix H (s,e) bS
  let M := fun s => tubeMeasureDensity n H bS bE (s,e)
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  have hH (s : S) (hs : s ∈ D) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hen).1
  have hpos (s : S) (hs : s ∈ D) := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs hen bS bE
  have hmat (s : S) (hs : s ∈ D) : flatBlockHessian (fun s => -H (s,e)) bS s = B s := by
    rw [flatBlockHessian_neg]
    exact (tubeBaseMatrix_eq_slice (hH s hs) bS).symm
  have hweight (s : S) (hs : s ∈ D) : Real.exp (-(n : ℝ)*P s-(((n : ℝ)+2)/2)*F s) = M s*H (s,e)/(B s).det := by
    exact (tubeMeasureDensity_base bS bE (tube_dimension_eq bS bE L) he
      (hpos s hs).2.2 (hpos s hs).1.det_pos (hpos s hs).2.1).symm
  have hh := affineEpigraph_base_weighted_ibp (μ := μ) hΩ hcv hu hp a L hD hK hzero hen
    bS bE hσ hc hσD hg
  dsimp only at hh
  change (∫ s, M s*σ s^2*H (s,e)*(flatInverseTrace (B s) bS g s-
        (n : ℝ)*flatInversePair (B s) bS P g s-
        (((n : ℝ)+2)/2)*flatInversePair (B s) bS F g s) ∂μ) =
      -2*(∫ s, M s*σ s*H (s,e)*flatInversePair (B s) bS σ g s ∂μ)
  convert hh using 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hsd := hσD hs
      have hdet' : (flatBlockHessian (fun s => -H (s,e)) bS s).det ≠ 0 := by
        rw [hmat s hsd]; exact (hpos s hsd).1.det_pos.ne'
      change M s*σ s^2*H (s,e)*(_-_-_) =
        Real.exp (-(n : ℝ)*P s-(((n : ℝ)+2)/2)*F s)*σ s^2*_
      rw [flatCofactorTrace_eq_det_mul bS _ _ hdet',
        flatCofactorPair_eq_det_mul bS _ _ _ hdet',
        flatCofactorPair_eq_det_mul bS _ _ _ hdet',hmat s hsd,hweight s hsd]
      change M s*σ s^2*H (s,e)*(flatInverseTrace (B s) bS g s-
        (n : ℝ)*flatInversePair (B s) bS P g s-(((n : ℝ)+2)/2)*flatInversePair (B s) bS F g s) =
        M s*H (s,e)/(B s).det*σ s^2*((B s).det*flatInverseTrace (B s) bS g s-
        (n : ℝ)*((B s).det*flatInversePair (B s) bS P g s)-(((n : ℝ)+2)/2)*((B s).det*flatInversePair (B s) bS F g s))
      have hb : (B s).det ≠ 0 := (hpos s hsd).1.det_pos.ne'
      field_simp [hb]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hsd := hσD hs
      change M s*σ s*H (s,e)*flatInversePair (B s) bS σ g s =
        Real.exp (-(n : ℝ)*P s-(((n : ℝ)+2)/2)*F s)*σ s*flatCofactorPair (fun s => -H (s,e)) bS σ g s
      rw [flatCofactorPair_eq_det_mul bS _ _ _ (by rw [hmat s hsd]; exact (hpos s hsd).1.det_pos.ne'),hmat s hsd,hweight s hsd]
      have hb : (B s).det ≠ 0 := (hpos s hsd).1.det_pos.ne'
      field_simp [hb]
    · simp [image_eq_zero_of_notMem_tsupport hs]

end AffineBernstein
end

end OAI
