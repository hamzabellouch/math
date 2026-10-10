import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedSigma
import OAI.Analysis.AffineBernstein.NormalizedSigmaTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section UniformActualCells
open Filter Metric

/-- The multiplicative cell with positive center `s`, exactly the cell of
bounds.tex:219: no choice of transverse normalization occurs in this set. -/
def multiplicativeCell {k : ℕ} (s : Space k) : Set (Space k) :=
  {x | ∀ i, s i / 2 ≤ x i ∧ x i ≤ 2*s i}

lemma multiplicativeCell_eq_image {k : ℕ} (s : Space k) (hs : ∀ i, 0 < s i) :
    multiplicativeCell s = (positiveBaseEquiv s hs).symm '' normalizedCell k := by
  ext x
  constructor
  · intro hx
    refine ⟨positiveBaseEquiv s hs x,?_,by simp⟩
    intro i
    change 1/2 ≤ x i/s i ∧ x i/s i ≤ 2
    constructor
    · apply (le_div_iff₀ (hs i)).mpr
      linarith [(hx i).1]
    · exact (div_le_iff₀ (hs i)).mpr (by linarith [(hx i).2])
  · rintro ⟨y,hy,rfl⟩ i
    change s i/2 ≤ s i*y i ∧ s i*y i ≤ 2*s i
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hy i).1 (hs i).le
      linarith
    · have hh := mul_le_mul_of_nonneg_left (hy i).2 (hs i).le
      linarith

/-- Uniform full actual-sigma mass of every multiplicative cell for a maximal
model. The constant is independent of the model, its approximating coordinates,
and the position of the cell. The eventual threshold may depend on the cell.
This is the missing quantitative geometric producer, not a hypothesis about
sigma mass. The sole maximality condition is the source's selection of the
largest possible number of orthant directions. -/
theorem maximal_model_uniform_actual_cells {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False) :
    ∃ Cσ : ℝ≥0∞, Cσ ≠ ⊤ ∧
      ∀ (C : Set (Space k × Space m)), IsModelShape C →
      InAffineLimitFamily (sourceEpigraph Ω u) C →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ)),
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ s : Space k, (∀ i, 0 < s i) → ∀ᶠ j in atTop,
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (multiplicativeCell s)).prod (volume : Measure (Space m)).toSphere) ≤ Cσ := by
  let : NeZero k := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hneE : (sourceEpigraph Ω u).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,u x),hx,le_rfl⟩
  obtain ⟨c,hc,hnorm⟩ := uniform_model_fiber_normalization hm hclosed hneE hmax
  have hr : 0 < 2/(c+1) := div_pos (by norm_num) (by linarith)
  obtain ⟨Cσ,hCσ,hbound⟩ := normalized_model_uniform_actual_sigma hn hk hm e eE f hr
    (show (0:ℝ) ≤ 2*m by positivity)
  refine ⟨Cσ,hCσ,?_⟩
  intro C hC hf a L hlim s hs
  obtain ⟨A,hmod,hfam,hin,hout⟩ := hnorm C hC hf s hs
  let B := positiveBaseEquiv s hs
  let N := B.prodCongr A
  let L' := fun j => N.symm.trans (L j)
  let C' := N '' C
  have heq (j : ℕ) : affineEpigraphPullback Ω u (a j) (L' j) =
      N '' affineEpigraphPullback Ω u (a j) (L j) :=
    affineEpigraphPullback_normalize Ω u (a j) (L j) N
  have hclj (j : ℕ) : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) :=
    affineEpigraphPullback_isClosed hclosed (a j) (L j)
  have hnej (j : ℕ) : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have hlim' : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L' j)) C' := by
    have hh := hlim.homeomorph hC.closed ⟨0,hC.zero_mem⟩ hclj hnej N.toHomeomorph
    change LocalDistanceConverges (fun j => N '' affineEpigraphPullback Ω u (a j) (L j)) C' at hh
    simpa only [heq] using hh
  have hclj' (j : ℕ) : IsClosed (affineEpigraphPullback Ω u (a j) (L' j)) :=
    affineEpigraphPullback_isClosed hclosed (a j) (L' j)
  have hcvj' (j : ℕ) : Convex ℝ (affineEpigraphPullback Ω u (a j) (L' j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage
      (L' j).toLinearMap
  have hnej' (j : ℕ) : (affineEpigraphPullback Ω u (a j) (L' j)).Nonempty := by
    rw [heq]
    exact (hnej j).image N
  have hbnd := hbound hΩ hne hcv hu hp hmP hcomplete a L' C' hmod hin hout hlim'
  have hfib := hlim'.eventually_normalized_fibers hmod hclj' hcvj' hnej' hr
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1) (by norm_num : (1:ℝ)≤4) hin hout
  have hncard : n = k+d := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_sum] using hh
  have hcell : B '' multiplicativeCell s = normalizedCell k := by
    rw [multiplicativeCell_eq_image s hs,Set.image_image]
    simp only [B,ContinuousLinearEquiv.apply_symm_apply,Set.image_id']
  have hQ : MeasurableSet (multiplicativeCell s) := by
    rw [multiplicativeCell_eq_image s hs]
    exact B.symm.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (isCompact_normalizedCell k).measurableSet
  filter_upwards [hbnd,hfib] with j hj hfj
  have hK (t : Space k) (ht : t ∈ normalizedCellDomain k) :
      IsCompact {y | (t,y) ∈ affineEpigraphPullback Ω u (a j) (L' j)} := by
    exact (isCompact_closedBall (0:Space m) _).of_isClosed_subset
      ((hclj' j).preimage (continuous_const.prodMk continuous_id))
      (hfj t (fun i => ⟨(ht i).1.le,(ht i).2.le⟩)).2.2
  have hz (t : Space k) (ht : t ∈ normalizedCellDomain k) :
      (0:Space m) ∈ interior {y | (t,y) ∈ affineEpigraphPullback Ω u (a j) (L' j)} :=
    (hfj t (fun i => ⟨(ht i).1.le,(ht i).2.le⟩)).2.1
  have he := affineEpigraph_sigma_normalization hm hncard
    ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) hΩ hcv hu hp (a j) (L j) B A
    (fun i => (s i)⁻¹) (fun i => inv_ne_zero (hs i).ne')
    (fun t i => by simp [B,div_eq_mul_inv,mul_comm])
    (isOpen_normalizedCellDomain k) hQ (by rw [hcell]; exact normalizedCell_subset_domain k)
    (fun t ht i => ne_of_gt (lt_of_lt_of_le (half_pos (hs i)) (ht i).1)) hK hz
  dsimp only at he ⊢
  rw [he,hcell]
  exact hj
end UniformActualCells


end AffineBernstein
end

end OAI
