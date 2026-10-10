import Mathlib
import OAI.Analysis.AffineBernstein.UniformActualCells

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section UniformLogCells
open Metric Filter

/-- A pushforward cell is bounded by any enclosing physical base cell. No
integrability or finiteness assumption on the density is used. -/
lemma logTubeMeasure_apply_le_cell {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure (Space k)) [SFinite μ] (D : Set (Space k)) (F : Space k × E → ℝ)
    {K Q : Set (Space k)} (hK : MeasurableSet K)
    (hsub : D ∩ logSpace ⁻¹' K ⊆ Q) :
    logTubeMeasure μ D F K ≤
      ∫⁻ q : Space k × sphere (0:E) 1, ENNReal.ofReal (F (tubeLift q))
        ∂(μ.restrict Q).prod (volume : Measure E).toSphere := by
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  rw [logTubeMeasure,Measure.map_apply hmap hK,
    withDensity_apply _ (hK.preimage hmap),Measure.restrict_restrict (hK.preimage hmap),
    Measure.restrict_prod_eq_prod_univ]
  apply lintegral_mono_set
  rintro q ⟨hq,hDq,-⟩
  exact ⟨hsub ⟨hDq,hq⟩,Set.mem_univ _⟩

/-- Closed unit cells in the actual logarithmic base coordinates. -/
def logarithmicUnitCell (k : ℕ) (z : Fin k → ℤ) : Set (Space k) :=
  {x | ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ (z i : ℝ)+1}

lemma isClosed_logarithmicUnitCell (k : ℕ) (z : Fin k → ℤ) :
    IsClosed (logarithmicUnitCell k z) := by
  change IsClosed {x : Space k | ∀ i, (z i:ℝ) ≤ x i ∧ x i ≤ (z i:ℝ)+1}
  rw [Set.ofPred_forall]
  apply isClosed_iInter fun i => ?_
  exact (isClosed_le continuous_const (EuclideanSpace.proj i).continuous).inter
    (isClosed_le (EuclideanSpace.proj i).continuous continuous_const)

/-- A logarithmic unit cell fits in the physical factor-four cell about the
exponential of its midpoint. The quantitative inclusion uses log(2)≥1/2. -/
lemma logarithmicUnitCell_preimage_subset {k : ℕ} (z : Fin k → ℤ) :
    positiveOrthant k ∩ logSpace ⁻¹' logarithmicUnitCell k z ⊆
      multiplicativeCell (expSpace (WithLp.toLp 2 (fun i => (z i:ℝ)+1/2))) := by
  rintro s ⟨hs,hz⟩ i
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hi : Real.log (s i) ∈ Set.Icc (z i:ℝ) ((z i:ℝ)+1) := hz i
  change Real.exp ((z i:ℝ)+1/2)/2 ≤ s i ∧ s i ≤ 2*Real.exp ((z i:ℝ)+1/2)
  constructor
  · apply (Real.log_le_log_iff (div_pos (Real.exp_pos _) (by norm_num)) (hs i)).mp
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num),Real.log_exp]
    linarith [hi.1]
  · apply (Real.log_le_log_iff (hs i) (mul_pos (by norm_num) (Real.exp_pos _))).mp
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    linarith [hi.2]

lemma affineEpigraphLogMeasure_unitCell_le {n k m d : ℕ} (hm : 1 ≤ m)
    (D : Set (Space k)) (hD : D ⊆ positiveOrthant k)
    (Ω : Set (Space n)) (u : Space n → ℝ) (a : Space n × ℝ)
    (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ (Space m)) (z : Fin k → ℤ) :
    affineEpigraphLogMeasure volume D Ω u a L bE (logarithmicUnitCell k z) ≤
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
      ∫⁻ q : Space k × sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (multiplicativeCell (expSpace (WithLp.toLp 2 (fun i => (z i:ℝ)+1/2))))).prod
          (volume : Measure (Space m)).toSphere := by
  let : NeZero m := ⟨by omega⟩
  let H := fun q : Space k × Space m =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let F := fun q : Space k × Space m =>
    tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE q * tubeLogMassWeight H q
  exact logTubeMeasure_apply_le_cell volume D F (isClosed_logarithmicUnitCell k z).measurableSet (by
    intro s hs
    exact logarithmicUnitCell_preimage_subset z ⟨hD hs.1,hs.2⟩)

/-- Uniform actual sigma control in every translated logarithmic unit cell,
from the original PDE, completeness, maximal-model normalization, and true
coordinate covariance. There is no cell-mass hypothesis. Suitable regular
base domains may be supplied later when applying the differential inequality. -/
theorem maximal_model_uniform_log_cells {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False) :
    ∃ Cσ : ℝ, 0 ≤ Cσ ∧
      ∀ (C : Set (Space k × Space m)), IsModelShape C →
      InAffineLimitFamily (sourceEpigraph Ω u) C →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ)),
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ (D : ℕ → Set (Space k)), (∀ j, D j ⊆ positiveOrthant k) →
      ∀ z : Fin k → ℤ, ∀ᶠ j in atTop,
      affineEpigraphLogMeasure volume (D j) Ω u (a j) (L j)
        ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE)
        (logarithmicUnitCell k z) ≤ ENNReal.ofReal Cσ := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨Cσ,hCσ,hbound⟩ := maximal_model_uniform_actual_cells hn hk hm e eE f
    hΩ hne hcv hu hp hmP hcomplete hmax
  refine ⟨Cσ.toReal,ENNReal.toReal_nonneg,?_⟩
  intro C hC hf a L hlim D hD z
  have hb := hbound C hC hf a L hlim (expSpace (WithLp.toLp 2 (fun i => (z i:ℝ)+1/2)))
    (fun i => Real.exp_pos _)
  filter_upwards [hb] with j hj
  rw [ENNReal.ofReal_toReal hCσ]
  exact (affineEpigraphLogMeasure_unitCell_le hm (D j) (hD j) Ω u (a j) (L j)
    ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) z).trans hj
end UniformLogCells


end AffineBernstein
end

end OAI
