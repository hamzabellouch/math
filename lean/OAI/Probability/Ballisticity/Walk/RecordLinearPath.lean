import Mathlib
import OAI.Probability.Ballisticity.Coupling.WeakLimitBoundedFreshMap
import OAI.Probability.Ballisticity.Estimates.NoDropApproxError
import OAI.Probability.Ballisticity.Estimates.HighRecordCount
import OAI.Probability.Ballisticity.Geometry.HeightPolygonRandomShiftSmall

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def recordLinearPath {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (X : Path d) : C(unitInterval,ℝ) :=
  heightPolygon (fun h => signedCoordinate f (recordIndexPosition ℓ h X)-(h:ℝ)*θ) r n T

lemma measurable_recordLinearPath {d : ℕ} (ℓ : Vector d) (f : Direction d) (θ r n T : ℝ) :
    Measurable (recordLinearPath ℓ f θ r n T) :=
  measurable_heightPolygon _ (fun h =>
    ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h)).sub_const ((h:ℝ)*θ)) _ _ _

lemma recordLinearPath_suffix_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (θ r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hθ : Tendsto (fun i => θ i/r i) atTop (𝓝 0))
    (J : ℝ) (hJ : 0 ≤ J) {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (recordLinearPath ℓ f (θ i) (r i) (n i) (T+1))))) :
    TendstoInMeasure (conditionedLaw ν ℓ) (fun i X =>
      recordLinearPath ℓ f (θ i) (r i) (n i) T (highSuffix ℓ J X)-
        recordLinearPath ℓ f (θ i) (r i) (n i) T X) atTop 0 := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let H := highRecordCount ℓ J
  let D := fun X => signedCoordinate f (highRecordPosition ℓ J X)
  have hH : Measurable H := measurable_highRecordCount ℓ J hJ
  have hD : Measurable D := (measurable_of_countable (signedCoordinate f)).comp (measurable_highRecordPosition ℓ J hJ)
  let F := fun i h X => signedCoordinate f (recordIndexPosition ℓ h X)-(h:ℝ)*θ i
  have hF : ∀ i h, Measurable (F i h) := fun i h =>
    ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h)).sub_const ((h:ℝ)*θ i)
  let c := fun i X => (H X:ℝ)*θ i-D X
  have hc : TendstoInMeasure μ (fun i X => c i X/r i) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro i
      exact (((((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp hH).mul_const _).sub hD).div_const _).aestronglyMeasurable
    · apply ae_of_all
      intro X
      have hh := (hθ.const_mul (H X:ℝ)).sub (tendsto_const_nhds.div_atTop hr :
        Tendsto (fun i => D X/r i) atTop (𝓝 0))
      simpa only [mul_zero,sub_zero,Pi.zero_apply,c,sub_div,mul_div_assoc] using hh
  have hs := heightPolygon_random_shift_small μ F hF r n hn H hH c hc hT ht
  apply hs.congr _ (Filter.EventuallyEq.rfl)
  intro i
  filter_upwards [conditioned_highSuffix_recordPosition ν ℓ htrans J hJ] with X hX
  congr 1
  congr 1
  funext h
  dsimp only [recordLinearPath,F,c,H,D]
  rw [hX h,signedCoordinate_sub,Nat.cast_add]
  ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weighted_recordLinearPath_limit {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (θ r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hθ : Tendsto (fun i => θ i/r i) atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (recordLinearPath ℓ f (θ i) (r i) (n i) (T+1)))))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim :
      letI : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
      TendstoInDistribution (fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T)
        atTop id (fun _ => conditionedLaw ν ℓ) W)
    (J : ℝ) (hJ : 0 ≤ J) (g : ℕ → Environment d → ℝ≥0∞)
    (hg : ∀ i, @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ (g i))
    (hgle : ∀ i ω, g i ω ≤ 1) (c : ℝ≥0∞) (hc : 0 < c)
    (hcmass : ∀ i, c ≤ weightedConditioned ν ℓ (g i) Set.univ) :
    letI : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
    letI : ∀ i, IsFiniteMeasure (weightedConditioned ν ℓ (g i)) := fun i =>
      weightedConditioned_finite ν ℓ (g i) ((hg i).mono (rowSigma_le _) le_rfl) (hgle i)
    letI : ∀ i, IsProbabilityMeasure (normalizedMeasure (weightedConditioned ν ℓ (g i))) := fun i =>
      normalizedMeasure_probability (weightedConditioned ν ℓ (g i))
        (ne_of_gt (hc.trans_le (hcmass i)))
    TendstoInDistribution (fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T)
      atTop id (fun i => normalizedMeasure (weightedConditioned ν ℓ (g i))) W := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : ∀ i, IsFiniteMeasure (weightedConditioned ν ℓ (g i)) := fun i =>
    weightedConditioned_finite ν ℓ (g i) ((hg i).mono (rowSigma_le _) le_rfl) (hgle i)
  let η := fun i => normalizedMeasure (weightedConditioned ν ℓ (g i))
  let : ∀ i, IsProbabilityMeasure (η i) := fun i => normalizedMeasure_probability _
    (ne_of_gt (hc.trans_le (hcmass i)))
  let F := fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T
  have hF : ∀ i, Measurable (F i) := fun i => measurable_recordLinearPath _ _ _ _ _ _
  have hl : Tendsto (fun i => ProbabilityMeasure.map (⟨μ,inferInstance⟩ : ProbabilityMeasure (Path d))
      (F i)) atTop (𝓝 W) := by
    have hh := hlim.tendsto
    change Tendsto (fun i => ProbabilityMeasure.map (⟨μ,inferInstance⟩ : ProbabilityMeasure (Path d))
      (F i)) atTop (𝓝 (W.map id)) at hh
    have he : W.map id = W := Subtype.ext Measure.map_id
    rw [he] at hh
    exact hh
  have hs := recordLinearPath_suffix_small ν ℓ htrans f θ r n hr hn hθ J hJ hT ht
  have hclose : ∀ ε, 0 < ε → Tendsto (fun i => μ.real
      {X | ε ≤ dist (F i (highSuffix ℓ J X)) (F i X)}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [Pi.zero_apply,sub_zero,dist_eq_norm,F] using
      (tendstoInMeasure_iff_measureReal_norm.mp hs ε hε)
  refine ⟨fun i => (hF i).aemeasurable,measurable_id.aemeasurable,?_⟩
  have hout := weak_limit_of_bounded_fresh_map μ η (highSuffix ℓ J)
    (measurable_highSuffix ℓ J hJ)
    (fun i => normalized_weightedConditioned_highSuffix ν ℓ htrans J hJ (g i) (hg i)
      (hgle i) (ne_of_gt (hc.trans_le (hcmass i)))) c⁻¹ (ENNReal.inv_ne_top.mpr hc.ne')
    (fun i => normalized_weightedConditioned_le ν ℓ (g i) ((hg i).mono (rowSigma_le _) le_rfl)
      (hgle i) c (hcmass i)) F hF W hl hclose
  change Tendsto (fun i => ProbabilityMeasure.map (⟨η i,inferInstance⟩ : ProbabilityMeasure (Path d))
    (F i)) atTop (𝓝 (W.map id))
  have he : W.map id = W := Subtype.ext Measure.map_id
  rw [he]
  exact hout

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma noDropWeighted_recordLinearPath_limit {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (θ r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hθ : Tendsto (fun i => θ i/r i) atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν (realPosition (step e))).map
      (recordLinearPath (realPosition (step e)) f (θ i) (r i) (n i) (T+1)))))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim :
      letI : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
        conditionedLaw_probability ν _ (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
      TendstoInDistribution (fun i => recordLinearPath (realPosition (step e)) f (θ i) (r i) (n i) T)
        atTop id (fun _ => conditionedLaw ν (realPosition (step e))) W)
    (y : ℕ → Lattice d) (hy : ∀ i, signedHeight e (y i) = 0)
    (c : ℝ≥0∞) (hc : 0 < c)
    (hcmass : ∀ i, c ≤ weightedConditioned ν (realPosition (step e))
      (noDropQuenched (realPosition (step e)) (y i)) Set.univ) :
    letI : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
      conditionedLaw_probability ν _ (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    letI : ∀ i, IsFiniteMeasure (weightedConditioned ν (realPosition (step e))
      (noDropQuenched (realPosition (step e)) (y i))) := fun _i =>
      weightedConditioned_finite ν _ _ (measurable_noDropQuenched _ _) (fun _ => prob_le_one)
    letI : ∀ i, IsProbabilityMeasure (normalizedMeasure (weightedConditioned ν (realPosition (step e))
      (noDropQuenched (realPosition (step e)) (y i)))) := fun i =>
        normalizedMeasure_probability _ (ne_of_gt (hc.trans_le (hcmass i)))
    TendstoInDistribution (fun i => recordLinearPath (realPosition (step e)) f (θ i) (r i) (n i) T)
      atTop id (fun i => normalizedMeasure (weightedConditioned ν (realPosition (step e))
        (noDropQuenched (realPosition (step e)) (y i)))) W := by
  let ℓ := realPosition (step e)
  let p := annealedLaw ν (NoDrop ℓ 0)
  have hp : p ≠ 0 := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let μ i := weightedConditioned ν ℓ (noDropQuenched ℓ (y i))
  let η J i := weightedConditioned ν ℓ (noDropFinite ℓ (y i) J)
  let : ∀ i, IsFiniteMeasure (μ i) := fun i => weightedConditioned_finite ν ℓ _
    (measurable_noDropQuenched ℓ (y i)) (fun _ => prob_le_one)
  let : ∀ J i, IsFiniteMeasure (η J i) := fun J i => weightedConditioned_finite ν ℓ _
    (noDropFinite_measurable ℓ (y i) J) (fun _ => prob_le_one)
  let : ∀ i, IsProbabilityMeasure (normalizedMeasure (μ i)) := fun i =>
    normalizedMeasure_probability _ (ne_of_gt (hc.trans_le (hcmass i)))
  have hmono (J i : ℕ) : μ i ≤ η J i := weightedConditioned_mono ν ℓ _ _
    (measurable_noDropQuenched ℓ (y i)) (noDropFinite_measurable ℓ (y i) J)
    (fun ω => noDropQuenched_le_finite ℓ (y i) ω J)
  have heta (J i : ℕ) : c ≤ η J i Set.univ := (hcmass i).trans (hmono J i Set.univ)
  let : ∀ J i, IsProbabilityMeasure (normalizedMeasure (η J i)) := fun J i =>
    normalizedMeasure_probability _ (ne_of_gt (hc.trans_le (heta J i)))
  let F i := recordLinearPath ℓ f (θ i) (r i) (n i) T
  have hF : ∀ i, Measurable (F i) := fun i => measurable_recordLinearPath _ _ _ _ _ _
  let A i : ProbabilityMeasure C(unitInterval,ℝ) :=
    ProbabilityMeasure.map (⟨normalizedMeasure (μ i),inferInstance⟩ : ProbabilityMeasure (Path d)) (F i)
  let B J i : ProbabilityMeasure C(unitInterval,ℝ) :=
    ProbabilityMeasure.map (⟨normalizedMeasure (η J i),inferInstance⟩ : ProbabilityMeasure (Path d)) (F i)
  have heW : W.map id = W := Subtype.ext Measure.map_id
  have hB (J : ℕ) : Tendsto (B J) atTop (𝓝 W) := by
    have h := weighted_recordLinearPath_limit ν ℓ htrans f θ r n hr hn hθ hT ht W hlim
      (J:ℝ) (Nat.cast_nonneg J) (fun i => noDropFinite ℓ (y i) J)
      (fun i => noDropFinite_lower_rows e (y i) (hy i) J) (fun _ _ => prob_le_one) c hc (heta J)
    have hh := h.tendsto
    change Tendsto (B J) atTop (𝓝 (W.map id)) at hh
    rwa [heW] at hh
  have hd : Tendsto (fun J => (c⁻¹*(p⁻¹*noDropApproxError ν ℓ J)).toReal) atTop (𝓝 0) := by
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (noDropApproxError_tendsto ν ℓ)).const_mul ((c⁻¹).toReal*(p⁻¹).toReal)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_zero,mul_zero,Function.comp_def,mul_assoc] using h
  have hclose (J i : ℕ) : levyProkhorovDist (A i : Measure C(unitInterval,ℝ)) (B J i : Measure C(unitInterval,ℝ)) ≤
      (c⁻¹*(p⁻¹*noDropApproxError ν ℓ J)).toReal := by
    rw [levyProkhorovDist_comm]
    exact levyProkhorov_normalized_map_le (μ i) (η J i) (hmono J i)
      (p⁻¹*noDropApproxError ν ℓ J) c hc
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp)
        (ne_of_lt ((noDropApproxError_le_one ν ℓ J).trans_lt (by simp))))
      (hcmass i) (fun A hA => weightedConditioned_noDrop_approx ν ℓ (y i) J A hA) (F i) (hF i)
  refine ⟨fun i => (hF i).aemeasurable,measurable_id.aemeasurable,?_⟩
  change Tendsto A atTop (𝓝 (W.map id))
  rw [heW]
  exact weak_limit_of_uniform_approximation A B W _ hd hB hclose

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
