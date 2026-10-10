import Mathlib
import OAI.Probability.Ballisticity.Estimates.OperationalMarkBounds

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

omit [IsProbabilityMeasure ν] in
lemma dropCut_integrable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] (B : ℝ≥0) :
    Integrable (fun ω => cutENNReal B (ENNReal.ofReal (C.dropAt hef N ω i))) Q := by
  apply Integrable.of_bound
    (((cutENNReal B).continuous.measurable.comp (C.dropAt_measurable hef N i).ennreal_ofReal).aestronglyMeasurable) B
  filter_upwards [] with ω
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs,abs_of_nonneg (cutENNReal_nonneg _ _)]
  exact cutENNReal_le _ _

lemma raw_dropCut_integral (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] (B : ℝ≥0) :
    (∫ Y, dropMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)) =
      ∫ ω, ∑ i∈Finset.range N, cutENNReal B (ENNReal.ofReal (C.dropAt hef N ω i)) ∂Q := by
  rw [actualOccupationRaw_env_test e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.activeCount_measurable hef N) (dropMarkCut e B 0)
    (fun i ω => cutENNReal B (ENNReal.ofReal (C.dropAt hef N ω i)))
    (fun i => (cutENNReal B).continuous.measurable.comp (C.dropAt_measurable hef N i).ennreal_ofReal)
    (fun i X => C.dropCut_actual hef N i B X)]
  rw [integral_finsetSum (Finset.range N) (fun i _ => C.dropCut_integrable hef N i Q B)]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro ω hω
  have hi : C.activeCount hef N ω ≤ i := Nat.le_of_not_lt hω
  have hz := EpisodeChainLedger.dropMark_inactive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i hi
  change C.dropAt hef N ω i=0 at hz
  rw [hz]
  simp [cutENNReal]

omit [IsProbabilityMeasure ν] in
lemma shortDrop_integrable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i L : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u) :
    Integrable (fun ω => if C.stagesAt hef N ω i ≤ L then C.dropAt hef N ω i else 0) Q := by
  convert Integrable.piecewise
    (measurableSet_le (C.stagesAt_measurable hef N i) (measurable_const : Measurable (fun _ : Environment d => L)))
    (C.dropAt_integrable hef N i Q hQ).integrableOn (integrable_const (0:ℝ)).integrableOn using 1
  all_goals rfl

lemma raw_dropCut_lower (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N L : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u)
    (B : ℝ≥0) (hB : C.injectionCost+2*C.b*L ≤ B) :
    (∫ ω, ∑ i∈Finset.range N, if C.stagesAt hef N ω i ≤ L then C.dropAt hef N ω i else 0 ∂Q) ≤
    (∫ Y, dropMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)) := by
  rw [C.raw_dropCut_integral]
  apply integral_mono_ae
    (integrable_finsetSum _ (fun i _ => C.shortDrop_integrable hef N i L Q hQ))
    (integrable_finsetSum _ (fun i _ => C.dropCut_integrable hef N i Q B))
  filter_upwards [hQ] with ω hω
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨hc,hbound⟩ := C.dropAt_bounds hef N i ω hω
  rw [cut_ofReal_eq_min B _ hc]
  split
  · rename_i hi
    have hj : (C.stagesAt hef N ω i:ℝ) ≤ L := Nat.cast_le.mpr hi
    have hb : C.dropAt hef N ω i ≤ B := by nlinarith only [hbound,hj,hB,C.hb]
    exact le_min le_rfl hb
  · exact le_min hc B.coe_nonneg

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma raw_dropCut_upper (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u) (B : ℝ≥0) :
    (∫ Y, dropMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)) ≤
      C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) +
      2*C.b*(∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q) := by
  have hiM := EpisodeChainLedger.number_integrable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N Q N
  have hiJ := (EpisodeChainLedger.counts_integrable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N Q N).1
  change Integrable (fun ω => (C.activeCount hef N ω:ℝ)) Q at hiM
  rw [C.raw_dropCut_integral,←integral_const_mul,←integral_const_mul,
    ←integral_add (hiM.const_mul _) (hiJ.const_mul _)]
  apply integral_mono_ae (integrable_finsetSum _ (fun i _ => C.dropCut_integrable hef N i Q B))
    ((hiM.const_mul _).add (hiJ.const_mul _))
  filter_upwards [hQ] with ω hω
  have hc : (∑ i∈Finset.range N, (cutENNReal B) (ENNReal.ofReal (C.dropAt hef N ω i))) ≤
      ∑ i∈Finset.range N, C.dropAt hef N ω i := Finset.sum_le_sum (fun i _ => by
    rw [cut_ofReal_eq_min B _ (C.dropAt_bounds hef N i ω hω).1]
    exact min_le_left (C.dropAt hef N ω i) (B:ℝ))
  apply hc.trans
  change ∑ i∈Finset.range N, EpisodeChainLedger.dropMark (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i ≤ _
  rw [EpisodeChainLedger.dropMark_total]
  exact EpisodeChainLedger.total_drop_bound_local (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N C.order C.hf.le C.hb.le
    (lt_of_lt_of_le zero_lt_one C.hs) C.height_pos C.κ C.hκ0 C.hκ1
    (lt_of_lt_of_le (by norm_num) C.hk) C.hbκ ω hω

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma mark_lintegral_bound_of_weak_limit
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs atTop (𝓝 μ)) (F : C(X,ℝ≥0∞)) (A : ℝ)
    (hbound : ∀ n (B : ℝ≥0), ∫ x, cutENNReal B (F x) ∂(μs n : Measure X) ≤ A) :
    (∫⁻ x, F x ∂(μ : Measure X)) ≤ ENNReal.ofReal A := by
  have hcut (B : ℝ≥0) : ∫ x, cutENNReal B (F x) ∂(μ : Measure X) ≤ A := by
    let G : C(X,ℝ) := (cutENNReal B).comp F
    exact le_of_tendsto ((ProbabilityMeasure.continuous_integral_continuousMap G).continuousAt.tendsto.comp hlim)
      (Filter.Eventually.of_forall (fun n => hbound n B))
  have hcut' (n : ℕ) : (∫⁻ x, min (F x) (n:ℝ≥0∞) ∂(μ : Measure X)) ≤ ENNReal.ofReal A := by
    let G : C(X,ℝ) := (cutENNReal (n:ℝ≥0)).comp F
    have hG : Integrable G (μ : Measure X) :=
      G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hn := ENNReal.ofReal_le_ofReal (hcut n)
    change ENNReal.ofReal (∫ x, G x ∂(μ : Measure X)) ≤ ENNReal.ofReal A at hn
    rw [ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall (fun x => cutENNReal_nonneg _ _))] at hn
    convert hn using 1
    apply lintegral_congr
    intro x
    change min (F x) (n:ℝ≥0∞) = ENNReal.ofReal ((min (F x) ((n:ℝ≥0):ℝ≥0∞)).toReal)
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    simp
  have he (x : X) : (⨆ n : ℕ, min (F x) (n:ℝ≥0∞))=F x := by
    rw [←inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
  rw [show (fun x => F x)=(fun x => ⨆ n : ℕ, min (F x) (n:ℝ≥0∞)) from funext (fun x => (he x).symm)]
  rw [lintegral_iSup (fun n => F.continuous.measurable.min measurable_const)
    (fun n m h x => min_le_min_left _ (by exact_mod_cast h))]
  exact iSup_le hcut'

lemma mark_integrable_of_lintegral_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) (hF : Measurable F) (A : ℝ)
    (hbound : (∫⁻ x, F x ∂μ) ≤ ENNReal.ofReal A) :
    (∀ᵐ x ∂μ, F x<∞) ∧ Integrable (fun x => (F x).toReal) μ := by
  have hfin : (∫⁻ x, F x ∂μ)<∞ := hbound.trans_lt ENNReal.ofReal_lt_top
  exact ⟨ae_lt_top' hF.aemeasurable hfin.ne,
    integrable_toReal_of_lintegral_ne_top hF.aemeasurable hfin.ne⟩

end DirectionalTransience

end

end OAI
