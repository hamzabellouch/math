import Mathlib
import OAI.Probability.Ballisticity.Walk.GaussianPathFiniteLawSingleton
import OAI.Probability.Ballisticity.Renewal.PositiveOpenTest

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

def pathWindowEvent (τ : unitInterval) (δ ρ B : ℝ) : Set C(unitInterval,ℝ) :=
  {g | Set.MapsTo g (Metric.closedBall τ δ) (Set.Ioo (-ρ) ρ) ∧ ‖g‖ < B}

lemma isOpen_pathWindowEvent (τ : unitInterval) (δ ρ B : ℝ) :
    IsOpen (pathWindowEvent τ δ ρ B) :=
  (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_closedBall τ δ) isOpen_Ioo).inter
    (isOpen_lt continuous_norm continuous_const)

lemma pathWindowEvent_compl_nonempty (τ : unitInterval) (δ ρ B : ℝ) (hδ : 0 ≤ δ) :
    (pathWindowEvent τ δ ρ B)ᶜ.Nonempty := by
  refine ⟨ContinuousMap.const _ (ρ+1),?_⟩
  intro h
  have hh := h.1 (Metric.mem_closedBall_self hδ)
  change -ρ < ρ+1 ∧ ρ+1 < ρ at hh
  linarith [hh.2]

lemma endpoint_window_covered (τ : unitInterval) (ρ : ℝ) :
    {g : C(unitInterval,ℝ) | |g τ| < ρ} ⊆
      ⋃ n : ℕ, pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1) := by
  intro g hg
  have he : 0 < ρ-|g τ| := sub_pos.mpr hg
  obtain ⟨δ,hδ,hgδ⟩ := Metric.continuousAt_iff.mp g.continuous.continuousAt (ρ-|g τ|) he
  have hn : ∀ᶠ n : ℕ in atTop, 1/((n:ℝ)+1) < δ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ
  have hn' : ∀ᶠ n : ℕ in atTop, ‖g‖ < (n:ℝ)+1 := by
    have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop ‖g‖)
    filter_upwards [hh] with n hn
    linarith
  obtain ⟨n,hn,hbn⟩ := (hn.and hn').exists
  refine Set.mem_iUnion.mpr ⟨n,?_,hbn⟩
  intro t ht
  have hd := hgδ (lt_of_le_of_lt ht hn)
  have hgt : |g t| < ρ := by
    rw [Real.dist_eq] at hd
    have ha := abs_add_le (g t-g τ) (g τ)
    rw [sub_add_cancel] at ha
    linarith
  exact abs_lt.mp hgt

theorem positive_path_window_test (μ : Measure C(unitInterval,ℝ)) [IsFiniteMeasure μ]
    (τ : unitInterval) (ρ : ℝ) (hpos : 0 < μ {g | |g τ| < ρ}) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∃ F : C(unitInterval,ℝ) →ᵇ ℝ,
      (∀ g, 0 ≤ F g ∧ F g ≤ 1) ∧
      (∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval, dist t τ ≤ δ → |g t| < ρ) ∧
      0 < ∫ g, F g ∂μ := by
  have hc := endpoint_window_covered τ ρ
  have hn : ∃ n : ℕ, 0 < μ (pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1)) := by
    by_contra! h
    have hz : ∀ n : ℕ, μ (pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1)) = 0 :=
      fun n => le_antisymm (h n) zero_le
    have hu := measure_iUnion_null hz
    exact (ne_of_gt hpos) (measure_mono_null hc hu)
  obtain ⟨n,hn⟩ := hn
  have hB : 0 < (n:ℝ)+1 := by positivity
  have hδ : 0 < 1/((n:ℝ)+1) := by positivity
  obtain ⟨F,hF,hFs,hFp⟩ := positive_bounded_test_of_open μ
    (pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1)) (isOpen_pathWindowEvent _ _ _ _)
    (pathWindowEvent_compl_nonempty _ _ _ _ hδ.le) hn
  refine ⟨_,_,hδ,hB,F,hF,?_,hFp⟩
  intro g hg
  have hh := hFs g hg
  refine ⟨hh.2,fun t ht => ?_⟩
  exact abs_lt.mpr (hh.1 ht)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma gaussianReal_centered_window_pos (v : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianReal 0 v {z : ℝ | |z| < ρ} := by
  by_cases hv : v = 0
  · rw [hv,gaussianReal_zero_var]
    simp [hρ]
  · apply pos_iff_ne_zero.mpr
    intro hz
    have hh := gaussianReal_absolutelyContinuous' 0 hv hz
    have hs : {z : ℝ | |z| < ρ} = Set.Ioo (-ρ) ρ := by
      ext z
      change |z| < ρ ↔ -ρ < z ∧ z < ρ
      exact abs_lt
    rw [hs,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hh
    linarith

theorem brownian_positive_common_time_window (W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (τ : unitInterval) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∃ F : C(unitInterval,ℝ) →ᵇ ℝ,
      (∀ g, 0 ≤ F g ∧ F g ≤ 1) ∧
      (∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval, dist t τ ≤ δ → |g t| < ρ) ∧
      0 < ∫ g, F g ∂(W : Measure C(unitInterval,ℝ)) := by
  apply positive_path_window_test
  have hp := gaussianReal_centered_window_pos (Real.toNNReal (T*(τ:ℝ))) hρ
  rw [← wiener_path_eval W T hW τ] at hp
  simpa only [Measure.map_apply (continuous_eval_const τ).measurable
    (isOpen_lt (continuous_abs) continuous_const).measurableSet,Set.preimage_ofPred_eq] using hp

end DirectionalTransience

end

end

end OAI
