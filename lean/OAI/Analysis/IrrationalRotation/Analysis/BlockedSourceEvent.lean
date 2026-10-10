import OAI.Analysis.IrrationalRotation.Model.BlockedSourceEvent
import OAI.Analysis.IrrationalRotation.Rotation.BlockedCircleEvent
import OAI.Analysis.IrrationalRotation.Analysis.BlockedEventConditions
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import Mathlib.Analysis.PSeries

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

theorem mem_sourceRetainedEvent_iff {X : Type*} {m : ℕ → ℕ} {K : ℕ → ℝ}
    {r : X → ℝ} {x y : Sample m → X} {j : ℕ} {z : Sample m} :
    z ∈ sourceRetainedEvent m K r x y j ↔
      (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
      (∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
        2 / (m j : ℝ) < (z j i).2.2) ∧
      (∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ r (x z) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ 1 - r (y z) := by
  simp only [sourceRetainedEvent, Set.mem_sdiff, mem_union, not_or,
    not_mem_futureBad_iff, currentEvent, mem_ofPred_eq, not_lt]
  tauto

theorem retainedEvent_subset_sourceRetainedEvent {X : Type*}
    (m : ℕ → ℕ) (K : ℕ → ℝ) (r : X → ℝ) (x y : Sample m → X)
    (j : ℕ) (hj : 1 ≤ j) :
    retainedEvent m K r x y j ⊆ sourceRetainedEvent m K r x y j := by
  intro z hz
  obtain ⟨htag, hcur, hfuture, hx, hy⟩ := mem_retainedEvent_iff.mp hz
  have hdiv : 1 / ((j + 1 : ℕ) : ℝ) ≤ 1 / (j : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < j))
      (by exact_mod_cast Nat.le_succ j)
  exact mem_sourceRetainedEvent_iff.mpr ⟨htag, hcur, hfuture, hdiv.trans hx, hdiv.trans hy⟩

theorem source_kappa_nonneg (j : ℕ) : 0 ≤ ProductScaleData.kappa j := by
  unfold ProductScaleData.kappa
  positivity

theorem source_kappa_le (j : ℕ) : ProductScaleData.kappa j ≤ 1 / 100 := by
  apply one_div_le_one_div_of_le (by norm_num)
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
  linarith

theorem source_kappa_sq_summable : Summable (fun j => ProductScaleData.kappa j ^ 2) := by
  have hs : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  apply (ht.mul_left (1 / (100 : ℝ) ^ 2)).congr
  intro j
  dsimp [ProductScaleData.kappa]
  ring

theorem sourceLaw_isProbabilityMeasure {p : ProductScaleData}
    (hp : ProductScaleLaws p) (j : ℕ) : IsProbabilityMeasure (sourceLaw p j) :=
  law_isProbabilityMeasure hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) j

theorem sourceLaw_quasiMeasurePreserving_hybrid {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ)
    (sel : ℕ → Bool) :
    Measure.QuasiMeasurePreserving
      (toCircle ∘ (OrderedProductCoupling.hybridEndpoint sel ∘ flatten e))
      (sourceLaw p j) ProductModel.baseMeasure := by
  apply measurePreserving_toCircle.quasiMeasurePreserving.comp
  refine ⟨(OrderedProductCoupling.hybridEndpoint_measurable sel).comp
    (by unfold flatten; fun_prop), ?_⟩
  obtain ⟨H, _, _, _, _, hmap⟩ := exists_hybrid_density_of_blocks
    hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)
    source_kappa_sq_summable e j sel
  change (sourceLaw p j).map _ = _ at hmap
  rw [hmap]
  exact withDensity_absolutelyContinuous _ _

theorem sourceLaw_quasiMeasurePreserving_left {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    Measure.QuasiMeasurePreserving (circleLeftEndpoint e)
      (sourceLaw p j) ProductModel.baseMeasure := by
  exact sourceLaw_quasiMeasurePreserving_hybrid hp e j (fun _ => false)

theorem sourceLaw_quasiMeasurePreserving_right {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    Measure.QuasiMeasurePreserving (circleRightEndpoint e)
      (sourceLaw p j) ProductModel.baseMeasure := by
  exact sourceLaw_quasiMeasurePreserving_hybrid hp e j (fun _ => true)

theorem source_cutoff_ratio_tendsto {p : ProductScaleData} (hp : ProductScaleLaws p) :
    Tendsto (fun j => (p.K j : ℝ) / p.K (j + 1)) atTop (𝓝 0) := by
  have hH := SamplingHorizon.tendsto_horizon_ratio_of_pow_two_le
    (m := fun j => (p.m j : ℝ)) (K := fun j => (p.K j : ℝ))
    (fun j => by exact_mod_cast hp.m_ge_pow_self j)
    (fun j => by rw [hp.next_K j]; exact Nat.le_ceil _)
  apply squeeze_zero (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hH
  intro j
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j
    _ ≤ (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j) := by
      have hm : (100 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_100 j
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p.m j)
          (by linarith : (1 : ℝ) ≤ (7 / 10 : ℝ) * p.m j)

theorem eventually_sourceEvent_mass {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ}
    (hr : Measurable r) (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤ (sourceLaw p j).real (sourceEvent p e r j) := by
  have h := eventually_circle_retainedEvent_mass hp.m_ge_100
    source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)
    source_kappa_sq_summable e hp.real_K_pos hp.real_K_double
    (source_cutoff_ratio_tendsto hp) hr hi
  filter_upwards [h, eventually_ge_atTop 1] with j hj hjpos
  have := sourceLaw_isProbabilityMeasure hp j
  change Real.exp (-82) / 2 ≤ (sourceLaw p j).real _ at hj
  exact hj.trans (measureReal_mono
    (retainedEvent_subset_sourceRetainedEvent _ _ _ _ _ j hjpos))

end Invariant233.BlockedProductCoupling

end

end OAI
