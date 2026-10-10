import OAI.Analysis.IrrationalRotation.Operators.BlockedProjectionWindow
import OAI.Analysis.IrrationalRotation.Model.PhaseBlocks

namespace OAI

open scoped BigOperators

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.BlockedProductCoupling

@[simp] theorem unflatten_flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) (z : Sample m) :
    unflatten e (flatten e z) = z := by
  funext s i
  change (fun q : Σ t, Fin (m t) => z q.1 q.2) (e (e.symm ⟨s, i⟩)) = z s i
  rw [e.apply_symm_apply]

@[simp] theorem flatten_unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (ω : OrderedProductCoupling.Sample) : flatten e (unflatten e ω) = ω := by
  funext i
  simp [unflatten, flatten]

theorem measurable_unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Measurable (unflatten e) := by unfold unflatten; fun_prop

theorem measurable_flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Measurable (flatten e) := by unfold flatten; fun_prop

theorem source_measurePreserving_flatten {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    MeasurePreserving (flatten e) (sourceLaw p j)
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)) := by
  refine ⟨measurable_flatten e, ?_⟩
  change (law _ _ _ _ _).map _ = _
  rw [law_map_flatten hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)]
  congr 1
  simp [parameters, OrderedProductCoupling.sourceBlocks, OrderedProductCoupling.ofBlocks,
    OrderedProductCoupling.sourceKappa, ProductScaleData.kappa, Nat.cast_add, Nat.cast_one]

theorem source_measurePreserving_unflatten {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    MeasurePreserving (unflatten e)
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j))
      (sourceLaw p j) := by
  refine ⟨measurable_unflatten e, ?_⟩
  rw [← (source_measurePreserving_flatten hp e j).map_eq,
    Measure.map_map (measurable_unflatten e) (measurable_flatten e)]
  rw [show unflatten e ∘ flatten e = id from funext (unflatten_flatten e)]
  exact Measure.map_id

theorem measurable_flatSourceEvent (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r) (j : ℕ) :
    MeasurableSet (flatSourceEvent p e r j) :=
  (measurable_sourceEvent p e hr j).preimage (measurable_unflatten e)

theorem flatSourceEvent_mass_eq {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r) (j : ℕ) :
    (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)).real
      (flatSourceEvent p e r j) = (sourceLaw p j).real (sourceEvent p e r j) := by
  rw [← (source_measurePreserving_unflatten hp e j).map_eq,
    map_measureReal_apply (measurable_unflatten e) (measurable_sourceEvent p e hr j)]
  rfl

@[simp] theorem circleLeftEndpoint_unflatten {m : ℕ → ℕ}
    (e : ℕ ≃ Σ s, Fin (m s)) (ω : OrderedProductCoupling.Sample) :
    circleLeftEndpoint e (unflatten e ω) = OrderedProductCoupling.circleLeftEndpoint ω := by
  change toCircle (OrderedProductCoupling.leftEndpoint (flatten e (unflatten e ω))) = _
  rw [flatten_unflatten]
  rfl

@[simp] theorem circleRightEndpoint_unflatten {m : ℕ → ℕ}
    (e : ℕ ≃ Σ s, Fin (m s)) (ω : OrderedProductCoupling.Sample) :
    circleRightEndpoint e (unflatten e ω) = OrderedProductCoupling.circleRightEndpoint ω := by
  change toCircle (OrderedProductCoupling.rightEndpoint (flatten e (unflatten e ω))) = _
  rw [flatten_unflatten]
  rfl

theorem eventually_flatSourceEvent_mass {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)).real
        (flatSourceEvent p e r j) := by
  filter_upwards [eventually_sourceEvent_mass hp e hr hi] with j hj
  rwa [flatSourceEvent_mass_eq hp e hr j]

theorem ae_flatSourceEvent_coefficient_properties {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (P : ProjectionField) (hP : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (P x)) (j : ℕ) :
    ∀ᵐ ω ∂OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j),
      ω ∈ flatSourceEvent p e (projectionDiagonal P) j →
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientA p e θ P (unflatten e ω) v‖ ≤ p.coefficientBound j) ∧
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientB p e θ P (unflatten e ω) v‖ ≤ p.coefficientBound j) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientA p e θ P (unflatten e ω) 0‖ ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientB p e θ P (unflatten e ω) 0‖ :=
  (source_measurePreserving_unflatten hp e j).quasiMeasurePreserving.ae
    (ae_sourceEvent_coefficient_properties hp e θ hphase P hP j)

theorem ae_sourceEvent_tag_endpoints {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (r : ProductModel.Base → ℝ) (j : ℕ) :
    ∀ᵐ z ∂sourceLaw p j, z ∈ sourceEvent p e r j →
      ∃ k ∈ ProductPhases.consecutiveBlock p.m j,
        circleRepresentative (circleLeftEndpoint e z k) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint e z k) := by
  have ht : ∀ᵐ z ∂sourceLaw p j, ∀ i : Fin (p.m j),
      (z j i).1 = some (4 : Fin 5) →
        (z j i).2.1 < 1 / (p.m j : ℝ) ∧ 1 - 1 / (p.m j : ℝ) ≤ (z j i).2.2 := by
    apply ae_all_iff.mpr
    intro i
    have h := OneCoordinateCoupling.labelledLaw_ae_tag_interval
      (ProductScaleData.kappa j) (p.m j) (p.a j) (p.b j) (if j = j then 1 else 0)
    rw [← law_map_coordinate hp.m_ge_100 source_kappa_nonneg source_kappa_le
      (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
      (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) j j i] at h
    exact ae_of_ae_map (by fun_prop : Measurable (fun z : Sample p.m => z j i)).aemeasurable h
  have hrep := ae_circle_representatives hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) e j
  filter_upwards [ht, hrep] with z hz hr
  intro hE
  obtain ⟨i, hi⟩ := (mem_sourceRetainedEvent_iff.mp hE).1
  let k := e.symm ⟨j, i⟩
  have hk : k ∈ ProductPhases.consecutiveBlock p.m j := by
    dsimp [k]
    rw [he]
    simp only [ProductPhases.consecutiveBlock, Finset.mem_Ico]
    have := i.isLt
    omega
  have hcoord : flatten e z k = z j i := by
    change (fun q : Σ s, Fin (p.m s) => z q.1 q.2) (e (e.symm ⟨j, i⟩)) = _
    rw [e.apply_symm_apply]
  refine ⟨k, hk, ?_⟩
  rw [(hr k).1, (hr k).2]
  change (flatten e z k).2.1 < _ ∧ _ ≤ (flatten e z k).2.2
  rw [hcoord]
  exact hz i hi

theorem ae_flatSourceEvent_tag_endpoints {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (r : ProductModel.Base → ℝ) (j : ℕ) :
    ∀ᵐ ω ∂OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j),
      ω ∈ flatSourceEvent p e r j →
      ∃ k ∈ ProductPhases.consecutiveBlock p.m j,
        circleRepresentative (OrderedProductCoupling.circleLeftEndpoint ω k) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (OrderedProductCoupling.circleRightEndpoint ω k) := by
  have h := (source_measurePreserving_unflatten hp e j).quasiMeasurePreserving.ae
    (ae_sourceEvent_tag_endpoints hp e he r j)
  simpa only [circleLeftEndpoint_unflatten, circleRightEndpoint_unflatten,
    flatSourceEvent, mem_preimage] using h

end Invariant233.BlockedProductCoupling

end

end OAI
