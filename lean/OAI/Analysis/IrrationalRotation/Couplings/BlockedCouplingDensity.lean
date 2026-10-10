import OAI.Analysis.IrrationalRotation.Couplings.BlockedProductCoupling
import OAI.Analysis.IrrationalRotation.Couplings.BlockedCouplingEnergy
import OAI.Analysis.IrrationalRotation.Analysis.EndpointLoss

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.BlockedProductCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem law_map_flatten (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    (law m κ a b j).map (flatten e) =
      OrderedProductCoupling.law (parameters hm hκ0 hκ ha ha' hb hb' e j) := by
  let P := parameters hm hκ0 hκ ha ha' hb hb' e j
  change (law m κ a b j).map
    ((fun z : (Σ s, Fin (m s)) → Coordinate => fun i => z (e i)) ∘
      (fun z p => z p.1 p.2)) = OrderedProductCoupling.law P
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    law_map_uncurry hm hκ0 hκ ha ha' hb hb']
  have h := Measure.infinitePi_map_piCongrLeft
    (OrderedProductCoupling.coordinateLaw P) e.symm
  simp only [OrderedProductCoupling.coordinateLaw, P, parameters,
    Equiv.apply_symm_apply] at h
  unfold OrderedProductCoupling.law
  convert h using 1 <;> congr 1
  · funext z i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · congr 1
    funext p
    rw [e.apply_symm_apply]

theorem exists_hybrid_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) (sel : ℕ → Bool) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      (∫ x, H x ∂OrderedProductCoupling.baseMeasure) = 1 ∧
      eLpNorm H 2 OrderedProductCoupling.baseMeasure ≤
        ENNReal.ofReal (Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1))) ∧
      (law m κ a b j).map (OrderedProductCoupling.hybridEndpoint sel ∘ flatten e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  let P := parameters hm hκ0 hκ ha ha' hb hb' e j
  obtain ⟨hs, he⟩ := enumerated_energy_sum m (fun s => by have := hm s; omega) κ hsq e j
  have hs' : Summable (OrderedProductCoupling.energyBound P) := hs
  have he' : (∑' i, OrderedProductCoupling.energyBound P i) ≤
      20 * (2 * (∑' s, κ s ^ 2) + 1) := he.le
  obtain ⟨H, hH, hn, hmean, hnorm, hmap⟩ :=
    OrderedProductCoupling.exists_hybrid_density P sel hs' he'
  refine ⟨H, hH, hn, hmean, ?_, ?_⟩
  · convert hnorm using 1
    congr 2
    ring
  · rw [← Measure.map_map (OrderedProductCoupling.hybridEndpoint_measurable sel)
      (by unfold flatten; fun_prop), law_map_flatten hm hκ0 hκ ha ha' hb hb']
    exact hmap

theorem exists_left_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      Real.sqrt (∫ x, H x ^ 2 ∂OrderedProductCoupling.baseMeasure) ≤
        Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1)) ∧
      (law m κ a b j).map (leftEndpoint e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hn, _, hnorm, hmap⟩ :=
    exists_hybrid_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e j (fun _ => false)
  refine ⟨H, hH, hn, ?_, ?_⟩
  · rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm hH]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  · have hf : OrderedProductCoupling.hybridEndpoint (fun _ => false) ∘ flatten e =
        leftEndpoint e := by
      funext z i
      rfl
    rw [hf] at hmap
    exact hmap

theorem exists_right_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      Real.sqrt (∫ x, H x ^ 2 ∂OrderedProductCoupling.baseMeasure) ≤
        Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1)) ∧
      (law m κ a b j).map (rightEndpoint e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hn, _, hnorm, hmap⟩ :=
    exists_hybrid_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e j (fun _ => true)
  refine ⟨H, hH, hn, ?_, ?_⟩
  · rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm hH]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  · have hf : OrderedProductCoupling.hybridEndpoint (fun _ => true) ∘ flatten e =
        rightEndpoint e := by
      funext z i
      rfl
    rw [hf] at hmap
    exact hmap

end Invariant233.BlockedProductCoupling

end OAI
