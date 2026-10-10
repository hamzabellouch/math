import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Sampling.PrefixCompactTransfer

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

theorem prefixEndpoint_circle_endpoints (D : ℕ) (ω : Sample) :
    ProductModel.prefixEndpoint D (circleLeftEndpoint ω) (circleRightEndpoint ω) =
      circleHybridEndpoint (fun i => decide (i < D)) ω := by
  funext i
  by_cases hi : i < D <;>
    simp [ProductModel.prefixEndpoint_apply, circleLeftEndpoint,
      circleRightEndpoint, circleHybridEndpoint, circleEndpoint, hybridEndpoint, Function.comp_apply, hi]

theorem prefixPairLaw_circlePairLaw (P : Parameters) (D : ℕ) :
    ProductModel.prefixPairLaw (circlePairLaw P) D =
      (law P).map (fun ω =>
        (circleLeftEndpoint ω, circleHybridEndpoint (fun i => decide (i < D)) ω)) := by
  rw [ProductModel.prefixPairLaw, circlePairLaw,
    Measure.map_map (ProductModel.measurable_prefixPair D)
      (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  congr 1
  funext ω
  exact congrArg (fun y => (circleLeftEndpoint ω, y))
    (prefixEndpoint_circle_endpoints D ω)

theorem prefixPairLaw_circlePairLaw_fst (P : Parameters) (D : ℕ) :
    (ProductModel.prefixPairLaw (circlePairLaw P) D).map Prod.fst =
      (law P).map (circleHybridEndpoint (fun _ => false)) := by
  rw [ProductModel.prefixPairLaw_first_marginal]
  exact circlePairLaw_fst P

theorem prefixPairLaw_circlePairLaw_snd (P : Parameters) (D : ℕ) :
    (ProductModel.prefixPairLaw (circlePairLaw P) D).map Prod.snd =
      (law P).map (circleHybridEndpoint (fun i => decide (i < D))) := by
  rw [prefixPairLaw_circlePairLaw,
    Measure.map_map measurable_snd (circleLeftEndpoint_measurable.prodMk
      (circleHybridEndpoint_measurable (fun i => decide (i < D))))]
  rfl

theorem circlePairLaw_marginals_ac_of_energy (P : Parameters)
    (hsum : Summable (energyBound P)) :
    (circlePairLaw P).map Prod.fst ≪ ProductModel.baseMeasure ∧
      (circlePairLaw P).map Prod.snd ≪ ProductModel.baseMeasure := by
  have hhybrid (ε : ℕ → Bool) :
      (law P).map (circleHybridEndpoint ε) ≪ ProductModel.baseMeasure := by
    obtain ⟨G, _, _, _, _, hG⟩ := exists_circle_hybrid_density P ε hsum
      (le_refl (∑' i, energyBound P i))
    rw [hG]
    exact withDensity_absolutelyContinuous _ _
  constructor
  · rw [circlePairLaw_fst]
    exact hhybrid (fun _ => false)
  · rw [circlePairLaw_snd]
    exact hhybrid (fun _ => true)

theorem circlePairLaw_prefix_hasUniformL2Marginals (P : Parameters)
    (hsum : Summable (energyBound P)) :
    ProductModel.HasUniformL2Marginals
      (ProductModel.prefixPairLaw (circlePairLaw P)) := by
  let H : ℝ := Real.exp ((∑' i, energyBound P i) / 2)
  have hH : 0 ≤ H := (Real.exp_pos _).le
  have hd (ε : ℕ → Bool) :
      ∃ f : Lp ℝ 2 ProductModel.baseMeasure,
        (∀ᵐ x ∂ProductModel.baseMeasure, 0 ≤ f x) ∧
        (law P).map (circleHybridEndpoint ε) =
          ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ‖f‖ ≤ H := by
    obtain ⟨G, hG, hpos, _, hnorm, hlaw⟩ := exists_circle_hybrid_density P ε hsum
      (le_refl (∑' i, energyBound P i))
    refine ⟨hG.toLp G, ?_, ?_, ?_⟩
    · filter_upwards [hG.coeFn_toLp, hpos] with x hx hpx
      simpa only [hx, Pi.zero_apply] using hpx
    · rw [hlaw]
      apply withDensity_congr_ae
      filter_upwards [hG.coeFn_toLp] with x hx
      exact congrArg ENNReal.ofReal hx.symm
    · rw [Lp.norm_toLp]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
        (ENNReal.toReal_ofReal hH)
  refine ⟨H, hH, fun D => ?_⟩
  obtain ⟨f, hf, hflaw, hfnorm⟩ := hd (fun _ => false)
  obtain ⟨g, hg, hglaw, hgnorm⟩ := hd (fun i => decide (i < D))
  refine ⟨f, g, hf, hg, ?_, ?_, hfnorm, hgnorm⟩
  · rw [prefixPairLaw_circlePairLaw_fst]
    exact hflaw
  · rw [prefixPairLaw_circlePairLaw_snd]
    exact hglaw

end Invariant233.OrderedProductCoupling

end

end OAI
