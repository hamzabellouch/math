import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProducts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCompactWords

namespace OAI

/-! # Bounded terminal corrections preserve the Cartan lift controls -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
theorem exists_terminal_correction_bounds
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : Continuous (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = q (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x) (hbijD : Function.Bijective F.ExpD)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    {K : Set F.D.carrier} (hK : IsCompact K)
    (scale RH η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH) (hη : Tendsto η atTop (𝓝 0)) :
    ∃ R ε : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      Tendsto ε atTop (𝓝 0) ∧ ∀ n (d z : F.D.carrier), z ∈ K →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RH n →
        ‖q (heightProjection T.character
          (cartanLog H F.D.equiv F.ExpD hbijD d : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ η n * scale n →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d * z))‖ ≤ R n ∧
        ‖q (heightProjection T.character
          (cartanLog H F.D.equiv F.ExpD hbijD (d * z) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ε n * scale n := by
  obtain ⟨C, hC0, hC⟩ := exists_compact_exponential_coordinate_bound F.D.equiv F.ExpD
    chartD hchartD (finBasis ℝ H) hK
  have hClog (z : F.D.carrier) (hz : z ∈ K) :
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD z)‖ ≤ C := by
    obtain ⟨v, hv, hb⟩ := hC hz
    rw [← hv]
    change ‖(finBasis ℝ H).equivFun
      (cartanLog H F.D.equiv F.ExpD hbijD (F.ExpD (F.D.equiv v)))‖ ≤ C
    rw [cartanLog_exp]
    exact hb
  obtain ⟨R, hR0, hR, hprod⟩ := exists_sequence_cartan_product_bound H F.D.equiv F.ExpD hbijD
    F.isExpD dynkinD scale RH (fun _ => C) hs hRH0 (fun _ => hC0) hRH
      (sequence_subexponential_upper_const hs C)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hπ.comp F.closedD.continuous).continuousOn
  let ε := fun n => η n + max B 0 / scale n
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [add_zero] using hη.add
      (tendsto_const_nhds.div_atTop hs : Tendsto (fun n => max B 0 / scale n) atTop (𝓝 0))
  refine ⟨R, ε, hR0, hR, hε, ?_⟩
  intro n d z hz hd hh
  refine ⟨hprod n d z hd (hClog z hz), ?_⟩
  rw [← F.inclusionD_height T q π hπExp hbijD] at hh ⊢
  rw [map_mul, map_mul]
  change ‖(π (F.inclusionD d)).toAdd + (π (F.inclusionD z)).toAdd‖ ≤ ε n * scale n
  calc
    ‖(π (F.inclusionD d)).toAdd + (π (F.inclusionD z)).toAdd‖ ≤
        ‖(π (F.inclusionD d)).toAdd‖ + ‖(π (F.inclusionD z)).toAdd‖ := norm_add_le _ _
    _ ≤ η n * scale n + max B 0 := add_le_add hh ((hB z hz).trans (le_max_left _ _))
    _ = ε n * scale n := by dsimp only [ε]; rw [add_mul, div_mul_cancel₀ _ (hscale n).ne']

end PolycyclicRecognition.CartanFactorModel

end

end OAI
