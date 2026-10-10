import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOverlapBound
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanOverlap
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceQuotientVolume

namespace OAI

/-! # Volume hidden by variable Cartan lifts

For Cartan logarithms with a subexponential bound and heights `o(scale)`,
all nilpotent coordinates projecting into one fixed-radius ambient ball
have subexponential Haar outer measure. The center of the ball is arbitrary.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include hunimod in
theorem exists_subexponential_lift_multiplicity
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure]
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (scale RH η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH) (hη : Tendsto η atTop (𝓝 0))
    (ρ : ℝ) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (y : G),
        μ {u | ∃ d : F.D.carrier,
          ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RH n ∧
          ‖eW (heightProjection T.character
            (cartanLog H F.D.equiv F.ExpD hbijD d : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
              η n * scale n ∧
          dist (F.inclusionN u * F.inclusionD d) y ≤ ρ} ≤ ENNReal.ofReal (V n) := by
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨C, hC, hcover⟩ := F.compactLifts (closedBall (1 : G) (2 * ρ)) (isCompact_closedBall _ _)
  obtain ⟨RN, hRN, hN⟩ := exists_compact_exponential_coordinate_bound F.N.equiv F.ExpN
    chartN hchartN (WordBasisSelections.basis M.letter M.wordList γ) (hC.image continuous_fst)
  obtain ⟨RD, hRD, hD⟩ := exists_compact_exponential_coordinate_bound F.D.equiv F.ExpD
    chartD hchartD (finBasis ℝ H) (hC.image continuous_snd)
  obtain ⟨RZ, hRZ0, hRZ, hZ⟩ := exists_sequence_cartan_overlap_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD scale RH (fun _ => RD) hs hRH0 (fun _ => hRD) hRH
    (sequence_subexponential_upper_const hs RD)
  obtain ⟨S, hS0, hS, hdiff⟩ := M.exists_subexponential_overlap_difference_bound T F hunimod eW
    hExpG hinjG realize hbijN hbijD dynkinN b γ scale RH (fun _ => RN) RZ η hs
    hscale hRH0 (fun _ => hRN) hRZ0 hRH (sequence_subexponential_upper_const hs RN) hRZ hη
  have hnil := cartanRootIdeal_nilpotent H T
  obtain ⟨hfinite, hvolume⟩ := haar_model_sequence_boxes haarN F.ExpN F.isExpN F.N.equiv
    hnil b μ scale S hs hS0 hS
  let B := fun n => exponentialCoordinateBox (F.ExpN ∘ F.N.equiv) b (S n)
  refine ⟨fun n => (μ (B n)).toReal, fun _ => ENNReal.toReal_nonneg, hvolume, ?_⟩
  intro n y
  let A := {u | ∃ d : F.D.carrier,
    ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RH n ∧
    ‖eW (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbijD d : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
        η n * scale n ∧ dist (F.inclusionN u * F.inclusionD d) y ≤ ρ}
  change μ A ≤ _
  by_cases hA : A.Nonempty
  · obtain ⟨u₀, d₀, hd₀, hh₀, hy₀⟩ := hA
    have hsub : A ⊆ (fun u => u₀⁻¹ * u) ⁻¹' B n := by
      intro u hu
      obtain ⟨d, hd, hh, hy⟩ := hu
      let q₀ := F.inclusionN u₀ * F.inclusionD d₀
      let q := F.inclusionN u * F.inclusionD d
      have hdist : dist (q₀⁻¹ * q) 1 ≤ 2 * ρ := by
        have he : dist (q₀⁻¹ * q) 1 = dist q q₀ := by
          simpa only [mul_inv_cancel_left, mul_one] using
            (dist_mul_left q₀ (q₀⁻¹ * q) 1).symm
        rw [he]
        calc
          dist q q₀ ≤ dist q y + dist y q₀ := dist_triangle _ _ _
          _ ≤ 2 * ρ := by rw [dist_comm y q₀]; linarith
      obtain ⟨z, hz, hproj⟩ := hcover hdist
      change F.inclusionN z.1 * F.inclusionD z.2 = q₀⁻¹ * q at hproj
      have he : F.inclusionN u * F.inclusionD d =
          (F.inclusionN u₀ * F.inclusionD d₀) * (F.inclusionN z.1 * F.inclusionD z.2) := by
        change q = q₀ * _
        rw [hproj]
        simp
      have hdz : ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD z.2)‖ ≤ RD := by
        obtain ⟨v, hv, hb⟩ := hD ⟨z, hz, rfl⟩
        rw [← hv]
        change ‖(finBasis ℝ H).equivFun
          (cartanLog H F.D.equiv F.ExpD hbijD (F.ExpD (F.D.equiv v)))‖ ≤ RD
        rw [cartanLog_exp]
        exact hb
      exact hdiff n u₀ u z.1 d₀ d z.2 he hd₀ hh₀ (hN ⟨z, hz, rfl⟩)
        (hZ n d₀ z.2 d hd₀ hdz hd)
    calc
      μ A ≤ μ ((fun u => u₀⁻¹ * u) ⁻¹' B n) := measure_mono hsub
      _ = μ (B n) := measure_preimage_mul μ _ _
      _ = ENNReal.ofReal ((μ (B n)).toReal) := (ENNReal.ofReal_toReal (hfinite n)).symm
  · rw [Set.not_nonempty_iff_eq_empty.mp hA, measure_empty]
    exact bot_le

end PolycyclicRecognition.CartanWordModel

end

end OAI
