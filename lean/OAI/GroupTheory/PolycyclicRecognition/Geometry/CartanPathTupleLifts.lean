import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanTupleLifts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileEndpointLifts

namespace OAI

/-! # Actual controlled paths supply the target tuple lifts -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

/-- Finite tuples whose successive transitions have controlled template paths
admit compatible lifts with subexponential Cartan size and template increments. -/
theorem exists_sequence_path_tuple_lifts
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (h : ℕ) (E : Fin h → Set W) (β : Fin h → M.Bases)
    (hEc : ∀ i, IsCompact (E i)) (hEn : ∀ i, (E i).Nonempty)
    (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (E i)) (β i).val)
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s : ℕ → Set (Fin h → G))
    (path : ∀ (_n : ℕ) (x : Fin h → G) (i : Fin h), Path (1 : G)
      ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)))
    (hmetric : ∀ n x, x ∈ s n → ∀ i,
      PathMetricBound (path n x i) (A * scale n) (B * (1 + Real.log (2 + scale n))))
    (htemplate : ∀ n x, x ∈ s n → ∀ i t, ∃ z ∈ E i,
      ‖(π (path n x i t)).toAdd - scale n • z‖ ≤
        2 * scale n * η n + A * (1 + Real.log (2 + scale n)))
    (hend : ∀ n x, x ∈ s n → ∀ i : Fin h,
      ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
        η n * scale n) :
    ∃ (RH R : ℕ → ℝ)
      (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier)),
      (∀ n, 0 ≤ RH n) ∧ (∀ n, 0 ≤ R n) ∧
      HasSubexponentialUpperBoundSeq scale RH ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n x, x ∈ s n →
        (∀ i, F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i) ∧
        (∀ i, ‖(finBasis ℝ H).equivFun
          (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n) ∧
        (∀ i, ‖eW (heightProjection T.character
          (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) :
            GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ((h : ℝ) * η n) * scale n) ∧
        (∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n)) := by
  classical
  have hφ := fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG
    realize hbijN hbijD dynkinN d
  have hlifts := fun i => M.exists_sequence_profile_endpoint_lifts T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ hφ hpath hK hLip
    (hEc i) (hEn i) (β i) (hβ i) scale η hs hscale hη0 hη A B hA hB
  choose RN RD hRN0 hRD0 hRN hRD hlifts using hlifts
  obtain ⟨RN', hRN'0, hRN', hRNle⟩ := finite_subexponential_envelope hs RN hRN0 hRN
  obtain ⟨RD', hRD'0, hRD', hRDle⟩ := finite_subexponential_envelope hs RD hRD0 hRD
  have hchoice : ∀ n x (i : Fin h), ∃ (u : F.N.carrier) (d : F.D.carrier),
      x ∈ s n → F.inclusionN u * F.inclusionD d =
        (basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1) ∧
      u ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (RN' n) ∧
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD' n ∧
      ‖(π (F.inclusionD d)).toAdd‖ ≤ η n * scale n := by
    intro n x i
    by_cases hx : x ∈ s n
    · obtain ⟨u, d, hp, hdh, hu, hd⟩ := hlifts i n (path n x i)
        (hmetric n x hx i) (htemplate n x hx i)
      refine ⟨u, d, fun _ => ⟨hp, ?_, hd.trans (hRDle i n), ?_⟩⟩
      · obtain ⟨v, hv, hb⟩ := hu
        exact ⟨v, hv, hb.trans (hRNle i n)⟩
      · rw [hdh]
        exact hend n x hx i
    · exact ⟨1, 1, fun h => (hx h).elim⟩
  choose u d hud using hchoice
  let u' := fun n x j => if hj : j < h then u n x ⟨j, hj⟩ else 1
  let d' := fun n x j => if hj : j < h then d n x ⟨j, hj⟩ else 1
  apply M.exists_sequence_accumulated_tuple_lifts T F hunimod eW hExpG realize π hπExp
    hbijN hbijD dynkinN dynkinD b₀ h E β hEc hEn hβ scale RN' RD' η hs
    (fun n => lt_of_lt_of_le zero_lt_one (hscale n)) hRN'0 hRD'0 hη0 hRN' hRD' hη s u' d'
  · intro n x hx j hj
    simpa only [u', d', dite_eq_left hj] using (hud n x ⟨j, hj⟩ hx).1
  · intro n x hx i
    simpa only [u', dite_eq_left i.isLt] using (hud n x i hx).2.1
  · intro n x hx j hj
    simpa only [d', dite_eq_left hj] using (hud n x ⟨j, hj⟩ hx).2.2.1
  · intro n x hx j hj
    simpa only [d', dite_eq_left hj] using (hud n x ⟨j, hj⟩ hx).2.2.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
