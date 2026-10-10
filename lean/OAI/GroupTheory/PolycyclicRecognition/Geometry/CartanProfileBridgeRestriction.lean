import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeAdaptedPathBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntrinsicBridge
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileEndpointLifts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealStrictWidth

namespace OAI

/-! # The second profile path and bridge control the actual ideal coordinate -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- The second selected path and its short bridge give one actual factor
lift whose entire right cell has controlled ideal and Cartan coordinates.
The exact adapted-basis identity is supplied by
`exists_cone_adapted_path_basis`; no endpoint restriction is assumed. -/
theorem exists_profile_bridge_restrictions_of_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.ConeIdealBases C)
    (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
      ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
      cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) γ.val)
    (hbox : ∀ r R : ℝ, M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E γ r R =
      exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis
          (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
            (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
            bQ lift hlift)
          (Sum.elim
            (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
            (fun _ => 0)) r) R)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r →
      let B := exponentialRescaleBasis
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
          (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
          bQ lift hlift)
        (Sum.elim
          (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
          (fun _ => 0)) r
      ∀ i j k, |B.repr ⁅B i, B j⁆ k| ≤ K)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ j, lo ≤ M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
    {Q : Type*} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) =
      ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (scale η : ℕ → ℝ) (hmono : StrictMono scale) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ {endpoint : G} (path : Path (1 : G) endpoint) (bridge : G),
          PathMetricBound path (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E, ‖(π (path t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π endpoint).toAdd‖ ≤ δ * scale n →
          dist 1 bridge ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = endpoint * bridge ∧
            ∀ z ∈ cell,
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  ((M.supportIn T hunimod eW).weightSupport E) β (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n := by
  obtain ⟨RN, RH, hRN0, hRH0, hRN, hRH, hliftPath⟩ :=
    M.exists_sequence_profile_endpoint_lifts T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ hφ hpath
      hKπ hLip hE hne γ hγ scale η hscale hscale1 hη0 hη A B hA hB
  obtain ⟨S, RD, hS0, hRD0, hS, hRD, δ₀, hδ₀, hbridge⟩ :=
    M.exists_sequence_intrinsic_bridge_lifts T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
      b₀ γ₀ hcell hφ hpath hKπ hLip C
      (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
      bQ lift hlift ExpQ πQ hπQ hinjQ hzeroQ
      (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
      hlo hcost K hK hbr scale RN RH hmono hscale
      (fun n => zero_le_one.trans (hscale1 n)) hRN0 hRH0 hRN hRH
  refine ⟨S, RD, hS0, hRD0, hS, hRD, δ₀, hδ₀, ?_⟩
  intro δ hδ hδle
  filter_upwards [hbridge δ hδ hδle] with n hn
  intro endpoint path bridge hmetric hheight hsmall hdist
  obtain ⟨u₂, d₂, hend, hdheight, hu₂, hd₂⟩ := hliftPath n path hmetric hheight
  have hu₂' := Eq.mp (congrArg (fun s : Set F.N.carrier => u₂ ∈ s)
    (hbox (scale n) (RN n))) hu₂
  have hh₂ : ‖(π (F.inclusionD d₂)).toAdd‖ ≤ δ * scale n := by
    rw [hdheight]
    exact hsmall
  obtain ⟨u, d, hprod, hbounds⟩ := hn u₂ d₂ bridge hu₂' hd₂ hh₂ hdist
  refine ⟨u, d, hprod.trans (congrArg (fun g => g * bridge) hend), ?_⟩
  exact hbounds


include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- Positive ideal widths and zero quotient widths construct all of the
adapted bridge data. Only the actual controlled path, its small endpoint
height and the short geometric bridge remain to be supplied. -/
theorem exists_profile_bridge_restrictions
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    (bI₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
      0 < (M.supportIn T hunimod eW).weightSupport E i)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI₀
      ((M.supportIn T hunimod eW).weightSupport E) β)
    {Q : Type*} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) =
      ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (scale η : ℕ → ℝ) (hmono : StrictMono scale) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      ∃ _hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j,
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ {endpoint : G} (path : Path (1 : G) endpoint) (bridge : G),
          PathMetricBound path (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E, ‖(π (path t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π endpoint).toAdd‖ ≤ δ * scale n →
          dist 1 bridge ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = endpoint * bridge ∧
            ∀ z ∈ cell,
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  ((M.supportIn T hunimod eW).weightSupport E) β (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n := by
  obtain ⟨bQ, lift, hlift, γ, hγ, hbox, K, hK, hbr⟩ :=
    M.exists_cone_adapted_path_basis C T hunimod eW b₀ bI₀ E hs hzero β hβ
  obtain ⟨lo, hlo, hcost⟩ := M.exists_positive_coneIdeal_width C
    ((M.supportIn T hunimod eW).weightSupport E) hs hpos
  refine ⟨bQ, lift, hlift, ?_⟩
  exact M.exists_profile_bridge_restrictions_of_basis T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
    b₀ γ₀ hcell hφ hpath hKπ hLip C hE hne β bQ lift hlift γ hγ
    (hbox (F.ExpN ∘ F.N.equiv)) K hK hbr hlo (fun j => hcost (β.val j))
    ExpQ πQ hπQ hinjQ hzeroQ scale η hmono hscale hscale1 hη0 hη A B hA hB


end PolycyclicRecognition.CartanWordModel

end

end OAI
