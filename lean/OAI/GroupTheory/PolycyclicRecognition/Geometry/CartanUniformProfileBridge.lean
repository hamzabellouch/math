import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileBridgeRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformIntrinsicBridge

namespace OAI

/-! # The profile bridge threshold precedes path length and error choices -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology

private theorem bridge_of_endpoint_factorization
    {N D G : Type*} [Mul G] (incN : N → G) (incD : D → G)
    (height : G → ℝ) (P P' : N → Prop) (Q : D → Prop) (R : N → D → Prop)
    (endpoint bridge : G) (δ : ℝ)
    (he : ∃ u d, incN u * incD d = endpoint ∧
      height (incD d) = height endpoint ∧ P u ∧ Q d)
    (hP : ∀ u, P u → P' u)
    (hb : ∀ u d, P' u → Q d → height (incD d) ≤ δ →
      ∃ v e, incN v * incD e = (incN u * incD d) * bridge ∧ R v e)
    (hh : height endpoint ≤ δ) :
    ∃ v e, incN v * incD e = endpoint * bridge ∧ R v e := by
  obtain ⟨u, d, he, hh', hu, hd⟩ := he
  obtain ⟨v, e, hprod, hr⟩ := hb u d (hP u hu) hd (hh' ▸ hh)
  exact ⟨v, e, hprod.trans (congrArg (fun x => x * bridge) he), hr⟩

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
theorem exists_uniform_profile_bridge_restrictions_of_basis
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
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
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
  obtain ⟨δ₀, hδ₀, hbridge⟩ :=
    M.exists_uniform_intrinsic_bridge_lifts T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
      b₀ γ₀ hcell hφ hpath hKπ hLip C
      (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
      bQ lift hlift ExpQ πQ hπQ hinjQ hzeroQ
      (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
      hlo hcost K hK hbr
  refine ⟨δ₀, hδ₀, ?_⟩
  intro scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨RN, RH, hRN0, hRH0, hRN, hRH, hliftPath⟩ :=
    M.exists_sequence_profile_endpoint_lifts T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ hφ hpath
      hKπ hLip hE hne γ hγ scale η hscale hscale1 hη0 hη A B hA hB
  obtain ⟨S, RD, hS0, hRD0, hS, hRD, hbridge⟩ := hbridge scale RN RH hmono hscale
    (fun n => zero_le_one.trans (hscale1 n)) hRN0 hRH0 hRN hRH
  refine ⟨S, RD, hS0, hRD0, hS, hRD, ?_⟩
  intro δ hδ hδle
  filter_upwards [hbridge δ hδ hδle] with n hn
  intro endpoint path bridge hmetric hheight hsmall hdist
  exact bridge_of_endpoint_factorization F.inclusionN F.inclusionD
    (fun g => ‖(π g).toAdd‖) _ _ _ _ endpoint bridge (δ * scale n)
    (by
      obtain ⟨u, d, he, hh, hu, hd⟩ := hliftPath n path hmetric hheight
      exact ⟨u, d, he, congrArg norm hh, hu, hd⟩)
    (fun u hu => Eq.mp (congrArg (fun s : Set F.N.carrier => u ∈ s)
      (hbox (scale n) (RN n))) hu)
    (fun u d hu hd hh => hn u d bridge hu hd hh hdist) hsmall



include hunimod hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_uniform_profile_bridge_restrictions
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
    :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      ∃ _hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j,
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop →
        (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
        ∃ S RD : ℕ → ℝ,
          (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
          HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
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
  exact M.exists_uniform_profile_bridge_restrictions_of_basis T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
    b₀ γ₀ hcell hφ hpath hKπ hLip C hE hne β bQ lift hlift γ hγ
    (hbox (F.ExpN ∘ F.N.equiv)) K hK hbr hlo (fun j => hcost (β.val j))
    ExpQ πQ hπQ hinjQ hzeroQ



end PolycyclicRecognition.CartanWordModel

end

end OAI
