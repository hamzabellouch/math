import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTwoPathProbeRestrictions
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformProfileBridge

namespace OAI

/-! # Uniform smallness threshold for the two probe paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology
open MeasureTheory

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
theorem exists_uniform_two_path_probe_restrictions
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbijQ : Function.Bijective ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ (Q.equiv (M.coneProjection C v)))
    (μQ : Measure Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πQ u * α d q)
    (E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β₁ : M.Bases)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hz₁ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₁ i = 0)
    (bI₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (β₂ : M.ConeIdealBases C)
    (hβ₂ : M.IsMaximizingConeIdealBasis C bI₀
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂)
    (hs₂ : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E₂ i)
    (hz₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₂ i = 0)
    (hp₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
      0 < (M.supportIn T hunimod eW).weightSupport E₂ i)
    :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop →
        (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ (RQ : ℕ → Set Q.carrier) (S RD : ℕ → ℝ),
        (∀ n, μQ (RQ n) ≠ ⊤) ∧
        HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal) ∧
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ (base anchor first second : G)
          (path₁ : Path (1 : G) (base⁻¹ * first))
          (path₂ : Path (1 : G) (anchor⁻¹ * second)),
          PathMetricBound path₁ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          PathMetricBound path₂ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₁, ‖(π (path₁ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₂, ‖(π (path₂ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π (anchor⁻¹ * second)).toAdd‖ ≤ δ * scale n →
          dist second first ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = anchor⁻¹ * first ∧
            ∀ z ∈ cell,
              act (base⁻¹ * (first * (F.inclusionN z.1 * F.inclusionD z.2))) 1 ∈ RQ n ∧
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  ((M.supportIn T hunimod eW).weightSupport E₂) β₂ (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n := by
  obtain ⟨bQ, lift, hlift, δ₀, hδ₀, hsecond⟩ :=
    M.exists_uniform_profile_bridge_restrictions T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
      b₀ γ₀ hcell hφ hpath hKπ hLip C bI₀ hE₂ hne₂ hs₂ hz₂ hp₂ β₂ hβ₂
      (ExpQ ∘ Q.equiv) πQ hπQ (hbijQ.injective.comp Q.equiv.injective)
      (by simp only [Function.comp_apply, map_zero, hExpQ.map_zero])
  refine ⟨bQ, lift, hlift, δ₀, hδ₀, ?_⟩
  intro scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨RQ, _RD₁, hRQ, hRQvol, _hRD₁0, _hRD₁, hfirst⟩ :=
    M.exists_controlled_profile_quotient_restriction T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ hcell hφ hpath hKπ hLip
      hE₁ hne₁ β₁ hβ₁ scale η hscale hscale1 hη0 hη A B hA hB C hz₁
      Q ExpQ hExpQ haarQ πQ hπQ (finBasis ℝ _) μQ α act hact
  obtain ⟨S, RD, hS0, hRD0, hS, hRD, hsecond⟩ :=
    hsecond scale η hmono hscale hscale1 hη0 hη A B hA hB
  refine ⟨RQ, S, RD, hRQ, hRQvol, hS0, hRD0, hS, hRD, ?_⟩
  intro δ hδ hδle
  filter_upwards [hsecond δ hδ hδle] with n hn
  intro base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist
  exact exists_two_frame_probe_lift
    (fun u d => F.inclusionN u * F.inclusionD d) (fun g q => act g q) 1
    cell (RQ n) base anchor first second (δ * scale n) _ _ _
    (hfirst n path₁ hm₁ hh₁)
    (fun bridge hbridge => hn path₂ bridge hm₂ hh₂ hsmall hbridge) hdist


end PolycyclicRecognition.CartanWordModel

end

end OAI
