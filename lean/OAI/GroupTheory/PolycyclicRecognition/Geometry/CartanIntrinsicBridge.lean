import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBridgeGeometry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBridgeAbsorption
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProducts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBridgeComposition

namespace OAI

/-! # Bridge absorption using the actual finite Dynkin expansion -/

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
/-- The published finite Dynkin identity supplies the bridge polynomial. -/
theorem exists_sequence_intrinsic_bridge_lifts
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD
        hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    {I J : Type*} [Fintype I] [Fintype J]
    (bI : Basis I ℝ (M.coneWordIdeal C))
    (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : J → cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    {Q : Type*} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r).repr
          ⁅exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r i,
           exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
    (scale RN RH : ℕ → ℝ) (hs : StrictMono scale) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hRN0 : ∀ n, 0 ≤ RN n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRN : HasSubexponentialUpperBoundSeq scale RN)
    (hRH : HasSubexponentialUpperBoundSeq scale RH) :
    ∃ S RD : ℕ → ℝ,
      (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
      HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n in atTop, ∀ (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G),
        u₂ ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
          (exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
          hbijD d₂)‖ ≤ RH n →
        ‖(π (F.inclusionD d₂)).toAdd‖ ≤ δ * scale n →
        dist 1 g ≤ δ * scale n →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
          ∀ z ∈ cell,
            (∃ (i : M.coneWordIdeal C)
              (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
              u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
              ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              hbijD
              (d * z.2))‖ ≤ RD n := by
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkinN F.N.equiv
    F.ExpN F.isExpN M.bound_zero 2
  have hmul (v w : cartanRootIdeal H) :
      F.ExpN (F.N.equiv (finiteDynkinPolynomial coeff ![v, w])) =
        F.ExpN (F.N.equiv v) * F.ExpN (F.N.equiv w) := by
    simpa using (hprod ![v, w]).symm
  exact M.exists_sequence_thickened_bridge_lifts T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD hbijN hbijD
    b₀ γ₀ hcell hφ hpath hKπ hLip C bI bQ lift hlift ExpQ πQ hπQ hinjQ hzeroQ
    coeff hcoeff hmul cost hlo hcost K hK hbr scale RN RH hs hscale hscale0
    hRN0 hRH0 hRN hRH

end PolycyclicRecognition.CartanWordModel

end

end OAI
