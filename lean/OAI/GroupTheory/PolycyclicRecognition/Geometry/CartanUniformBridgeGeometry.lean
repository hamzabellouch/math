import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformMetricFactorBounds
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformBridgeAbsorption
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBridgeGeometry

namespace OAI

/-! # Thickened bridge bounds with a preassigned smallness threshold -/

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

omit [IsIsometricSMul G G] [ProperSpace G] in
private theorem assemble_uniform_bridge_point
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    {J K QI : Type*} [Fintype J] [Fintype K] [Fintype QI]
    (b : Basis J ℝ (cartanRootIdeal H)) (C : Set (H →ₗ[ℝ] ℝ))
    (bI : Basis K ℝ (M.coneWordIdeal C))
    (bQ : Basis QI ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : QI → cartanRootIdeal H)
    (cost : K → ℝ) (cell : Set (F.N.carrier × F.D.carrier))
    (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G) (RE RB A δ r S RD : ℝ)
    (hRE : 0 ≤ RE) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (habs : ∀ v, ‖b.equivFun v‖ ≤ RE * Real.exp (((A + 1) * δ) * r) →
      ∃ (i : M.coneWordIdeal C) (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
        u₂ * F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H
          (cartanLog H F.D.equiv F.ExpD hbijD d₂) v)) =
          F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
        ‖(exponentialRescaleBasis bI cost r).equivFun i‖ ≤ S)
    (hprod : ∀ d, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RB →
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d₂ * d))‖ ≤ RD)
    (hbridge : ∃ ub db, F.inclusionN ub * F.inclusionD db = g ∧ ∀ z ∈ cell,
      (∃ v, F.ExpN (F.N.equiv v) = ub * F.action db z.1 ∧
        ‖b.equivFun v‖ ≤ RE * Real.exp (A * δ * r)) ∧
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (db * z.2))‖ ≤ RB) :
    ∃ u d, F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
      ∀ z ∈ cell,
        (∃ (i : M.coneWordIdeal C) (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
          u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
          ‖(exponentialRescaleBasis bI cost r).equivFun i‖ ≤ max S 0) ∧
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d * z.2))‖ ≤ RD := by
  apply exists_thickened_factor_bridge_of_bounds F.action F.inclusionN F.inclusionD F.conjugation
    (F.ExpN ∘ F.N.equiv) (fun i : M.coneWordIdeal C => F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (fun q => F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)))
    (fun v => ‖b.equivFun v‖)
    (fun d => ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖)
    (fun i => ‖(exponentialRescaleBasis bI cost r).equivFun i‖ ≤ max S 0)
    (fun d => ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD)
    (fun _ => True) cell u₂ d₂ g RE RB A δ r hRE hδ hr
  · intro v hv
    obtain ⟨i, q, he, hi⟩ := habs v hv
    refine ⟨i, q, ?_, hi.trans (le_max_left _ _)⟩
    have ha : F.action d₂ (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H
          (cartanLog H F.D.equiv F.ExpD hbijD d₂) v)) := by
      rw [hφ]
      exact integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN F.isExpN
        M.bound_zero _ v
    rw [Function.comp_apply, ha]
    exact he
  · exact hprod
  · obtain ⟨u, d, he, hb⟩ := hbridge
    exact ⟨u, d, he, trivial, hb⟩

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_uniform_thickened_bridge_lifts
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
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (hmul : ∀ v w, F.ExpN (F.N.equiv (finiteDynkinPolynomial coeff ![v, w])) =
      F.ExpN (F.N.equiv v) * F.ExpN (F.N.equiv w))
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
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale RN RH : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ RN n) → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RN → HasSubexponentialUpperBoundSeq scale RH →
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
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
  let b := WordBasisSelections.basis M.letter M.wordList γ₀
  obtain ⟨A, hA, hmetric⟩ := M.exists_uniform_sequence_metric_factor_bounds
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ b hcell hφ hpath hKπ hLip
  have hneg (v : cartanRootIdeal H) :
      F.ExpN (F.N.equiv (-v)) = (F.ExpN (F.N.equiv v))⁻¹ := by
    rw [map_neg, F.isExpN.map_neg]
  obtain ⟨δa, hδa, habs⟩ := M.exists_uniform_conjugated_bridge_ideal_bound
    T hunimod eW C b₀ bI bQ lift hlift (F.ExpN ∘ F.N.equiv) ExpQ πQ hπQ hinjQ
    hzeroQ hneg coeff hcoeff hmul cost hlo hcost K hK hbr
  let δ₀ := min 1 (δa / (A + 1))
  have hA1 : 0 < A + 1 := by linarith
  refine ⟨δ₀, lt_min zero_lt_one (div_pos hδa hA1), ?_⟩
  intro scale RN RH hs hscale hscale0 hRN0 hRH0 hRN hRH
  obtain ⟨RE, RB, hRE0, hRB0, hRE, hRB, hbridge⟩ := hmetric scale hscale hscale0
  obtain ⟨S, hS, habs⟩ := habs scale RN RH RE hs hscale hRN0 hRH0 hRN hRH hRE
  obtain ⟨RD, hRD0, hRD, hprod⟩ := exists_sequence_cartan_product_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD scale RH RB hscale hRH0 hRB0 hRH hRB
  let S' := fun n => max (S n) 0
  have hS' : HasSubexponentialUpperBoundSeq scale S' := by
    intro ε hε
    filter_upwards [hS ε hε] with n hn
    exact max_le hn (Real.exp_nonneg _)
  refine ⟨S', RD, fun _ => le_max_right _ _, hRD0, hS', hRD, ?_⟩
  intro δ hδ hδle
  have hδ1 : δ ≤ 1 := hδle.trans (min_le_left _ _)
  have hδa' : (A + 1) * δ ≤ δa := by
    have hh := (le_div_iff₀ hA1).mp (hδle.trans (min_le_right _ _))
    nlinarith
  filter_upwards [habs ((A + 1) * δ) (mul_pos hA1 hδ) hδa'] with n hn
  intro u₂ d₂ g hu₂ hd₂ hh₂ hg
  have hheight : ‖eW (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbijD d₂ : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
      ((A + 1) * δ) * scale n := by
    rw [← F.inclusionD_height T eW π hπExp hbijD]
    exact hh₂.trans (mul_le_mul_of_nonneg_right (by nlinarith) (hscale0 n))
  apply assemble_uniform_bridge_point T M F dynkinN hbijN hbijD hφ b C bI bQ lift cost
    cell u₂ d₂ g (RE n) (RB n) A δ (scale n) (S n) (RD n) (hRE0 n) hδ.le (hscale0 n)
  · exact fun v hv => hn u₂ γ₀ (cartanLog H F.D.equiv F.ExpD hbijD d₂) v
      hu₂ hd₂ hheight hv
  · exact fun d hd => hprod n d₂ d hd₂ hd
  · obtain ⟨u, d, he, _, hb⟩ := hbridge δ hδ hδ1 n g hg
    exact ⟨u, d, he, hb⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
