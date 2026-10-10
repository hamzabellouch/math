import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSmallHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeIdeal
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceWeightedSectionError

namespace OAI

/-! # Absorbing the conjugated bridge into the second-sheet ideal box

The logarithm of the second Cartan factor can be subexponentially large.
Its small height, rather than a bound on its full logarithm, controls the
exponential size of the conjugated bridge. Strict ideal widths absorb it.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))

local notation "U" => M.coneWordIdeal C

include hunimod in
/-- A single subexponential ideal box contains the residual ideal
coordinates after every sufficiently small bridge and every allowed
second-sheet Cartan factor. The threshold is independent of the scale
and of the chosen endpoints. -/
theorem exists_conjugated_bridge_ideal_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {I J : Type*} [Fintype I] [Fintype J]
    (bI : Basis I ℝ U) (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : J → cartanRootIdeal H) (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    {N Q : Type*} [Group N] [Group Q]
    (ExpN : cartanRootIdeal H → N) (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (π : N →* Q) (hπ : ∀ v, π (ExpN v) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)
    (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r).repr
          ⁅exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
              (Sum.elim cost (fun _ => 0)) r i,
            exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
              (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
    (scale RN RH RE : ℕ → ℝ) (hs : StrictMono scale) (hscale : Tendsto scale atTop atTop)
    (hRN0 : ∀ n, 0 ≤ RN n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRN : HasSubexponentialUpperBoundSeq scale RN)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hRE : HasSubexponentialUpperBoundSeq scale RE) :
    ∃ S : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale S ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n in atTop, ∀ (u : N) (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        u ∈ exponentialCoordinateBox ExpN
          (exponentialRescaleBasis (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖eW (heightProjection T.character (h : L))‖ ≤ δ * scale n →
        ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ ≤
          RE n * Real.exp (δ * scale n) →
        ∃ (i : U) (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
          u * ExpN (cartanIdealAdjointAutomorphism T H h v) =
            ExpN (i : cartanRootIdeal H) * ExpN (quotientLinearSection U bQ lift q) ∧
          ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n := by
  let b := basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift
  obtain ⟨A, hA, haction⟩ := M.exists_small_height_adjoint_sequence_bound T hunimod eW
    b₀ b scale RH RE hscale hRH0 hRH hRE
  obtain ⟨S, hS, δ₀, hδ₀, habs⟩ := weighted_section_error_absorbed_sequence
    U bI bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul
    scale hs hscale cost hlo hcost hA K hK hbr RN hRN0 hRN
  refine ⟨S, hS, δ₀, hδ₀, ?_⟩
  intro δ hδ hδle
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  filter_upwards [haction δ hδ, habs δ hδ hδle (fun _ => 0) hzero] with n ha hb
  intro u γ h v hu hh hw hv
  apply hb u (cartanIdealAdjointAutomorphism T H h v) hu
  simpa only [zero_add, add_zero, mul_assoc] using ha γ h v hh hw hv

end PolycyclicRecognition.CartanWordModel

end

end OAI
