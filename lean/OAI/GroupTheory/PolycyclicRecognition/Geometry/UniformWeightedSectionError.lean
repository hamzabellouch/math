import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedSectionError
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceWeightedSectionError

namespace OAI

/-! # An absorption threshold independent of the path envelopes -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

variable {V I J N Q : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

local notation "B" => basisWithQuotientLifts U.toSubmodule bI bQ lift hlift

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- Choose the small bridge threshold before the subexponential path envelope.
This order is needed when the path constants are only fixed after choosing the
contact pivot. -/
theorem weighted_section_error_absorbed_uniform
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo)
    (hcost : ∀ i, lo ≤ cost i) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (R : ℝ → ℝ),
      (∀ r, 0 ≤ R r) → HasSubexponentialUpperBound R →
      ∃ S : ℝ → ℝ, HasSubexponentialUpperBound S ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ᶠ r in atTop, ∀ (n : N) (e : V),
          n ∈ exponentialCoordinateBox ExpN
            (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r) (R r) →
          ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε r) * r) →
          ∃ (u : U) (q : V ⧸ U.toSubmodule),
            n * ExpN e = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
            ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ S r := by
  have hraw : ∀ i j k, |(B).repr ⁅(B) i, (B) j⁆ k| ≤ C := by
    simpa only [exponentialRescaleBasis_zero] using hbr 0 le_rfl
  obtain ⟨δ₀, hδ₀, habs⟩ := exists_section_error_absorption_threshold U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hraw cost hlo hcost hM
  refine ⟨δ₀, hδ₀, ?_⟩
  intro R hR hRsub
  let K₀ := sectionDynkinConstant (Fintype.card (I ⊕ J)) c C
  let K₁ := sectionDynkinConstant (Fintype.card I) c C
  let R₀ := fun r => K₀ * (1 + R r) ^ c
  let S := fun r => K₁ * (1 + (R₀ r + 1)) ^ c
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, sectionDynkinConstant]; positivity
  have hR₀ (r) : 0 ≤ R₀ r := mul_nonneg hK₀ (pow_nonneg (by linarith [hR r]) _)
  have hR₀sub : HasSubexponentialUpperBound R₀ :=
    section_box_subexponential_envelope (I := I) (J := J) (c := c) C hC R hR hRsub
  have hS : HasSubexponentialUpperBound S := by
    have hp := ((subexponential_upper_const 1).add
      (hR₀sub.add (subexponential_upper_const 1))).pow
      (Eventually.of_forall (fun r => by linarith [hR₀ r])) c
    exact (subexponential_upper_const K₁).mul hp
      (Eventually.of_forall (fun _ => by dsimp [K₁, sectionDynkinConstant]; positivity))
  refine ⟨S, hS, ?_⟩
  intro δ hδ hδle ε hε
  filter_upwards [habs δ hδ hδle ε hε,
    hRsub.eventually_le_perturbed_exp (mul_pos hM hδ) hε,
    eventually_ge_atTop (0 : ℝ)] with r hr hlarge hr0 n e hn he
  obtain ⟨u₀, q₀, hn, hu₀, hq₀⟩ := weighted_section_box_factorization U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul cost C hC hbr r (R r) hr0 (hR r) hn
  obtain ⟨u₁, q₁, heq, hu₁⟩ := hr q₀ e (hq₀.trans hlarge) he
  have hbrI : ∀ i j k, |(exponentialRescaleBasis bI cost r).repr
      ⁅exponentialRescaleBasis bI cost r i, exponentialRescaleBasis bI cost r j⁆ k| ≤ C := by
    apply ideal_basis_bracket_bound U (exponentialRescaleBasis bI cost r) bQ lift hlift
    simpa only [basisWithQuotientLifts_rescale] using hbr r hr0
  obtain ⟨u, hu, hub⟩ := ideal_product_coordinate_bound U
    (exponentialRescaleBasis bI cost r) ExpN coeff hcoeff hmul C hC hbrI
    (show 0 ≤ R₀ r + 1 by linarith [hR₀ r]) u₀ u₁
    (hu₀.trans (le_add_of_nonneg_right zero_le_one))
    (hu₁.trans (le_add_of_nonneg_left (hR₀ r)))
  refine ⟨u, q₁, ?_, hub⟩
  rw [hn, mul_assoc, heq, ← mul_assoc, ← hu]


include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The same threshold is uniform over the scale sequence and every
subexponential input envelope. -/
theorem weighted_section_error_absorbed_sequence_uniform
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo)
    (hcost : ∀ i, lo ≤ cost i) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale : ℕ → ℝ), StrictMono scale →
      Tendsto scale atTop atTop → ∀ (R : ℕ → ℝ), (∀ n, 0 ≤ R n) →
      HasSubexponentialUpperBoundSeq scale R →
      ∃ S : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale S ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
        ∀ᶠ n in atTop, ∀ (u : N) (e : V),
          u ∈ exponentialCoordinateBox ExpN
            (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) (scale n)) (R n) →
          ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε n) * scale n) →
          ∃ (i : U) (q : V ⧸ U.toSubmodule),
            u * ExpN e = ExpN (i : V) * ExpN (quotientLinearSection U bQ lift q) ∧
            ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n := by
  obtain ⟨δ₀, hδ₀, habs⟩ := weighted_section_error_absorbed_uniform U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul cost hlo hcost hM C hC hbr
  refine ⟨δ₀, hδ₀, ?_⟩
  intro scale hs hscale R hR hRsub
  obtain ⟨S, hS, he⟩ := habs (sequenceRealExtension scale R)
    (sequenceRealExtension_nonneg scale R hR) (hRsub.realExtension hs)
  refine ⟨S ∘ scale, hS.along_sequence hscale, ?_⟩
  intro δ hδ hδle ε hε
  have hh := hscale.eventually (he δ hδ hδle (sequenceRealExtension scale ε)
    (tendsto_sequenceRealExtension_zero scale hs ε hε))
  simpa only [sequenceRealExtension_apply scale hs, Function.comp_apply] using hh

end PolycyclicRecognition

end

end OAI
