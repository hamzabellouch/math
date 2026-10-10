import OAI.GroupTheory.PolycyclicRecognition.Geometry.SectionWeightedBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveWidthAbsorption
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialOperations

namespace OAI

/-! # Small logarithmic errors in ideal-section coordinates -/

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
local notation "K" => sectionDynkinConstant (Fintype.card (I ⊕ J)) c

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The ideal error created by a pure section followed by a small ambient
error is absorbed by every strictly positive ideal width. -/
theorem section_error_absorbed (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(B).repr ⁅B i, B j⁆ k| ≤ C)
    (cost : I → ℝ) {lo α : ℝ} (hcost : ∀ i, lo ≤ cost i) (hα : 0 ≤ α)
    (hgap : ((c * c : ℕ) : ℝ) * α < lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, ∀ (q : V ⧸ U.toSubmodule) (e : V),
      ‖bQ.equivFun q‖ ≤ Real.exp ((α + ε r) * r) →
      ‖(B).equivFun e‖ ≤ Real.exp ((α + ε r) * r) →
      ∃ (u : U) (q' : V ⧸ U.toSubmodule),
        ExpN (quotientLinearSection U bQ lift q) * ExpN e =
          ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q') ∧
        ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ 1 := by
  have hK : 0 ≤ K C * (1 + K C) ^ c := by
    dsimp [sectionDynkinConstant]
    positivity
  have habs := eventually_positive_width_absorbs_polynomial bI cost (c * c)
    hcost hK hα hgap ε hε
  filter_upwards [habs] with r hr q e hq he
  obtain ⟨u, q', hfact, hu⟩ := section_error_factorization_bound U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hbr
    (Real.exp ((α + ε r) * r)) (Real.exp_pos _).le q e hq he
  exact ⟨u, q', hfact, hr u hu⟩

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- One positive threshold works for all error envelopes. It depends only
on the least ideal width, the BCH degree and the fixed error exponent. -/
theorem exists_section_error_absorption_threshold (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(B).repr ⁅B i, B j⁆ k| ≤ C)
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (hM : 0 < M) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      ∀ᶠ r in atTop, ∀ (q : V ⧸ U.toSubmodule) (e : V),
        ‖bQ.equivFun q‖ ≤ Real.exp ((M * δ + ε r) * r) →
        ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε r) * r) →
        ∃ (u : U) (q' : V ⧸ U.toSubmodule),
          ExpN (quotientLinearSection U bQ lift q) * ExpN e =
            ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q') ∧
          ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ 1 := by
  let D := (((c * c : ℕ) : ℝ) + 1) * M
  have hD : 0 < D := by dsimp [D]; positivity
  let δ₀ := lo / (2 * D)
  have hδ₀ : 0 < δ₀ := div_pos hlo (by positivity)
  have heq : (2 * D) * δ₀ = lo := mul_div_cancel₀ lo (ne_of_gt (by positivity))
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle ε hε
  apply section_error_absorbed U bI bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ hneg
    coeff hcoeff hmul C hC hbr cost hcost (mul_nonneg hM.le hδ.le) _ ε hε
  have hle := mul_le_mul_of_nonneg_left hδle hD.le
  have hp : (0 : ℝ) ≤ (c * c : ℕ) := Nat.cast_nonneg _
  have hsmall : ((c * c : ℕ) : ℝ) * (M * δ) ≤ D * δ := by
    dsimp [D]
    nlinarith [mul_pos hM hδ]
  nlinarith

/-- Polynomial losses in the adapted box comparison are subexponential. -/
theorem section_box_subexponential_envelope (C : ℝ) (hC : 0 ≤ C)
    (R : ℝ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRsub : HasSubexponentialUpperBound R) :
    HasSubexponentialUpperBound (fun r => K C * (1 + R r) ^ c) := by
  have hp := ((subexponential_upper_const 1).add hRsub).pow
    (Eventually.of_forall (fun r => by linarith [hR r])) c
  exact (subexponential_upper_const (K C)).mul hp
    (Eventually.of_forall (fun _ => by dsimp [sectionDynkinConstant]; positivity))

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The two inclusions in the ideal-section box comparison share a single
subexponential envelope. The quotient has exactly the zero-width coordinates. -/
theorem section_box_comparison (C : ℝ) (hC : 0 ≤ C) (cost : I → ℝ)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C)
    (R : ℝ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRsub : HasSubexponentialUpperBound R) :
    ∃ S : ℝ → ℝ, HasSubexponentialUpperBound S ∧ ∀ r : ℝ, 0 ≤ r →
      (∀ n : N, n ∈ exponentialCoordinateBox ExpN
          (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r) (R r) →
        ∃ (u : U) (q : V ⧸ U.toSubmodule),
          n = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
          ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ S r ∧
          ‖bQ.equivFun q‖ ≤ S r) ∧
      (∀ (u : U) (q : V ⧸ U.toSubmodule),
        ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ R r →
        ‖bQ.equivFun q‖ ≤ R r →
        ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∈
          exponentialCoordinateBox ExpN
            (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r) (S r)) := by
  let S := fun r => K C * (1 + R r) ^ c + R r
  have hK : 0 ≤ K C := by dsimp [sectionDynkinConstant]; positivity
  have hpoly : HasSubexponentialUpperBound (fun r => K C * (1 + R r) ^ c) :=
    section_box_subexponential_envelope (I := I) (J := J) (c := c) C hC R hR hRsub
  refine ⟨S, hpoly.add hRsub, ?_⟩
  intro r hr
  constructor
  · intro n hn
    obtain ⟨u, q, hn, hu, hq⟩ := weighted_section_box_factorization U bI bQ lift hlift
      ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul cost C hC hbr r (R r) hr (hR r) hn
    refine ⟨u, q, hn, hu.trans ?_, hq.trans ?_⟩
    · exact le_add_of_nonneg_right (hR r)
    · exact le_add_of_nonneg_left (mul_nonneg hK (pow_nonneg (by linarith [hR r]) _))
  · intro u q hu hq
    obtain ⟨v, hv, hb⟩ := weighted_section_box_product U bI bQ lift hlift ExpN
      coeff hcoeff hmul cost C hC hbr r (R r) hr (hR r) u q hu hq
    exact ⟨v, hv, hb.trans (le_add_of_nonneg_right (hR r))⟩

end PolycyclicRecognition

end

end OAI
