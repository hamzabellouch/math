import OAI.GroupTheory.PolycyclicRecognition.Algebra.SectionErrorAbsorption
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IdealProductCoordinates

namespace OAI

/-! # The ideal coordinate after a small ambient logarithmic error

This is the last assertion of the manuscript's strict-width absorption
lemma. The error factor is computed by BCH; its ideal part is absorbed by
positive widths before multiplying the two ideal factors.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

theorem HasSubexponentialUpperBound.eventually_le_perturbed_exp
    {R : ℝ → ℝ} (hR : HasSubexponentialUpperBound R)
    {α : ℝ} (hα : 0 < α) {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ r in atTop, R r ≤ Real.exp ((α + ε r) * r) := by
  filter_upwards [hR (α / 2) (by positivity),
    hε.eventually (eventually_gt_nhds (show -(α / 2) < 0 by linarith)),
    eventually_ge_atTop (0 : ℝ)] with r hr he hr0
  exact hr.trans (Real.exp_le_exp.mpr (by nlinarith))

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
/-- A subexponential full box followed by a small exponential error still
has a subexponential ideal coordinate at the same positive widths. -/
theorem weighted_section_error_absorbed
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo)
    (hcost : ∀ i, lo ≤ cost i) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C)
    (R : ℝ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRsub : HasSubexponentialUpperBound R) :
    ∃ S : ℝ → ℝ, HasSubexponentialUpperBound S ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      ∀ᶠ r in atTop, ∀ (n : N) (e : V),
        n ∈ exponentialCoordinateBox ExpN
          (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r) (R r) →
        ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε r) * r) →
        ∃ (u : U) (q : V ⧸ U.toSubmodule),
          n * ExpN e = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
          ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ S r := by
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
  have hraw : ∀ i j k, |(B).repr ⁅(B) i, (B) j⁆ k| ≤ C := by
    simpa only [exponentialRescaleBasis_zero] using hbr 0 le_rfl
  obtain ⟨δ₀, hδ₀, habs⟩ := exists_section_error_absorption_threshold U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hraw cost hlo hcost hM
  refine ⟨S, hS, δ₀, hδ₀, ?_⟩
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

end PolycyclicRecognition

end

end OAI
