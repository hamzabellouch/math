import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedSectionError
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceRealExtension

namespace OAI

/-! # Small-error absorption along the actual profile scale sequence -/

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
/-- The absorption theorem requires only sequential subexponential data,
with no regularity between the scale values. -/
theorem weighted_section_error_absorbed_sequence
    (scale : ℕ → ℝ) (hs : StrictMono scale) (hscale : Tendsto scale atTop atTop)
    (cost : I → ℝ) {lo M : ℝ} (hlo : 0 < lo)
    (hcost : ∀ i, lo ≤ cost i) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r).repr
        ⁅exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r i,
          exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ C)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hRsub : HasSubexponentialUpperBoundSeq scale R) :
    ∃ S : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale S ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      ∀ᶠ j in atTop, ∀ (n : N) (e : V),
        n ∈ exponentialCoordinateBox ExpN
          (exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) (scale j)) (R j) →
        ‖(B).equivFun e‖ ≤ Real.exp ((M * δ + ε j) * scale j) →
        ∃ (u : U) (q : V ⧸ U.toSubmodule),
          n * ExpN e = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
          ‖(exponentialRescaleBasis bI cost (scale j)).equivFun u‖ ≤ S j := by
  obtain ⟨S, hS, δ₀, hδ₀, habs⟩ := weighted_section_error_absorbed U bI bQ lift hlift
    ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul cost hlo hcost hM C hC hbr
    (sequenceRealExtension scale R) (sequenceRealExtension_nonneg scale R hR)
    (hRsub.realExtension hs)
  refine ⟨S ∘ scale, hS.along_sequence hscale, δ₀, hδ₀, ?_⟩
  intro δ hδ hδle ε hε
  have hh := hscale.eventually (habs δ hδ hδle (sequenceRealExtension scale ε)
    (tendsto_sequenceRealExtension_zero scale hs ε hε))
  simpa only [sequenceRealExtension_apply scale hs, Function.comp_apply] using hh

end PolycyclicRecognition

end

end OAI
