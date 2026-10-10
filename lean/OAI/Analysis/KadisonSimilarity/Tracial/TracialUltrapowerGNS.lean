import OAI.Analysis.KadisonSimilarity.Tracial.UltrapowerConstants
import OAI.Analysis.BoundedHochschild.Ultrapowers

namespace OAI

/-! The GNS space of the tracial quotient embeds isometrically in the
Hilbert ultrapower. This is the bounded-algebra-sequence subspace used
in the finite-factor transfer. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower HochschildUltrapower TracialUltrapower
open scoped ENNReal Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- A bounded algebra sequence, viewed as a bounded family of GNS vectors. -/
def algebraSequenceVector (x : ℕ →ᵇ A) :
    UltraPreHilbert (fun _ : ℕ => τ.GNS) ω :=
  (⟨fun i => (τ.toPreGNS (x i) : τ.GNS), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    simpa only [UniformSpace.Completion.norm_coe] using
      (HochschildRigidity.preGNS_norm_le τ h1 (x i)).trans (x.norm_coe_le_norm i)⟩⟩ :
    lp (fun _ : ℕ => τ.GNS) ∞)

/-- Algebra sequences act linearly on the bounded-vector subspace. -/
def algebraSequenceVectorLinear : (ℕ →ᵇ A) →ₗ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω where
  toFun x := (algebraSequenceVector τ h1 ω x :
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω)
  map_add' x y := by
    rw [← UniformSpace.Completion.coe_add]
    congr 1
    apply Subtype.ext
    funext i
    change (τ.toPreGNS ((x + y) i) : τ.GNS) =
      (τ.toPreGNS (x i) : τ.GNS) + (τ.toPreGNS (y i) : τ.GNS)
    simp only [BoundedContinuousFunction.add_apply, map_add, UniformSpace.Completion.coe_add]
  map_smul' c x := by
    rw [← UniformSpace.Completion.coe_smul]
    congr 1
    apply Subtype.ext
    funext i
    change (τ.toPreGNS ((c • x) i) : τ.GNS) = c • (τ.toPreGNS (x i) : τ.GNS)
    simp only [BoundedContinuousFunction.smul_apply, map_smul, UniformSpace.Completion.coe_smul]

theorem algebraSequenceVector_norm (x : ℕ →ᵇ A) :
    ‖algebraSequenceVectorLinear τ h1 ω x‖ =
      sequenceTwoNorm (TracialUltrapower.traceHilbertMap τ h1) ω x := by
  change ‖(algebraSequenceVector τ h1 ω x :
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  apply tendsto_nhds_unique (UltraPreHilbert.norm_tendsto ω _)
  simpa only [algebraSequenceVector, UltraPreHilbert.family,
    UniformSpace.Completion.norm_coe, TracialUltrapower.traceHilbertMap_apply] using
    tendsto_sequenceTwoNorm (TracialUltrapower.traceHilbertMap τ h1) ω x

theorem algebraSequenceVector_null (x : ℕ →ᵇ A)
    (hx : x ∈ ideal τ h1 ω htr) : algebraSequenceVectorLinear τ h1 ω x = 0 := by
  apply norm_eq_zero.mp
  rw [algebraSequenceVector_norm]
  apply tendsto_nhds_unique (tendsto_sequenceTwoNorm _ _ x)
  exact (mem_nullSubmodule _ _ x).mp hx

/-- The algebra-sequence map factors through the actual tracial quotient. -/
def quotientGNSVector : Ultrapower τ h1 ω htr →ₗ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω :=
  (nullSubmodule (TracialUltrapower.traceHilbertMap τ h1).toLinearMap
    (ω : Filter ℕ)).liftQ (algebraSequenceVectorLinear τ h1 ω)
      (fun x hx => algebraSequenceVector_null τ h1 ω htr x hx)

@[simp] theorem quotientGNSVector_mk (x : ℕ →ᵇ A) :
    quotientGNSVector τ h1 ω htr (quotientHom τ h1 ω htr x) =
      algebraSequenceVectorLinear τ h1 ω x := rfl

/-- The tracial quotient's Hilbert norm is the ultralimit Hilbert norm. -/
def quotientPreGNSIsometry : (quotientTrace τ h1 ω htr).PreGNS →ₗᵢ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω where
  toLinearMap := (quotientGNSVector τ h1 ω htr).comp
    (quotientTrace τ h1 ω htr).ofPreGNS.toLinearMap
  norm_map' x := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      ((quotientTrace τ h1 ω htr).ofPreGNS x)
    change ‖quotientGNSVector τ h1 ω htr
      ((quotientTrace τ h1 ω htr).ofPreGNS x)‖ = ‖x‖
    have hx : x = (quotientTrace τ h1 ω htr).toPreGNS
        (quotientHom τ h1 ω htr a) := by
      apply (quotientTrace τ h1 ω htr).ofPreGNS.injective
      exact ha.symm
    rw [hx, PositiveLinearMap.ofPreGNS_toPreGNS, quotientGNSVector_mk,
      algebraSequenceVector_norm, quotientTrace_preGNS_norm]
    rfl

/-- The closed GNS subspace of the Hilbert ultrapower, constructed by completion. -/
def tracialUltrapowerGNSInclusion : (quotientTrace τ h1 ω htr).GNS →ₗᵢ[ℂ]
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω where
  toLinearMap := (quotientPreGNSIsometry τ h1 ω htr).toContinuousLinearMap.fromCompletion
    |>.toLinearMap
  norm_map' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      change ‖(quotientPreGNSIsometry τ h1 ω htr).toContinuousLinearMap.fromCompletion
        (x : (quotientTrace τ h1 ω htr).GNS)‖ = ‖(x : (quotientTrace τ h1 ω htr).GNS)‖
      rw [ContinuousLinearMap.fromCompletion_apply_coe, UniformSpace.Completion.norm_coe]
      exact (quotientPreGNSIsometry τ h1 ω htr).norm_map x

@[simp] theorem tracialUltrapowerGNSInclusion_mk (x : ℕ →ᵇ A) :
    tracialUltrapowerGNSInclusion τ h1 ω htr
      ((quotientTrace τ h1 ω htr).toPreGNS (quotientHom τ h1 ω htr x)) =
      algebraSequenceVectorLinear τ h1 ω x :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

end KadisonSimilarity

end

end OAI
