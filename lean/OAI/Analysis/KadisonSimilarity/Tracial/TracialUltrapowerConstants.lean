import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerActions
import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry

namespace OAI

/-! Both ultrapower constructions preserve the original constant Hilbert
space exactly. Compression back to that space recovers the original operator. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower NuclearUltrapower
open scoped ComplexOrder Topology BoundedContinuousFunction

theorem compression_through_composite
    {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : F →L[ℂ] K) (J : E →L[ℂ] F) (T : K →L[ℂ] K) :
    J.adjoint.comp ((V.adjoint.comp (T.comp V)).comp J) =
      (V.comp J).adjoint.comp (T.comp (V.comp J)) := by
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- The trace-preserving constant inclusion gives the actual GNS inclusion. -/
def constantTracialGNSInclusion : τ.GNS →ₗᵢ[ℂ] (quotientTrace τ h1 ω htr).GNS :=
  gnsTracialHomIsometry τ (quotientTrace τ h1 ω htr) (constant τ h1 ω htr)
    (quotientTrace_constant τ h1 ω htr)

/-- Going through the tracial quotient agrees with the constant Hilbert
ultrapower inclusion on the entire completed Hilbert space. -/
theorem tracialUltrapower_constant_inclusion :
    (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap.comp
      (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap =
      (constantHilbertInclusion (H := τ.GNS) ω).toContinuousLinearMap := by
  ext ξ
  refine (gnsTracialVector_dense τ).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change tracialUltrapowerGNSInclusion τ h1 ω htr
    (gnsTracialHomIsometry τ (quotientTrace τ h1 ω htr) (constant τ h1 ω htr)
      (quotientTrace_constant τ h1 ω htr) (gnsTracialVector τ a)) = _
  rw [gnsTracialHomIsometry_vector]
  change tracialUltrapowerGNSInclusion τ h1 ω htr
    ((quotientTrace τ h1 ω htr).toPreGNS
      (quotientHom τ h1 ω htr (constantSequence a))) = _
  rw [tracialUltrapowerGNSInclusion_mk]
  change algebraSequenceVectorLinear τ h1 ω (constantSequence a) =
    constantHilbertInclusion ω (gnsTracialVector τ a)
  rw [constantHilbertInclusion_apply]
  change (algebraSequenceVector τ h1 ω (constantSequence a) :
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω) =
    (constantPreHilbert ω (gnsTracialVector τ a) :
      HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω)
  congr 1

/-- The compressed ultrapower operator agrees with the original operator
after compression to the constant tracial subspace. -/
theorem constant_compression_tracialUltrapower (T : τ.GNS →L[ℂ] τ.GNS) :
    (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap.adjoint.comp
      ((tracialUltrapowerCompression τ h1 ω htr T).comp
        (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap) = T := by
  let V := (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap
  let J := (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap
  let C := (constantHilbertInclusion (H := τ.GNS) ω).toContinuousLinearMap
  have hVJ : V.comp J = C := tracialUltrapower_constant_inclusion τ h1 ω htr
  change J.adjoint.comp ((V.adjoint.comp
    ((HilbertUltraproduct.map ω (boundedConstant T)).comp V)).comp J) = T
  rw [compression_through_composite, hVJ]
  exact compression_map_constant_operator ω T

end KadisonSimilarity

end

end OAI
