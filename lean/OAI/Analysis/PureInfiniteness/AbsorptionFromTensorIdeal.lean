import OAI.Analysis.PureInfiniteness.SupportedPairConstruction
import OAI.Analysis.PureInfiniteness.AbsorptionFromCentralCopy

namespace OAI

/-! Absorption from local relative Cuntz pairs, the common-null tensor-ideal
span property (KR02 Lemma 7.18, using Blackadar Theorem 3.3), and a connected
approximate half-flip (Kirchberg 2006, Proposition 4.4 and Remark 4.6). -/

noncomputable section
open Filter
open scoped TensorProduct

namespace WeakPureInfiniteness.Campaign

universe u w
variable {A : Type u} [NonUnitalCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A]

local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem nuclear_absorption_from_tensor_ideal_and_halfFlip
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (hNuclear : Nuclear A)
    (hspan : ∀ (I : Type u) [Fintype I]
      (l : I → selfAdjoint (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) →L[ℝ] ℝ)
      (R : FunctionalTensorRepresentation l),
      R.elementarySpan U hNuclear (NonunitalGamma.normInclusion (A := A) U))
    {T : Type w} [CStarAlgebra T]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f)
    {n : ℕ} (hn : 1 ≤ n) (hF : FixedAmplification A n) : AbsorbsOInfinity A := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let := hA
    exact absorbsOInfinity_of_subsingleton A
  | inr hA =>
    let := hA
    have hP : MainGap.PropertyP A := fun a ha =>
      properlyInfinite_to_mainGap ((nuclear_fixedAmplification hNuclear hn hF).1 a ha)
    obtain ⟨φ⟩ := centralOInfinity_of_nuclear_and_elementary_span U hP hNuclear hspan
    exact minimalTensor_equiv_of_central_embedding U φ
      oInfinity_isNuclear oInfinity_topologicallySimple f hf hd hh

end WeakPureInfiniteness.Campaign

end

end OAI
