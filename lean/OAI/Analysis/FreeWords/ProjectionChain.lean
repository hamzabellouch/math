import Mathlib
import OAI.Analysis.FreeWords.ProjectionStructure

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport

open UniversalStrongKK Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem trace_tendsto_bounded_wot {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    {I : Type*} {l : Filter I} {f : I → ConcreteAlgebra M} {v : ConcreteAlgebra M}
    (hf : ∀ i, ‖f i‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (ht : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i : H →L[ℂ] H)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM (v : H →L[ℂ] H)))) :
    Tendsto (fun i => τ.map (f i)) l (𝓝 (τ.map v)) := by
  let fw : I → WeakAlgebra M := fun i => ⟨ContinuousLinearMapWOT.ofCLM (f i : H →L[ℂ] H),(f i).property⟩
  let vw : WeakAlgebra M := ⟨ContinuousLinearMapWOT.ofCLM (v : H →L[ℂ] H),v.property⟩
  have htw : Tendsto fw l (𝓝 vw) := tendsto_subtype_rng.mpr ht
  have htw' : Tendsto fw l (𝓝[{T : WeakAlgebra M | ‖T.val.toCLM‖ ≤ 1}] vw) :=
    tendsto_nhdsWithin_iff.mpr ⟨htw,Eventually.of_forall hf⟩
  exact (τ.normal 1 vw hv).tendsto.comp htw'

theorem projection_directed_limit {M : VonNeumannAlgebra H}
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (f : I → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (f i)) (hf : Monotone f) :
    ∃ v : ConcreteAlgebra M, IsStarProjection v ∧ (∀ i, f i ≤ v) ∧
      ∃ ω : Ultrafilter I, (ω : Filter I) ≤ atTop ∧
        Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i : H →L[ℂ] H)) (ω : Filter I)
          (𝓝 (ContinuousLinearMapWOT.ofCLM (v : H →L[ℂ] H))) := by
  let F (i : I) : PartialIso (H →L[ℂ] H) := ⟨(f i : H →L[ℂ] H),by
    have hh := concrete_projection_coe (hp i)
    change (f i : H →L[ℂ] H)*star (f i : H →L[ℂ] H)*(f i : H →L[ℂ] H)=f i
    rw [hh.isSelfAdjoint.star_eq,hh.isIdempotentElem.eq,hh.isIdempotentElem.eq]⟩
  have hF : Monotone F := by
    intro i j hij
    have hi := hp i
    have hji := hi.le_iff_mul_eq_right (hp j) |>.mp (hf hij)
    have hij' := hi.le_iff_mul_eq_left (hp j) |>.mp (hf hij)
    constructor
    · change (f j : H →L[ℂ] H)*(star (f i : H →L[ℂ] H)*(f i : H →L[ℂ] H))=f i
      rw [(concrete_projection_coe hi).isSelfAdjoint.star_eq,
        (concrete_projection_coe hi).isIdempotentElem.eq]
      exact congrArg Subtype.val hji
    · change star (f i : H →L[ℂ] H)*(f j : H →L[ℂ] H)=star (f i : H →L[ℂ] H)*(f i : H →L[ℂ] H)
      rw [(concrete_projection_coe hi).isSelfAdjoint.star_eq,
        (concrete_projection_coe hi).isIdempotentElem.eq]
      exact congrArg Subtype.val hij'
  obtain ⟨V,hV,ω,hω,hlim⟩ := partialIso_directed_limit F hF
  have hVM : V.value ∈ M := mem_of_wot_tendsto M hlim (Eventually.of_forall fun i => (f i).property)
  have hVs : star V.value=V.value := by
    have hs := hlim.star
    change Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (star (f i : H →L[ℂ] H))) (ω : Filter I)
      (𝓝 (ContinuousLinearMapWOT.ofCLM (star V.value))) at hs
    have he (i : I) : star (f i : H →L[ℂ] H)=(f i : H →L[ℂ] H) :=
      (concrete_projection_coe (hp i)).isSelfAdjoint.star_eq
    simp only [he] at hs
    exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique hs hlim)
  have hVi (i : I) : V.value*(f i : H →L[ℂ] H)=f i := by
    have hh := (hV i).1
    change V.value*(star (f i : H →L[ℂ] H)*(f i : H →L[ℂ] H))=f i at hh
    simpa only [(concrete_projection_coe (hp i)).isSelfAdjoint.star_eq,
      (concrete_projection_coe (hp i)).isIdempotentElem.eq] using hh
  have hVV : V.value*V.value=V.value := by
    have ht := wot_const_mul hlim V.value
    change Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (V.value*(f i : H →L[ℂ] H))) _ _ at ht
    simp only [hVi] at ht
    exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique ht hlim)
  let v : ConcreteAlgebra M := ⟨V.value,hVM⟩
  have hv : IsStarProjection v := ⟨Subtype.ext hVV,Subtype.ext hVs⟩
  exact ⟨v,hv,(fun i => ((hp i).le_iff_mul_eq_right hv).mpr (Subtype.ext (hVi i))),ω,hω,hlim⟩

end

end KKProjectionSupport
end

end OAI
