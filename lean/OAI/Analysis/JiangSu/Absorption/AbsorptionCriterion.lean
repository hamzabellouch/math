import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.RelativeCoefficient
import OAI.Analysis.JiangSu.Absorption.OneSidedIntertwiningChain2

namespace OAI

section

noncomputable section
namespace NonunitalRelative
open Pureness NonunitalGamma NormUltra NormUltra.QuotientAlgebra Filter CStarAbsorption
open scoped CStarAlgebra ENNReal TensorProduct

universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]
variable {A B E T : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [CStarAlgebra E] [CStarAlgebra T]
variable [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
variable (ι : A →⋆ₙₐ[ℂ] B) (k : B →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)
variable (hc : ∀ a d,Commute (k (ι a)) (κ d))
variable (hj : ∃ a : A,k (ι a)≠0) (φ : D →⋆ₐ[ℂ] CentralSequenceAlgebra (A := A) U)
variable (hD : IsNuclear.{u,u} D) (hs : Pureness.TopologicallySimple D)
variable (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (hf : Function.Injective f) (hd : DenseRange f)
variable (hh : ConnectedApproximateInnerHalfFlip f)
variable (hcoef : ∀ b : B,∀ ε : ℝ,0<ε → ∃ l : List (A×D),
  ‖coefficientSum (k.comp ι) κ l-k b‖<ε)

include hc hj φ hD hs hf hd hh hcoef in
theorem ambient_quotient_conjugacy : NonunitalIntertwining.AmbientQuotientConjugacy k U ι := by
  classical
  intro F G ε hε
  have hlist (b : G) : ∃ l : List (A×D),‖coefficientSum (k.comp ι) κ l-k b‖<ε/2 :=
    hcoef b (ε/2) (half_pos hε)
  choose l hl using hlist
  obtain ⟨u,hu⟩ := finite_coefficient_approximation U (k.comp ι) κ hc hj φ hD hs f hf hd hh l (half_pos hε)
  let v : unitary (QuotientAlgebra (fun _ : ℕ => E) U) :=
    Unitary.map (CStarConnectedLift.starMonoidHom (Centralizer U (k.comp ι)).subtype) u
  refine ⟨v,?_,?_⟩
  · intro a ha
    have he := unitary_conjugate_inclusion U (k.comp ι) u a
    change ‖((u:Centralizer U (k.comp ι)):QuotientAlgebra (fun _ : ℕ => E) U)*
      normInclusion U (k (ι a))*star ((u:Centralizer U (k.comp ι)):QuotientAlgebra (fun _ : ℕ => E) U)-
        normInclusion U (k (ι a))‖<ε
    rw [show normInclusion U (k (ι a))=normInclusion U ((k.comp ι) a) from rfl,he,sub_self,norm_zero]
    exact hε
  · intro b hb
    obtain ⟨x,hx⟩ := hu ⟨b,hb⟩
    refine ⟨x,?_⟩
    have hnorm : ‖normInclusion U (coefficientSum (k.comp ι) κ (l ⟨b,hb⟩))-normInclusion U (k b)‖<ε/2 := by
      rw [←map_sub,normInclusion_norm]
      exact hl ⟨b,hb⟩
    have htriangle := norm_sub_le_norm_sub_add_norm_sub
      ((v : QuotientAlgebra (fun _ : ℕ => E) U)*NonunitalNormMaps.quotientMap U (k.comp ι) x*
        star (v : QuotientAlgebra (fun _ : ℕ => E) U))
      (normInclusion U (coefficientSum (k.comp ι) κ (l ⟨b,hb⟩))) (normInclusion U (k b))
    have hx' : ‖(v : QuotientAlgebra (fun _ : ℕ => E) U)*NonunitalNormMaps.quotientMap U (k.comp ι) x*
        star (v : QuotientAlgebra (fun _ : ℕ => E) U)-
          normInclusion U (coefficientSum (k.comp ι) κ (l ⟨b,hb⟩))‖<ε/2 := hx
    linarith

include hc hj φ hD hs hf hd hh hcoef in
theorem equiv_of_central_embedding [TopologicalSpace.SeparableSpace B]
    (hi : Isometry ι) (hk : Isometry k)
    (hleft : ∀ (e : E) (b : B),e*k b∈Set.range k)
    (hright : ∀ (b : B) (e : E),k b*e∈Set.range k) : Nonempty (A ≃⋆ₐ[ℂ] B) :=
  NonunitalIntertwining.equiv_of_ambient_quotient_conjugacy k hk hleft hright U ι hi
    (ambient_quotient_conjugacy U ι k κ hc hj φ hD hs f hf hd hh hcoef)

end NonunitalRelative

end
end

end OAI
