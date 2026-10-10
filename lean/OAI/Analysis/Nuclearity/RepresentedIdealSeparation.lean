import OAI.Analysis.Nuclearity.RepresentedTensorKernel
import OAI.Analysis.Nuclearity.TensorSurjectivity
import OAI.Analysis.Nuclearity.ClosedIdealImage
import OAI.Analysis.Nuclearity.PureProductIdealDetection
import OAI.Analysis.Nuclearity.ProductPurePullback

namespace OAI

/-! Product pure-state ideal separation for a fixed factor representation.
The only nuclearity input here concerns its actual represented left image. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u w
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem productPure_separates_ideals_of_representation
    (I J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (H : ComplexHilbert.{w})
    (π : UnitalTensorRepresentation (A := A) (B := B) (H := H))
    (X : RepresentedImageData (leftRepresentedMap π))
    (Y : RepresentedImageData (rightRepresentedMap π))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ c : ℂ, T = c • 1)
    (hN : Pureness.IsNuclear.{w,w} X.Carrier)
    (hI : ∀ x ∈ I.module, π x = 0)
    (z : MinimalTensor A B) (hz : z ∈ J.module) (hne : π z ≠ 0) :
    ∃ F : ProductPureFunctional A B,
      (∀ x ∈ I.module, F.functional x = 0) ∧
      ∃ x ∈ J.module, F.functional x ≠ 0 := by
  let _ : PartialOrder X.Carrier := CStarAlgebra.spectralOrder X.Carrier
  let _ : StarOrderedRing X.Carrier := CStarAlgebra.spectralOrderedRing X.Carrier
  let _ : PartialOrder Y.Carrier := CStarAlgebra.spectralOrder Y.Carrier
  let _ : StarOrderedRing Y.Carrier := CStarAlgebra.spectralOrderedRing Y.Carrier
  let q := representedTensorQuotient π X Y
  have hq : Function.Surjective q := minimalMapAny_surjective _ _
    X.surjective Y.surjective
  have hk (x : MinimalTensor A B) : q x = 0 ↔ π x = 0 :=
    representedTensorQuotient_kernel π X Y hs hN x
  let K := closedIdealImage q hq J
  obtain ⟨f, g, y, hy, hfy⟩ := exists_pureProduct_detecting_ideal K (q z)
    (mem_closedIdealImage q hq J z hz) (fun h => hne ((hk z).mp h))
  let F := faithfulPureProductFunctional f g
  obtain ⟨G, hG⟩ := exists_productPure_pullback
    X.quotient Y.quotient X.surjective Y.surjective F
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    rw [hG]
    change F.functional (q x) = 0
    rw [(hk x).mpr (hI x hx), map_zero]
  · by_contra h
    have hzero (x : MinimalTensor A B) (hx : x ∈ J.module) : F.functional (q x) = 0 := by
      by_contra hh
      exact h ⟨x, hx, (hG x).trans_ne hh⟩
    exact hfy (functional_zero_on_closedIdealImage q hq J F.functional hzero y hy)

end WeakPureInfiniteness

end

end OAI
