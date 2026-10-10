import Mathlib
import OAI.Analysis.WeakInfiniteness.CPDefect
import OAI.Analysis.WeakInfiniteness.CuntzPairCorrection

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma exists_cuntzPair_near_cpc_images (r s : A)
    (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ φ : A →L[ℂ] B,CompletelyPositive φ → ‖φ‖≤1 →
      ‖φ 1-1‖<δ → ‖φ 1-star (φ r)*φ r‖<δ →
      ‖φ 1-star (φ s)*φ s‖<δ →
      ∃ x y : B,star x*x=1 ∧ star y*y=1 ∧ star x*y=0 ∧
        ‖x-φ r‖<ε ∧ ‖y-φ s‖<ε := by
  obtain ⟨κ,hκ,hcorr⟩ := exists_cuntzPair_near (A := B) ε hε
  let δ : ℝ := min (κ/4) (κ^2/4)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro φ hφ hφn hu hdr hds
  have hdκ : δ≤κ/4 := min_le_left _ _
  have hdκsq : δ≤κ^2/4 := min_le_right _ _
  have hn (z : A) (hz : star z*z=1) : ‖φ z‖≤1 := by
    have he := congrArg norm hz
    rw [CStarRing.norm_star_mul_self] at he
    have h1 : ‖(1:A)‖≤1 := cstar_norm_one_le_one
    have hzn : ‖z‖≤1 := by nlinarith [norm_nonneg z]
    exact (φ.le_opNorm z).trans ((mul_le_mul hφn hzn
      (norm_nonneg _) zero_le_one).trans (by norm_num))
  have herr := cpc_cuntzPair_errors hφ hφn r s hr hs hrs
  apply hcorr (φ r) (φ s) (hn r hr) (hn s hs)
  · have h := herr.1
    linarith
  · have h := herr.2.1
    linarith
  · have h := herr.2.2
    have h0 := norm_nonneg (star (φ r)*φ s)
    nlinarith

end

end WeakPureInfiniteness
end

end OAI
