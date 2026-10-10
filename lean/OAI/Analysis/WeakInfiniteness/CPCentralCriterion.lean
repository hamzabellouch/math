import Mathlib
import OAI.Analysis.WeakInfiniteness.CPCorrection
import OAI.Analysis.WeakInfiniteness.CentralExactPair

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

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma localCentralExactCuntzPair_of_cpc_schwarz_control
    (r s : A) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0)
    (hchoose : ∀ (F : Finset A) (δ : ℝ),0<δ →
      ∃ φ : A →L[ℂ] A,CompletelyPositive φ ∧ ‖φ‖≤1 ∧
        ‖φ 1-1‖<δ ∧ ‖φ 1-star (φ r)*φ r‖<δ ∧
        ‖φ 1-star (φ s)*φ s‖<δ ∧
        ∀ a∈F,∀ z : A,‖z‖≤1 → ‖a*φ z-φ z*a‖<δ) :
    LocalCentralExactCuntzPair A := by
  classical
  intro F ε hε
  let M : ℝ := 1+∑ a∈F,‖a‖
  have hM : 0<M := by dsimp only [M]; positivity
  have haM (a : A) (ha : a∈F) : ‖a‖≤M := by
    have h := Finset.single_le_sum (f := fun a : A => ‖a‖) (fun _ _ => norm_nonneg _) ha
    dsimp only [M]
    linarith
  let η : ℝ := ε/(4*M+4)
  have hη : 0<η := div_pos hε (by linarith)
  have hηε : (4*M+4)*η=ε := mul_div_cancel₀ _ (by linarith)
  obtain ⟨δ,hδ,hcorr⟩ := exists_cuntzPair_near_cpc_images (B := A) r s hr hs hrs η hη
  let κ : ℝ := min δ (ε/2)
  have hκ : 0<κ := lt_min hδ (by positivity)
  obtain ⟨φ,hφ,hφn,hu,hdr,hds,hF⟩ := hchoose F κ hκ
  obtain ⟨x,y,hx,hy,hxy,hxr,hys⟩ := hcorr φ hφ hφn
    (hu.trans_le (min_le_left _ _)) (hdr.trans_le (min_le_left _ _))
    (hds.trans_le (min_le_left _ _))
  have hn (z : A) (hz : star z*z=1) : ‖z‖≤1 := by
    have he := congrArg norm hz
    rw [CStarRing.norm_star_mul_self] at he
    have h1 : ‖(1:A)‖≤1 := cstar_norm_one_le_one
    nlinarith [norm_nonneg z]
  refine ⟨x,y,hx,hy,hxy,?_⟩
  intro a ha
  have hb (z w : A) (hz : ‖a*z-z*a‖<κ) (hw : ‖w-z‖<η) :
      ‖a*w-w*a‖<ε := by
    have hle := norm_commutator_perturbation_le a w z
    have hκle : κ≤ε/2 := min_le_right _ _
    have hprod : 2*‖a‖*‖w-z‖≤2*M*η := by
      gcongr
      exact haM a ha
    nlinarith
  exact ⟨hb (φ r) x (hF a ha r (hn r hr)) hxr,
    hb (φ s) y (hF a ha s (hn s hs)) hys⟩

end

end WeakPureInfiniteness
end

end OAI
