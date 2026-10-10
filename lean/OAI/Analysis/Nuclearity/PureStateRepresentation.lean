import OAI.Analysis.WeakInfiniteness.FaithfulRepresentation
import OAI.Analysis.JiangSu.Excision.PureStateNorming
import OAI.Analysis.JiangSu.CStarAlgebras.StateCoefficientApproximation

namespace OAI

/-! A faithful sum of pure GNS representations. This supplies the faithful
representation needed to detect nonzero ideals by product pure states. -/

noncomputable section
open scoped ComplexOrder ENNReal

namespace WeakPureInfiniteness

universe u
variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure PureStateData where
  state : A →ₚ[ℂ] ℂ
  unital : state 1 = 1
  pure : PureStateExcision.ofPositiveState state unital ∈
    (PureStateExcision.realStateCarrier (A := A)).extremePoints ℝ

local instance pureStateDecidable : DecidableEq (PureStateData A) := Classical.decEq _

def pureGNSHilbert : ComplexHilbert.{u} where
  Carrier := lp (fun f : PureStateData A => f.state.GNS) 2

def pureGNSRepresentation : A →⋆ₙₐ[ℂ] (pureGNSHilbert A →L[ℂ] pureGNSHilbert A) :=
  sumRepresentation (fun f : PureStateData A => f.state.gnsNonUnitalStarAlgHom)

theorem pureGNSRepresentation_injective : Function.Injective (pureGNSRepresentation A) := by
  apply sumRepresentation_injective
  intro a ha
  by_cases hA : Subsingleton A
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply PureStateExcision.norm_le_of_pure_gns a le_rfl
    intro f hf hp
    change ‖f.gnsNonUnitalStarAlgHom a‖ ≤ 0
    rw [ha ⟨f, hf, hp⟩, norm_zero]

@[simp] theorem pureGNSRepresentation_single (a : A) (f : PureStateData A)
    (ξ : f.state.GNS) :
    pureGNSRepresentation A a (lp.single 2 f ξ) =
      lp.single 2 f (f.state.gnsNonUnitalStarAlgHom a ξ) := by
  classical
  change (sumRepresentation (fun f : PureStateData A => f.state.gnsNonUnitalStarAlgHom)
    a (lp.single 2 f ξ) : lp (fun f : PureStateData A => f.state.GNS) 2) = _
  ext g
  by_cases h : g = f
  · subst g
    simp [sumRepresentation_apply]
  · simp [sumRepresentation_apply, lp.single_apply, h]

theorem pureGNS_operator_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : pureGNSHilbert A →L[ℂ] E)
    (hT : ∀ (f : PureStateData A) (a : A),
      T (lp.single 2 f (f.state.gnsStarAlgHom a (Pureness.stateGNSVector f.state))) = 0) :
    T = 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro f
  apply ContinuousLinearMap.ext
  intro ξ
  change T (lp.single 2 f ξ) = 0
  refine (NuclearNorm.stateGNS_cyclic f.state).induction_on (p := fun ξ => T (lp.single 2 f ξ) = 0) ξ ?_ ?_
  · exact isClosed_eq (T.continuous.comp
      (lp.singleContinuousLinearMap ℂ (fun g : PureStateData A => g.state.GNS) 2 f).continuous)
      continuous_const
  · exact hT f

end WeakPureInfiniteness

end

end OAI
