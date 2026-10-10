import OAI.Analysis.Pureness.Operators.PositiveStateSeparation
import OAI.Analysis.Pureness.Operators.HilbertSumRepresentation

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace ComplexOrder
local instance universalStateGNSDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def PositiveStateIndex := {f : A →ₚ[ℂ] ℂ // f 1 = 1}

abbrev UniversalStateHilbert := lp (fun f : PositiveStateIndex A => f.1.GNS) 2

def universalStateGNS : A →⋆ₐ[ℂ]
    (UniversalStateHilbert A →L[ℂ] UniversalStateHilbert A) :=
  hilbertSumRepresentation (fun f : PositiveStateIndex A => f.1.gnsStarAlgHom)

lemma universalStateGNS_apply (a : A) (x : UniversalStateHilbert A) (f : PositiveStateIndex A) :
    universalStateGNS A a x f = f.1.gnsStarAlgHom a (x f) := rfl

theorem universalStateGNS_injective : Function.Injective (universalStateGNS A) := by
  cases subsingleton_or_nontrivial A with
  | inl h => exact fun _ _ _ => Subsingleton.elim _ _
  | inr h =>
    apply (universalStateGNS A).toLinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply stateGNS_separates a
    intro f hf1
    have h := (hilbertSumRepresentation_eq_iff
      (fun g : PositiveStateIndex A => g.1.gnsStarAlgHom) a 0).mp
      (ha.trans (map_zero (universalStateGNS A)).symm) ⟨f, hf1⟩
    simpa only [map_zero] using h

lemma universalStateGNS_isometry : Isometry (universalStateGNS A) :=
  NonUnitalStarAlgHom.isometry (universalStateGNS A).toNonUnitalStarAlgHom
    (universalStateGNS_injective A)

lemma universalStateGNS_norm (a : A) : ‖universalStateGNS A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (universalStateGNS A).toNonUnitalStarAlgHom
    (universalStateGNS_injective A) a

def universalStateGNSInclusion (f : PositiveStateIndex A) :
    f.1.GNS →ₗᵢ[ℂ] UniversalStateHilbert A where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun g : PositiveStateIndex A => g.1.GNS) 2 f
  norm_map' x := by
    change ‖lp.single (E := fun g : PositiveStateIndex A => g.1.GNS) 2 f x‖ = ‖x‖
    exact lp.norm_single (E := fun g : PositiveStateIndex A => g.1.GNS) (by norm_num : (0 : ENNReal) < 2) f x

lemma universalStateGNSInclusion_intertwines (f : PositiveStateIndex A)
    (a : A) (x : f.1.GNS) :
    universalStateGNS A a (universalStateGNSInclusion A f x) =
      universalStateGNSInclusion A f (f.1.gnsStarAlgHom a x) := by
  classical
  apply lp.ext
  funext g
  change g.1.gnsStarAlgHom a (lp.single (E := fun g : PositiveStateIndex A => g.1.GNS) 2 f x g) =
    lp.single (E := fun g : PositiveStateIndex A => g.1.GNS) 2 f (f.1.gnsStarAlgHom a x) g
  by_cases h : g = f
  · subst g
    simp
  · simp [lp.single_apply, Pi.single_eq_of_ne h]

lemma universalStateGNS_vector_value (f : PositiveStateIndex A) (a : A) :
    ⟪universalStateGNSInclusion A f (stateGNSVector f.1),
      universalStateGNS A a (universalStateGNSInclusion A f (stateGNSVector f.1))⟫_ℂ = f.1 a := by
  rw [universalStateGNSInclusion_intertwines, LinearIsometry.inner_map_map]
  exact stateGNS_vector_value f.1 a
end CuntzPureness

end

end OAI
