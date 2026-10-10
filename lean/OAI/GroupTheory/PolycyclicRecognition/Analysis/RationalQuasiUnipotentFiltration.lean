import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIndexQuasiUnipotentAction
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.TorsionFree

namespace OAI

/-! # Rational actions with finite-index vanishing difference words

Extend scalars to the algebraic closure for the common-eigenvector argument,
then descend the vanishing of operator words through the injective tensor map.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

variable {G V : Type} [Group G] [Group.FG G] [Group.IsSolvable G]
    [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

def algebraicClosureAction (ρ : G →* (V ≃ₗ[ℚ] V)) :
    G →* (((AlgebraicClosure ℚ) ⊗[ℚ] V) ≃ₗ[AlgebraicClosure ℚ]
      ((AlgebraicClosure ℚ) ⊗[ℚ] V)) where
  toFun g := (ρ g).baseChange ℚ (AlgebraicClosure ℚ) V V
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    change (ρ 1).toLinearMap.baseChange (AlgebraicClosure ℚ) = 1
    rw [map_one]
    exact LinearMap.baseChange_one _ _
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    change (ρ (g * h)).toLinearMap.baseChange (AlgebraicClosure ℚ) =
      (ρ g).toLinearMap.baseChange (AlgebraicClosure ℚ) *
        (ρ h).toLinearMap.baseChange (AlgebraicClosure ℚ)
    rw [map_mul]
    exact LinearMap.baseChange_mul _ _

theorem rationalAction_finiteIndex_unipotent_filtration
    (ρ : G →* (V ≃ₗ[ℚ] V))
    (hρ : ∀ g, ∃ m : ℕ, 0 < m ∧ IsNilpotent ((ρ g).toLinearMap ^ m - 1)) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ ∃ c : ℕ,
      linearActionFiltration (fun a : H => (ρ a).toLinearMap - 1) c = ⊥ := by
  let L := AlgebraicClosure ℚ
  let U := L ⊗[ℚ] V
  let ρL := algebraicClosureAction ρ
  let e := (Module.finBasis L U).equivFun
  let ι := PolynomialMatrixGroup.coordinateLinearAction ρL e
  have hι (g : G) : ∃ m : ℕ, 0 < m ∧
      IsNilpotent ((PolynomialMatrixGroup.linearAction (ι g)).toLinearMap ^ m - 1) := by
    have hL : ∃ m : ℕ, 0 < m ∧ IsNilpotent ((ρL g).toLinearMap ^ m - 1) := by
      obtain ⟨m, hm, hn⟩ := hρ g
      refine ⟨m, hm, ?_⟩
      have hh := hn.map (Module.End.baseChangeHom ℚ L V).toRingHom
      change IsNilpotent ((ρ g).toLinearMap.baseChange L ^ m - 1)
      change IsNilpotent (((ρ g).toLinearMap ^ m - 1).baseChange L) at hh
      rw [LinearMap.baseChange_sub, LinearMap.baseChange_pow, LinearMap.baseChange_one] at hh
      exact hh
    apply unipotent_power_of_surjective_intertwining e.toLinearMap e.surjective
      (ρL g).toLinearMap _ _ hL
    intro v
    change e (ρL g v) = PolynomialMatrixGroup.linearAction (ι g) (e v)
    rw [PolynomialMatrixGroup.coordinateLinearAction_apply, e.symm_apply_apply]
  obtain ⟨H, hHn, hHi, c, hc⟩ :=
    PolynomialMatrixGroup.exists_finiteIndex_quasiUnipotent_words ι hι
  refine ⟨H, hHn, hHi, c, linearActionFiltration_eq_bot_of_word_zero _ c ?_⟩
  let q : V → (Fin (Module.finrank L U) → L) := fun v => e ((1 : L) ⊗ₜ[ℚ] v)
  have hq : Function.Injective q :=
    e.injective.comp (Module.Flat.tensorProduct_mk_injective ℚ V L)
  let D := fun a : H => (ρ a).toLinearMap - 1
  let E := fun a : H => (PolynomialMatrixGroup.linearAction (ι a)).toLinearMap - 1
  have hint (a : H) (v : V) : q (D a v) = E a (q v) := by
    change e ((1 : L) ⊗ₜ[ℚ] (ρ a v - v)) =
      PolynomialMatrixGroup.linearAction (ι a) (e ((1 : L) ⊗ₜ[ℚ] v)) -
        e ((1 : L) ⊗ₜ[ℚ] v)
    rw [TensorProduct.tmul_sub, map_sub,
      PolynomialMatrixGroup.coordinateLinearAction_apply, e.symm_apply_apply]
    rfl
  intro w hw
  apply LinearMap.ext
  intro v
  apply hq
  have hh := actionOperatorWord_intertwines_function D E q hint w v
  rw [hc w hw] at hh
  simpa only [q, LinearMap.zero_apply, TensorProduct.tmul_zero, map_zero] using hh

end PolycyclicRecognition

end

end OAI
