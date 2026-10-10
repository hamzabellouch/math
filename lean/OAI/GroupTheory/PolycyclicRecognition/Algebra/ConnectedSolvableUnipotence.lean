import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedSolvableEigenvector
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonEigenspaceCommutators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntertwinedActionWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionDepth

namespace OAI

/-! # Uniform unipotence of the commutator action

Successive common eigenspaces of a connected solvable matrix action are
fixed by its commutator subgroup. Induction on the quotient dimension
therefore makes every sufficiently long mixed product of commutator
action differences zero.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K G : Type*} [Field K] [IsAlgClosed K] [Group G]
    [TopologicalSpace G] [PreconnectedSpace G] [SeparatelyContinuousMul G]
    [ContinuousInv G] [Group.IsSolvable G]

theorem connected_solvable_commutator_words {n : ℕ}
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι) :
    ∃ c : ℕ, ∀ w : List (commutator G), w.length = c →
      actionOperatorWord (fun a : commutator G =>
        (linearAction (ι a)).toLinearMap - 1) w = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨0, fun _ _ => ?_⟩
      ext v i
      exact Fin.elim0 i
    let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    obtain ⟨χ, hχ⟩ := connected_solvable_commonEigenspace hc₁ hc₂ ι hι
    let ρ := linearAction.toMonoidHom.comp ι
    let W := commonEigenspace (fun g => (ρ g).toLinearMap) χ
    have hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W := commonEigenspace_invariant ρ χ
    let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hχ
    let m := Module.finrank K ((Fin n → K) ⧸ W)
    have hm : m < n := by
      have he := W.finrank_quotient_add_finrank
      have hp := Module.finrank_pos (R := K) (M := W)
      rw [Module.finrank_fin_fun] at he
      change m + Module.finrank K W = n at he
      omega
    let e := (Module.finBasis K ((Fin n → K) ⧸ W)).equivFun
    let ρQ := quotientLinearAction ρ W hW
    let ιQ : G →* PolynomialMatrixGroup K m := coordinateLinearAction ρQ e
    have hιQ : Continuous ιQ := continuous_quotientLinearAction ι hι W hW e
    obtain ⟨c, hc⟩ := ih m hm ιQ hιQ
    let D := fun a : commutator G => (ρ a).toLinearMap - 1
    let E := fun a : commutator G => (linearAction (ιQ a)).toLinearMap - 1
    let q : (Fin n → K) →ₗ[K] (Fin m → K) := e.toLinearMap.comp W.mkQ
    have hint (a : commutator G) (v : Fin n → K) : q (D a v) = E a (q v) := by
      change q (ρ a v - v) = linearAction (ιQ a) (q v) - q v
      rw [map_sub, coordinateLinearAction_apply]
      change e (W.mkQ (ρ a v)) - q v = e (ρQ a (e.symm (e (W.mkQ v)))) - q v
      rw [e.symm_apply_apply]
      rfl
    refine ⟨c + 1, ?_⟩
    intro w hw
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons a w =>
      have hw' : w.length = c := by simp only [List.length_cons] at hw; omega
      have hz : actionOperatorWord E w = 0 := hc w hw'
      apply LinearMap.ext
      intro v
      change ρ a (actionOperatorWord D w v) - actionOperatorWord D w v = 0
      apply sub_eq_zero.mpr
      apply commutator_fixes_commonEigenspace ρ χ a
      change actionOperatorWord D w v ∈ W
      apply (Submodule.Quotient.mk_eq_zero W).mp
      apply e.injective
      have hq := actionOperatorWord_intertwines D E q hint w v
      rw [hz] at hq
      simpa only [q, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearMap.zero_apply, map_zero] using hq

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
