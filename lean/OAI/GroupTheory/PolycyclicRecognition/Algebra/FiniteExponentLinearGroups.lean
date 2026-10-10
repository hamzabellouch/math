import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrderMatrixTraces
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteExponentSubquotients
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixScalarExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

namespace OAI

/-! # Characteristic-zero matrix groups of finite exponent are finite

The irreducible case follows from finite trace coordinates. For a reducible
action, induction applies to the actual subspace and quotient images, and
the pair of images detects every element of finite order.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

theorem coordinateLinearAction_eq_implies_eq
    {K G U : Type*} [Field K] [Group G] [AddCommGroup U] [Module K U] {n : ℕ}
    (ρ : G →* (U ≃ₗ[K] U)) (e : U ≃ₗ[K] (Fin n → K)) {g h : G}
    (he : coordinateLinearAction ρ e g = coordinateLinearAction ρ e h) : ρ g = ρ h := by
  apply LinearEquiv.ext
  intro x
  apply e.injective
  have hh := congrArg (fun A : PolynomialMatrixGroup K n => linearAction A (e x)) he
  simpa only [coordinateLinearAction_apply, e.symm_apply_apply] using hh

theorem finite_of_faithful_common_exponent
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K] (n : ℕ) :
    ∀ (G : Type) [Group G], ∀ ι : G →* PolynomialMatrixGroup K n,
      Function.Injective ι → ∀ m : ℕ, 0 < m → (∀ g : G, g ^ m = 1) → Finite G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ ι hinj m hm hpow
    classical
    by_cases hn : n = 0
    · subst n
      have hsub : Subsingleton G := ⟨fun g h => hinj (by
        apply PolynomialMatrixGroup.ext
        apply Units.ext
        ext i
        exact Fin.elim0 i)⟩
      let := hsub
      infer_instance
    let ρ := linearAction.toMonoidHom.comp ι
    let R : Representation K G (Fin n → K) :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
    by_cases hR : R.IsIrreducible
    · let := hR
      exact finite_of_irreducible_common_exponent ι hinj m hm hpow
    let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have htop : (⊤ : Subrepresentation R) ≠ ⊥ := by
      intro he
      have hh : (⊤ : Submodule K (Fin n → K)) = ⊥ :=
        congrArg Subrepresentation.toSubmodule he
      exact top_ne_bot hh
    let : Nontrivial (Subrepresentation R) := ⟨⟨⊤, ⊥, htop⟩⟩
    have hex : ∃ W : Subrepresentation R, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra! h
      exact hR { eq_bot_or_eq_top := fun W => or_iff_not_imp_left.mpr (h W) }
    obtain ⟨W, hW0, hWtop⟩ := hex
    let U := W.toSubmodule
    have hU0 : U ≠ ⊥ := by
      intro he
      exact hW0 (Subrepresentation.toSubmodule_injective he)
    have hUtop : U ≠ ⊤ := by
      intro he
      exact hWtop (Subrepresentation.toSubmodule_injective he)
    have hU (g : G) (x : Fin n → K) (hx : x ∈ U) : ρ g x ∈ U :=
      W.apply_mem_toSubmodule g hx
    let rU := invariantSubspaceAction ρ U hU
    let rQ := quotientLinearAction ρ U hU
    let eU := (Module.finBasis K U).equivFun
    let eQ := (Module.finBasis K ((Fin n → K) ⧸ U)).equivFun
    let jU := coordinateLinearAction rU eU
    let jQ := coordinateLinearAction rQ eQ
    have hdU : Module.finrank K U < n := by
      simpa only [Module.finrank_fin_fun] using Submodule.finrank_lt hUtop
    have hdQ : Module.finrank K ((Fin n → K) ⧸ U) < n := by
      let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU0
      have hp := Module.finrank_pos (R := K) (M := U)
      have he := U.finrank_quotient_add_finrank
      rw [Module.finrank_fin_fun] at he
      omega
    have hpU (g : jU.range) : g ^ m = 1 := by
      obtain ⟨a, ha⟩ := jU.rangeRestrict_surjective g
      rw [← ha, ← map_pow, hpow, map_one]
    have hpQ (g : jQ.range) : g ^ m = 1 := by
      obtain ⟨a, ha⟩ := jQ.rangeRestrict_surjective g
      rw [← ha, ← map_pow, hpow, map_one]
    let : Finite jU.range := ih _ hdU jU.range jU.range.subtype Subtype.val_injective m hm hpU
    let : Finite jQ.range := ih _ hdQ jQ.range jQ.range.subtype Subtype.val_injective m hm hpQ
    have hr : Function.Injective ρ := linearAction.injective.comp hinj
    have hf := subquotient_action_pair_injective_of_finite_exponent ρ hr U hU m hm hpow
    let f : G → jU.range × jQ.range := fun g => (jU.rangeRestrict g, jQ.rangeRestrict g)
    apply Finite.of_injective f
    intro g h he
    apply hf
    have heU := congrArg (fun p : jU.range × jQ.range => p.1.val) he
    have heQ := congrArg (fun p : jU.range × jQ.range => p.2.val) he
    exact Prod.ext (coordinateLinearAction_eq_implies_eq rU eU heU)
      (coordinateLinearAction_eq_implies_eq rQ eQ heQ)

theorem finite_of_faithful_common_exponent_charZero
    {K G : Type} [Field K] [CharZero K] [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    (m : ℕ) (hm : 0 < m) (hpow : ∀ g : G, g ^ m = 1) : Finite G := by
  let f := algebraMap K (AlgebraicClosure K)
  exact finite_of_faithful_common_exponent n G ((scalarExtension f).comp ι)
    ((scalarExtension_injective f).comp hι) m hm hpow

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
