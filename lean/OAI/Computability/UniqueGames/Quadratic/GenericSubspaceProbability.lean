import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Quadratic.AlignmentCertificateLemmas
import OAI.Computability.UniqueGames.Quadratic.GenericSeparationLemmas
import OAI.Computability.UniqueGames.Quadratic.UniformSubspaces

namespace OAI

section

/-!
The polynomial exceptional-event bound is transported first to all binary
linear parameter maps and then, by proved uniformity conditional on
injectivity, to the actual finite Grassmannian.  The same argument supplies
a generic subspace, rather than presupposing that one exists.
-/

noncomputable section

open Module
open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic

private theorem conditioning_counts {A : Type*} [Fintype A] [Nonempty A]
    (P Q : A → Prop) (α : ℚ) (hα : α < 1)
    (hbad : (Nat.card {a : A // ¬(P a ∧ Q a)} : ℚ) / Nat.card A ≤ α) :
    (∃ a : A, P a ∧ Q a) ∧
      (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤ α * Nat.card A ∧
      (1 - α) * Nat.card A ≤ (Nat.card {a : A // P a} : ℚ) := by
  classical
  have hpos : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hbadCount := (div_le_iff₀ hpos).mp hbad
  have hgood : ∃ a : A, P a ∧ Q a := by
    by_contra h
    have hall : ∀ a : A, ¬(P a ∧ Q a) := fun a ha => h ⟨a, ha⟩
    have hcard : Nat.card {a : A // ¬(P a ∧ Q a)} = Nat.card A := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hall]
    rw [hcard, div_self hpos.ne'] at hbad
    exact (not_le_of_gt hα) hbad
  have hnoninj : Nat.card {a : A // ¬P a} ≤ Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : A // ¬P a} => (⟨a.1, fun h => a.2 h.1⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hbadInj : Nat.card {a : {a : A // P a} // ¬Q a.1} ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : {a : A // P a} // ¬Q a.1} =>
        (⟨a.1.1, fun h => a.2 h.2⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hpartitionNat : Nat.card {a : A // P a} + Nat.card {a : A // ¬P a} = Nat.card A := by
    have hle := Fintype.card_subtype_le P
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    omega
  have hpartition : (Nat.card {a : A // P a} : ℚ) +
      Nat.card {a : A // ¬P a} = Nat.card A := by exact_mod_cast hpartitionNat
  have hn : (Nat.card {a : A // ¬P a} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hnoninj
  have hb : (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hbadInj
  refine ⟨hgood, hb.trans hbadCount, ?_⟩
  linarith

variable {F J : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] [Fintype J]

/-- Both generic-subspace existence and the conditional Grassmannian bound
follow from the single unconditional parameter-map exceptional bound. -/
theorem generic_subspace_and_probability_of_parameter_error (α : ℚ)
    (hα₀ : 0 ≤ α) (hα : α < 1)
    (herror : (finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) : ℚ) ≤ α) :
    (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
      nongenericFraction F (Fintype.card J) ≤ α / (1 - α) := by
  classical
  let V := J → ZMod 2
  let W := Fin 3 → F
  let A := V →ₗ[ZMod 2] W
  let P : A → Prop := fun g => Function.Injective g
  let Q : A → Prop := fun g => IsGeneric g.range
  let : Fintype A := Fintype.ofEquiv ((Fin 3 × J) → F) parameterMapEquiv
  let : Fintype (Submodule (ZMod 2) W) :=
    Fintype.ofInjective (fun S : Submodule (ZMod 2) W => (S : Set W)) SetLike.coe_injective
  let : Fintype (W ≃ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  let : Fintype (UniformSubspaces.Injection (ZMod 2) V W) :=
    inferInstanceAs (Fintype {g : A // Function.Injective g})
  let : Fintype (RankSpace (ZMod 2) W (finrank (ZMod 2) V)) :=
    inferInstanceAs (Fintype {S : Submodule (ZMod 2) W // finrank (ZMod 2) S = finrank (ZMod 2) V})
  have hcount : (Nat.card {g : A // ¬(P g ∧ Q g)} : ℚ) / Nat.card A ≤ α := by
    rw [parameterMap_event_probability (fun g : A => ¬(P g ∧ Q g))] at herror
    exact herror
  have hc := conditioning_counts P Q α hα hcount
  obtain ⟨g, hgP, hgQ⟩ := hc.1
  let J₀ : UniformSubspaces.Injection (ZMod 2) V W := ⟨g, hgP⟩
  have hdim : finrank (ZMod 2) V = Fintype.card J :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hfrac := UniformSubspaces.bad_subspace_bound J₀
    (fun S : RankSpace (ZMod 2) W (finrank (ZMod 2) V) => ¬IsGeneric S.1)
    α α hα₀ hα hc.2.1 (by
      rw [← Nat.card_eq_fintype_card]
      exact hc.2.2)
  refine ⟨?_, ?_⟩
  · refine ⟨⟨g.range, ?_⟩, hgQ⟩
    simpa only [V, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_of_inj hgP)
  · rw [← Nat.card_eq_fintype_card] at hfrac
    change nongenericFraction F (finrank (ZMod 2) V) ≤ α / (1 - α) at hfrac
    simpa only [hdim] using hfrac

/-- The exact v2 genericity statement with a positive numerator fixed before
the extension field.  The property quantifies over every binary linear lift. -/
theorem exists_generic_subspace_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        (D : ℚ) / Fintype.card F < 1 →
        (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
          nongenericFraction F (Fintype.card J) ≤
            ((D : ℚ) / Fintype.card F) / (1 - (D : ℚ) / Fintype.card F) := by
  obtain ⟨D, hD, hbound⟩ := exists_genericity_error_numerator J
  refine ⟨D, hD, ?_⟩
  intro F _ _ _ _ hsmall
  apply generic_subspace_and_probability_of_parameter_error ((D : ℚ) / Fintype.card F)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsmall
  exact_mod_cast hbound F

/-- A convenient numerical threshold for choosing one field for finitely
many ranks: `α ≤ min(1/2, ε/2)` is sufficient. -/
theorem conditional_error_le_of_small (α ε : ℚ) (hα : 0 ≤ α)
    (hhalf : α ≤ 1 / 2) (hε : α ≤ ε / 2) : α / (1 - α) ≤ ε := by
  have hd : 0 < 1 - α := by linarith
  apply (div_le_iff₀ hd).mpr
  have hε₀ : 0 ≤ ε := by linarith
  have hprod : 0 ≤ ε * (1 / 2 - α) := mul_nonneg hε₀ (by linarith)
  nlinarith

end UniqueGamesTheorem.Quadratic

end

end

end OAI
