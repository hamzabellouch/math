import OAI.Computability.UniqueGames.Gadgets.ActualGadgetLemmas
import OAI.Computability.UniqueGames.Gadgets.BaseConstruction
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Gadget

open Quadratic QuadraticStageNoise
open UniqueGamesTheorem.Integration.BinaryLinear
open scoped Classical

noncomputable section

/-- Actual finite gadget data, with a rank threshold independent of the final
logical dimension and an arbitrarily small nonlinear change probability. -/
theorem exists_actual_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ g : UniqueGamesTheorem.Gadget.ActualGadget.Data (Vector ℓ),
        UniqueGamesTheorem.Gadget.ActualGadget.Satisfies g p (7 / 8) r := by
  obtain ⟨d, _hd, n, herror, hdetect⟩ := BaseConstruction.exists_base p hp
  let B := Vec (BinaryField d)
  let s := quotientStage (F := BinaryField d) n
  let : Fintype B := Fintype.ofFinite _
  let : FiniteDimensional (ZMod 2) B := Module.Finite.of_finite
  let : Fintype s.Input := Fintype.ofFinite _
  let : Fintype s.Noise := Fintype.ofFinite _
  let i : B →ₗ[ZMod 2] s.Input := s.embed
  let r := Module.finrank (ZMod 2) B + 2
  refine ⟨r, by omega, ?_⟩
  intro ℓ hℓ
  have hdim : Module.finrank (ZMod 2) B ≤
      Module.finrank (ZMod 2) (Vector ℓ) := by
    rw [finrank_vector]
    omega
  let b₀ : B := fun _ => 1
  have hb₀ : b₀ ≠ 0 := by
    intro h
    have hzero := congrFun h (0 : Fin 3)
    exact one_ne_zero hzero
  have hequiv : ∀ u (b : B), s.output (u + i b) = s.output u + b := by
    intro u b
    exact s.equivariant u b
  have hc : Enlargement.probability (fun z : s.Input × s.Noise =>
      s.output (z.1 + s.noise z.2) ≠ s.output z.1) ≤ p := by
    rw [← StageData.error_eq_count_probability s]
    exact herror
  have hb : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : s.Input →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
      (1 / 4 : ℚ) ≤ Enlargement.probability (fun t => U (s.noise t) ≠ 0) := by
    intro E _ _ U hU
    have h := hdetect E U hU
    rw [StageNoiseRecurrence.average_eq_expect] at h
    refine h.trans_eq ?_
    rw [StageData.count_probability_eq_expect]
    apply Finset.expect_congr rfl
    intro t _
    by_cases ht : U (s.noise t) = 0
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_true_eq_false, ite_false]
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_false_eq_true, ite_true]
  exact EnlargementEndpoint.exists_data (B := B) (K := Vector ℓ)
    i s.embed_injective s.output hequiv s.noise hdim b₀ hb₀ p hc hb

theorem exists_split_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ d : ℕ, ∃ g : UniqueGamesTheorem.Reduction.ActualSource.SplitGadget ℓ d,
        g.stabilityError ≤ p ∧
        ∀ (P : Type) [AddCommGroup P] [Module F2 P]
          (S : UniqueGamesTheorem.Reduction.ActualSource.Ambient ℓ d →ₗ[F2] P),
          r ≤ Module.finrank F2
            (S.comp (UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding ℓ d)).range →
          UniqueGamesTheorem.Integration.SplitGadget.kernelProbability g S ≤ 7 / 8 := by
  obtain ⟨r, hr, hg⟩ := exists_actual_gadget p hp
  refine ⟨r, hr, ?_⟩
  intro ℓ hℓ
  obtain ⟨g, hgood⟩ := hg ℓ hℓ
  exact UniqueGamesTheorem.Integration.SplitGadget.exists_split_gadget_general g hgood

end

end UniqueGamesTheorem.Gadget

end

end OAI
