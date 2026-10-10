import OAI.Analysis.KadisonSimilarity.Tensor.EndpointPairings

namespace OAI

/-!
# Stable coefficients on growing matrix stages

Finite Schur--Weyl spanning, compatibility of normalized contractions, and the
actual matrix-unit endpoint estimate produce one stable coefficient family.
The small-cycle coefficients are proved zero; neither stability nor those
zeros are added as assumptions.
-/

noncomputable section
namespace KadisonSimilarity

open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Coefficients chosen by finite Schur--Weyl spanning agree at every stage
once their normalized contractions restrict to the common initial stage. -/
theorem exists_stable_matrix_expansion
    (spanning : ∀ s, SchurWeylMultilinearSpanning ι (A s))
    (F : ∀ s, MultilinearMap ℂ (fun _ : ι => Matrix (A s) (A s) ℂ) ℂ)
    (hF : ∀ s, UnitaryConjugationInvariant (F s))
    (embed : ∀ s, Matrix (A 0) (A 0) ℂ → Matrix (A s) (A s) ℂ)
    (hform : ∀ s v, F s (fun i => embed s (v i)) = F 0 v)
    (hcontraction : ∀ s (π : Equiv.Perm ι) (v : ι → Matrix (A 0) (A 0) ℂ),
      normalizedPermutationContraction π (fun i => embed s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ι → A 0) (hlabels : Function.Injective labels) :
    ∃ c : Equiv.Perm ι → ℂ, ∀ s v,
      F s v = ∑ π, c π * normalizedPermutationContraction π v := by
  choose coeff hcoeff using fun s => spanning s (F s) (hF s)
  have hstable (s : ℕ) : coeff s = coeff 0 := by
    apply normalizedPermutationContraction_coefficients_unique labels hlabels
    intro v
    calc
      (∑ π, coeff s π * normalizedPermutationContraction π v) =
          ∑ π, coeff s π * normalizedPermutationContraction π (fun i => embed s (v i)) := by
        simp only [hcontraction]
      _ = F s (fun i => embed s (v i)) := (hcoeff s _).symm
      _ = F 0 v := hform s v
      _ = ∑ π, coeff 0 π * normalizedPermutationContraction π v := hcoeff 0 v
  refine ⟨coeff 0, fun s v => ?_⟩
  simpa only [hstable s] using hcoeff s v

/-- The endpoint test eliminates every stable coefficient below the cycle
threshold. The input bound is on the original stage form at explicit matrix
units, not on already-isolated coefficients. -/
theorem stable_matrix_coefficient_zero
    (F : ∀ s, MultilinearMap ℂ (fun _ : ι => Matrix (A s) (A s) ℂ) ℂ)
    (c : Equiv.Perm ι → ℂ)
    (hexp : ∀ s v, F s v = ∑ π, c π * normalizedPermutationContraction π v)
    (labels : ∀ s, ι → A s) (hlabels : ∀ s, Function.Injective (labels s))
    (hsize : Tendsto (fun s => (Fintype.card (A s) : ℝ)) atTop atTop)
    (tailDegree : ℕ) (C : ℝ)
    (hbound : ∀ s π, ‖F s (permutationTest (labels s) π)‖ ≤
      C * (Fintype.card (A s) : ℝ) ^ (-1 - (tailDegree : ℝ) / 2))
    (π : Equiv.Perm ι)
    (hfew : (permutationCycleCount π : ℝ) < 1 + (tailDegree : ℝ) / 2) : c π = 0 := by
  apply cycle_coefficient_zero (fun s => (Fintype.card (A s) : ℝ))
    (fun s => by exact_mod_cast Fintype.card_pos (α := A s)) hsize
    tailDegree 0 (permutationCycleCount π) (c π) C (by simpa using hfew)
  intro s
  have hb := hbound s π
  rw [hexp s (permutationTest (labels s) π),
    norm_normalizedPermutationContraction_sum_test (labels s) (hlabels s)] at hb
  simpa using hb

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Assemble finite Schur--Weyl spanning, coefficient stability, endpoint
matrix-unit estimates, and the proved pair-trace factorization. -/
theorem exists_stable_tail_pairing_expansion
    (rank : T → ℕ) (hrank : Function.Injective rank)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option T) (A s))
    (F : ∀ s, MultilinearMap ℂ (fun _ : Option T => Matrix (A s) (A s) ℂ) ℂ)
    (hF : ∀ s, UnitaryConjugationInvariant (F s))
    (embed : ∀ s, Matrix (A 0) (A 0) ℂ → Matrix (A s) (A s) ℂ)
    (hform : ∀ s v, F s (fun i => embed s (v i)) = F 0 v)
    (hcontraction : ∀ s (π : Equiv.Perm (Option T))
      (v : Option T → Matrix (A 0) (A 0) ℂ),
      normalizedPermutationContraction π (fun i => embed s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option T → A s) (hlabels : ∀ s, Function.Injective (labels s))
    (hsize : Tendsto (fun s => (Fintype.card (A s) : ℝ)) atTop atTop)
    (C : ℝ)
    (hbound : ∀ s π, ‖F s (permutationTest (labels s) π)‖ ≤
      C * (Fintype.card (A s) : ℝ) ^ (-1 - (Fintype.card T : ℝ) / 2)) :
    ∃ c : Equiv.Perm (Option T) → ℂ,
      (∀ s v, F s v = ∑ π, c π * normalizedPermutationContraction π v) ∧
      (∀ π, 2 * permutationCycleCount π < Fintype.card (Option T) + 1 → c π = 0) ∧
      (∀ s v, (∀ i : T, Matrix.trace (v (some i)) = 0) →
        F s v = ((Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v none)) *
          ∑ P : PerfectMatching T, c (endpointMatching P) *
            ∏ i : MatchingRepresentatives rank P,
              (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i)))) := by
  obtain ⟨c, hc⟩ := exists_stable_matrix_expansion spanning F hF embed hform hcontraction
    (labels 0) (hlabels 0)
  have hzero (π : Equiv.Perm (Option T))
      (hπ : 2 * permutationCycleCount π < Fintype.card (Option T) + 1) : c π = 0 := by
    apply stable_matrix_coefficient_zero F c hc labels hlabels hsize (Fintype.card T) C hbound π
    have hn : 2 * permutationCycleCount π < Fintype.card T + 2 := by
      simpa only [Fintype.card_option, Nat.add_assoc, one_add_one_eq_two] using hπ
    have hr : (2 : ℝ) * permutationCycleCount π < (Fintype.card T : ℝ) + 2 := by
      exact_mod_cast hn
    linarith
  refine ⟨c, hc, hzero, ?_⟩
  intro s v hv
  rw [hc s v]
  exact invariant_expansion_tail_pairings rank hrank v hv c hzero

end KadisonSimilarity

end

end OAI
