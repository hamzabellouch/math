import OAI.Analysis.KadisonKastler.WeakCPDescent

namespace OAI

/-! # Directed finite tests on arbitrary Hilbert spaces

Local approximations need not agree on overlapping tests. An ultrafilter
extending the directed test filter produces the coefficient limits needed
by the UCP criterion.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

local instance testFactorOrder (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _
local instance testFactorStarOrder (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _

/-- The finite coefficient condition supplied by separable restrictions in
the manuscript. It asserts no global range inclusion for a local conjugacy. -/
def FiniteCoefficientConjugations (M N : VonNeumannAlgebra H) (a : ℝ) : Prop :=
  ∀ (E : Finset (Algebra M)) (V : Finset H) (k : ℕ),
    ∃ U : unitary (H →L[ℂ] H), ‖(U : H →L[ℂ] H) - 1‖ ≤ a ∧
      ∀ x ∈ E, ∃ b : Algebra N, ∀ ξ ∈ V, ∀ η ∈ V,
        ‖inner ℂ η (((b : H →L[ℂ] H) -
          (U : H →L[ℂ] H) * (x : H →L[ℂ] H) * star (U : H →L[ℂ] H)) ξ)‖ <
            1 / (k + 1 : ℝ)

/-- Assemble all finite tests, take the UCP limit, and apply the concrete
correction theorem on the original ambient Hilbert space. -/
theorem concrete_unitary_of_finite_coefficient_tests
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    {a g : ℝ} (ha : 0 ≤ a) (htests : FiniteCoefficientConjugations M N a)
    (hsmall : 2 * a < 1 / 1000) (hge : g + 2 * a < 1)
    (hgap : kkDistance M N < g) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * a := by
  classical
  let I := Finset (Algebra M) × Finset H × ℕ
  choose U hU hb using (fun i : I => htests i.1 i.2.1 i.2.2)
  let b (i : I) (x : Algebra M) : Algebra N :=
    if hx : x ∈ i.1 then Classical.choose (hb i x hx) else 0
  let ω : Ultrafilter I := Ultrafilter.of atTop
  have hω : (ω : Filter I) ≤ atTop := Ultrafilter.of_le atTop
  apply concrete_unitary_of_weak_conjugations hCorrection hCommutant ω U ha hU b
    ?_ hsmall hge hgap
  intro x ξ η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hevent : ∀ᶠ i : I in atTop,
      ‖inner ℂ η (((b i x : H →L[ℂ] H) -
        (U i : H →L[ℂ] H) * (x : H →L[ℂ] H) * star (U i : H →L[ℂ] H)) ξ)‖ < ε := by
    filter_upwards [eventually_ge_atTop (({x} : Finset (Algebra M)),
      ({ξ, η} : Finset H), k)] with i hi
    have hx : x ∈ i.1 := hi.1 (by simp)
    have hξ : ξ ∈ i.2.1 := hi.2.1 (by simp)
    have hη : η ∈ i.2.1 := hi.2.1 (by simp)
    have hbi := Classical.choose_spec (hb i x hx) ξ hξ η hη
    have hbound : 1 / (i.2.2 + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hi.2.2 1
    simpa only [b, dite_eq_left hx] using (hbi.trans_le hbound).trans hk
  exact (hevent.filter_mono hω).mono fun i hi => by simpa only [dist_zero_right] using hi

end

end KadisonKastler

end OAI
