import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshBudgetEvent

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma fluctuationRadius_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (s : ℝ) : 0<fluctuationRadius μ S s := by
  unfold fluctuationRadius
  split
  · rename_i h
    exact h.choose_spec.1
  · norm_num

lemma seedSeparatedRaw_mass_antitone {d k : ℕ} (e f : Direction d) (H : ℕ)
    {G F : ℝ} (hGF : G≤F) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    seedSeparatedRaw e f H F π ω Set.univ ≤ seedSeparatedRaw e f H G π ω Set.univ := by
  rw [seedSeparatedRaw_univ,seedSeparatedRaw_univ]
  exact measure_mono (fun x hx => tupleSeparated_mono f hGF x hx)

theorem adapted_separated_seeds_capped {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ : ℝ, 0<C ∧ 0<c₀ ∧ c₀≤1 ∧ 0<g₀ ∧ ∃ H₀ : ℕ, ∀ H≥H₀,
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ A : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A →
        environmentLaw ν (A∩{ω | seedSeparatedRaw e f H
          (c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) ((H:ℝ)/C))
          (π ω).val ω Set.univ<ENNReal.ofReal g₀})≤ENNReal.ofReal p*environmentLaw ν A := by
  obtain ⟨C,c,g,hC,hc,hg,H₀,hh⟩ := adapted_separated_seeds ν hue e f hef htrans k hk p hp
  refine ⟨C,min c 1,g,hC,lt_min hc (by norm_num),min_le_right _ _,hg,H₀,?_⟩
  intro H hH a π hπ A hA
  apply le_trans (measure_mono ?_) (hh H hH a π hπ A hA)
  rintro ω ⟨hA,hfail⟩
  refine ⟨hA,?_⟩
  change seedSeparatedRaw e f H _ (π ω).val ω Set.univ < _
  exact lt_of_le_of_lt (seedSeparatedRaw_mass_antitone e f H
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (fluctuationRadius_pos _ _ _).le) _ _) hfail

end DirectionalTransience

end

end OAI
