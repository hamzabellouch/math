import Mathlib
import OAI.Probability.Ballisticity.Estimates.OccupationParameters

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

theorem occupation_cutoff_escape {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {t : ℝ}
    (D : OccupationData ν e f t) (A : ℝ) (r : ℕ → ℝ)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) :
    ∃ (b : ℕ → ℝ) (K : ℕ → ℕ),
      (∀ i, D.u₀ ≤ b i) ∧ Tendsto (fun i => b i/r i) atTop (𝓝 0) ∧
      (∀ i u, b i ≤ u → u ≤ A*r i →
        fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) u*
          (independentConditionedPairLaw ν (realPosition (step e))).real
            {P | D.l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ D.ε) ∧
      ∀ i, 0 < K i ∧ (K i:ℝ) ≤ D.C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) (b i) ∧
        ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
          D.q ≤ (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
            (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
              (signedHeight e x+K i) {uv | 2*b i ≤ |signedCoordinate f uv.1-signedCoordinate f uv.2|}) := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  obtain ⟨b,hb,hgood,hb0⟩ := gaussian_bad_cutoff μ S (measurable_commonIncrementProcess ℓ f 0)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr
    (A := A) D.u₀_pos D.l_pos D.ε_pos
  have hesc (i : ℕ) : LowerEscape ν e f (b i) D.C D.q := by
    apply D.escape
    rcases (hb i).2 with he | ⟨u,hu,_,hbad,he⟩
    · exact Or.inl he
    · exact Or.inr ⟨u,hu,hbad.le,he⟩
  choose K hK hKn hKprob using hesc
  exact ⟨b,K,fun i => (hb i).1,hb0,hgood,fun i => ⟨hK i,hKn i,hKprob i⟩⟩

end DirectionalTransience

end

end

end OAI
