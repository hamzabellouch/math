import OAI.NumberTheory.Ostmann.Tree.PairCoefficientMeans

namespace OAI

/-! # The two quantitative mean bounds for the concrete same-pair majorant -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance samePairMeanBoundsFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem concrete_samePairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : ∀ χ a, ‖additiveFourier (characterTwist g χ) a‖ ≤ ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ,
      samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment g) ρ y) /
        (Fintype.card (ZMod p)ˣ : ℝ) ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 := by
  have h := samePairMajorant_mean_le (fieldPairCoefficientMoment g) (fieldPairMoment g)
    (fun _ _ => sq_nonneg _) (fieldPairMoment_nonneg g)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 * ε ^ 2)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) (by positivity)
    (fun χ => fieldPairCoefficientMoment_mean_le g hg χ ε hε (hflat χ) henergy)
    (fieldPairMoment_mean_le g hg henergy) ρ
  convert h using 1
  ring

theorem concrete_samePairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment g) ρ y) /
        (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  have h := samePairMajorant_total_mean_le (fieldPairCoefficientMoment g) (fieldPairMoment g)
    (fun _ _ => sq_nonneg _) (fieldPairMoment_nonneg g)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) (sq_nonneg _)
    (fieldPairCoefficientMoment_total_mean_le g hg henergy)
    (fieldPairMoment_mean_le g hg henergy)
  convert h using 1
  ring

end Ostmann

end OAI
