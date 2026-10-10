import OAI.MeasureTheory.Falconer.Incidence.FrozenHeavyCover
import OAI.MeasureTheory.Falconer.Estimates.TroublesomePair

namespace OAI

/-! # Covers of the measurable troublesome-pair relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem troublesome_pair_covers (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ]
    (c : Space (n+1)) {r D δ C B F : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hF : 0 < F)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ A : Space (n+1) → Finset (Space (n+1)),
      (∀ z p, (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F) →
        ∃ a ∈ A p, ‖perpendicularPart (NormedSpace.normalize (c-p)) (z-a)‖ ≤
          ((n+1:ℕ):ℝ)*δ) ∧
      ∀ p, ((A p).card:ℝ) ≤ ((2*L+1)^(n+1):ℕ)/F := by
  classical
  have hall (p : Space (n+1)) : ∃ P : Finset (Space (n+1)),
      (∀ z, (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F) →
        ∃ a ∈ P, ‖perpendicularPart (NormedSpace.normalize (c-p)) (z-a)‖ ≤
          ((n+1:ℕ):ℝ)*δ) ∧ (P.card:ℝ) ≤ ((2*L+1)^(n+1):ℕ)/F := by
    by_cases hp : ∃ z, (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F)
    · obtain ⟨z,hz⟩ := hp
      obtain ⟨P,hP,hcard⟩ := frozen_heavy_tube_cover μ p c hr hz.1 hδ hfreeze hsource
        {z | (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F)}
        (fun z hz => ⟨hz.2.1,hz.2.2.1,hz.2.2.2.1⟩) (ENNReal.ofReal F)
        (fun z hz => hz.2.2.2.2.le) L hL
      refine ⟨P,hP,?_⟩
      apply (le_div_iff₀ hF).mpr
      have hfinite : ((((2*L+1)^(n+1):ℕ):ℝ≥0∞)*μ univ) ≠ ∞ := by
        rw [measure_univ,mul_one]
        exact ENNReal.natCast_ne_top _
      have hc := ENNReal.toReal_mono hfinite hcard
      simpa only [measure_univ,mul_one,ENNReal.toReal_mul,ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hF.le] using hc
    · refine ⟨∅,fun z hz => False.elim (hp ⟨z,hz⟩),?_⟩
      simp only [Finset.card_empty,Nat.cast_zero]
      exact div_nonneg (Nat.cast_nonneg _) hF.le
  choose A hA using hall
  exact ⟨A,fun z p hz => (hA p).1 z hz,fun p => (hA p).2⟩

end Falconer

end OAI
