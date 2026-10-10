import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortFamily
import OAI.NumberTheory.CubicMoment.Estimates.AllShortNeighborhoods

namespace OAI

/-! The exceptional-moment machinery applied to constructed smooth factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem all_short_smooth_cubic_neighborhood {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y N : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := all_short_cubic_neighborhood (ι := ι) hδ hC
  refine ⟨κ,hκ,hκhi,ε,hε,T,?_⟩
  intro F Y N X A q η W t P hY hNlo hNhi hA hX hq hW hcut hshort hlo hhi hP
  let K := shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW
  have h := hbound K 0 Y N P hY hNlo hNhi hshort hlo hhi hP
  simpa only [K,smoothShortFamily_cubicValue F X A q η W t hA hX hq hW hcut] using h

theorem all_short_smooth_mixed_neighborhood (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/3 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+κ) ∧ norm p.2 ≤ Y^(1/3+κ)) →
      (∑ p ∈ P, ‖∏ i, primaryShortSmoothSum (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := all_short_mixed_neighborhood (ι := ι) hHuxley hδ hC
  refine ⟨κ,hκ,hκhi,ε,hε,T,?_⟩
  intro F Y X A q η W t P hY hA hX hq hW hcut hshort hlo hhi hP
  let K := shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW
  have h := hbound K 0 Y P hY hshort hlo hhi hP
  simpa only [K,smoothShortFamily_mixedValue F X A q η W t hA hX hq hW hcut] using h


end CubicFirstMoment

end

end OAI
