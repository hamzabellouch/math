import OAI.NumberTheory.TotientAsymptotic.Normalization

namespace OAI

/-! An actual vanishing envelope for an iterated eventual error bound. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- Turn an iterated small-error estimate into one envelope valid at every
fixed index. The infimum is taken over eventual normalized upper bounds;
its approximation needs no attainment or uniform threshold in the index. -/
theorem ppt_iterated_error_envelope (E : ℕ→ℝ→ℝ) (S : ℝ→ℝ)
    (hS : ∀ᶠ x : ℝ in atTop, 0 < S x)
    (hbound : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ P : ℕ, E P x ≤ C*S x)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop,
      ∀ᶠ x : ℝ in atTop, E P x ≤ ε*S x) :
    ∃ δ : ℕ→ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ P : ℕ, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℝ in atTop, E P x ≤ (δ P+ε)*S x := by
  obtain ⟨C,hC⟩:=hbound
  let U : ℕ→Set ℝ := fun P => {b | 0 ≤ b ∧ ∀ᶠ x : ℝ in atTop,E P x ≤ b*S x}
  have hne (P : ℕ) : (U P).Nonempty := by
    refine ⟨max C 0,le_max_right _ _,?_⟩
    filter_upwards [hC,hS] with x hx hSx
    exact (hx P).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hSx.le)
  have hbdd (P : ℕ) : BddBelow (U P) := ⟨0,fun _ hb=>hb.1⟩
  let δ : ℕ→ℝ := fun P => sInf (U P)
  have hnonneg (P : ℕ) : 0 ≤ δ P := le_csInf (hne P) (fun _ hb=>hb.1)
  refine ⟨δ,?_,?_⟩
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun P=>ha.trans_le (hnonneg P))
    · intro b hb
      filter_upwards [hsmall (b/2) (half_pos hb)] with P hP
      have hbU : b/2∈U P := ⟨(half_pos hb).le,hP⟩
      have hh : δ P ≤ b/2 := csInf_le (hbdd P) hbU
      linarith only [hh,hb]
  · intro P ε hε
    obtain ⟨b,hb,hlt⟩:=exists_lt_of_csInf_lt (hne P)
      (show sInf (U P) < δ P+ε by change δ P < δ P+ε; linarith only [hε])
    filter_upwards [hb.2,hS] with x hx hSx
    exact hx.trans (mul_le_mul_of_nonneg_right hlt.le hSx.le)

end TotientAsymptotic

end

end OAI
