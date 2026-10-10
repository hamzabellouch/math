import OAI.Combinatorics.Progressions.Estimates.BooleanMinorDimension

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def insertBlockParameters {B O F α : Type*} (block : O → B)
    (outside : BlockParameter B F α → ℝ) (x : BlockParameter O F α → ℝ)
    (z : BlockParameter B F α) : ℝ :=
  Function.extend block (fun o vr => x (o, vr)) (fun b vr => outside (b, vr)) z.1 z.2

theorem restrict_insertBlockParameters {B O F α : Type*}
    (block : O → B) (hblock : Function.Injective block)
    (outside : BlockParameter B F α → ℝ) (x : BlockParameter O F α → ℝ) :
    restrictBlockParameters block (insertBlockParameters block outside x) = x := by
  funext z
  simp only [restrictBlockParameters, insertBlockParameters, hblock.extend_apply]

theorem booleanSelectedMinor_insert_eval {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (hblock : Function.Injective block)
    (v : F) (r : O → Option α) (outside : BlockParameter B F α → ℝ)
    (x : BlockParameter O F α → ℝ) :
    (booleanSelectedMinor c sets block v r).map
      (MvPolynomial.eval (insertBlockParameters block outside x)) =
      (booleanSelectedMinor (c ∘ block) sets id v r).map (MvPolynomial.eval x) := by
  rw [booleanSelectedMinor_restrict_eval, restrict_insertBlockParameters block hblock]

theorem exists_allocated_boolean_minor_sublevel_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c (block o)|) :
    ∃ r : O → Option α, ∀ (outside : BlockParameter B (Fin h) α → ℝ)
      (d : ℕ), 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (Ω : Set (Fin N → ℝ)), MeasurableSet Ω →
      ∀ (R u : ℝ), 1 ≤ R → (∀ x ∈ Ω, ∀ j, |x j| ≤ R) →
      ∀ (ρ : (Fin N → ℝ) → ℝ), IntegrableOn ρ Ω →
      ∀ (H : ℝ), 0 ≤ H → (∀ x ∈ Ω, ρ x ≤ H) → 0 < u →
      (∫ x in Ω ∩ {x | |((booleanSelectedMinor c sets block (⟨0, hh⟩ : Fin h) r).map
        (MvPolynomial.eval (insertBlockParameters block outside (x ∘ e)))).det| ≤ u}, ρ x) ≤
        H * (R ^ N * multivariateSublevelConstant N d) *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨r, hr⟩ := exists_weighted_boolean_minor_sublevel_bound
    (c ∘ block) sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro outside d hd hdeg Ω hΩm R u hR hΩ ρ hρ H hH hbound hu
  simp only [booleanSelectedMinor_insert_eval c sets block hblock]
  exact hr d hd hdeg Ω hΩm R u hR hΩ ρ hρ H hH hbound hu

end Erdos3

end

end OAI
