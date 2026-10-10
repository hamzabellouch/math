import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The surjectivity step in the completely positive criterion

The first paragraph of Proposition 2.4 in the manuscript proves surjectivity
from a reverse unit-ball gap strictly below one. The normed-space argument
uses Riesz's lemma and requires no operator-algebra perturbation theorem.
-/

namespace KadisonKastler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A closed complex subspace that uniformly approximates the unit ball to
an error strictly below one must be the whole space. -/
theorem eq_top_of_unitBall_approx (V : Submodule ℂ E)
    (hclosed : IsClosed (V : Set E)) {c : ℝ} (hc : c < 1)
    (happrox : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ V, ‖x - y‖ ≤ c) : V = ⊤ := by
  by_contra hproper
  have hout : ∃ x : E, x ∉ V := by
    by_contra h
    push Not at h
    exact hproper (Submodule.eq_top_iff'.mpr h)
  obtain ⟨x, _, hx, hsep⟩ :=
    riesz_lemma_of_lt_one hclosed hout (show (c + 1) / 2 < 1 by linarith)
  obtain ⟨y, hy, hxy⟩ := happrox x hx.le
  have := hsep y hy
  linarith

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- The reverse-gap argument for a continuous linear map with closed range.
The domain and codomain may have different norms and need not be algebras. -/
theorem surjective_of_closed_range_unitBall_approx (F : P →L[ℂ] Q)
    (hclosed : IsClosed (Set.range F)) {c : ℝ} (hc : c < 1)
    (happrox : ∀ y : Q, ‖y‖ ≤ 1 → ∃ x : P, ‖y - F x‖ ≤ c) :
    Function.Surjective F := by
  have htop : F.toLinearMap.range = ⊤ :=
    eq_top_of_unitBall_approx F.toLinearMap.range hclosed hc (by
      intro y hy
      obtain ⟨x, hx⟩ := happrox y hy
      exact ⟨F x, ⟨x, rfl⟩, hx⟩)
  exact LinearMap.range_eq_top.mp htop

/-- The range argument used in the manuscript's UCP criterion. Here `ρ`
and `ι` are isometric embeddings into one ambient operator space. The
reverse gap is expressed with arbitrary positive slack, so no nearest
point or compactness hypothesis is hidden in the statement. -/
theorem bijective_of_close_isometry_and_reverse_gap [CompleteSpace P]
    (ρ : P →L[ℂ] E) (ι : Q →L[ℂ] E) (F : P →L[ℂ] Q)
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖) (hι : ∀ y, ‖ι y‖ = ‖y‖)
    {e g : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hge : g + e < 1)
    (hclose : ∀ x, ‖ι (F x) - ρ x‖ ≤ e * ‖x‖)
    (hgap : ∀ y : Q, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : P, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    Function.Bijective F := by
  have hpos : 0 < 1 - e := sub_pos.mpr he1
  have hlower (x : P) : (1 - e) * ‖x‖ ≤ ‖F x‖ := by
    have ht := norm_add_le (ρ x - ι (F x)) (ι (F x))
    have hc := hclose x
    rw [norm_sub_rev] at hc
    rw [sub_add_cancel, hρ, hι] at ht
    nlinarith
  have hanti : AntilipschitzWith ⟨(1 - e)⁻¹, inv_nonneg.mpr hpos.le⟩ F := by
    apply F.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ (1 - e)⁻¹ * ‖F x‖
    exact (le_inv_mul_iff₀ hpos).mpr (hlower x)
  refine ⟨hanti.injective, ?_⟩
  apply surjective_of_closed_range_unitBall_approx F
    (hanti.isClosed_range F.uniformContinuous)
    (c := (g + 1 - e) / 2 + e) (by linarith)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hgap y hy ((g + 1 - e) / 2) (by linarith)
  refine ⟨x, ?_⟩
  calc
    ‖y - F x‖ = ‖ι y - ι (F x)‖ := by rw [← map_sub, hι]
    _ ≤ ‖ι y - ρ x‖ + ‖ρ x - ι (F x)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (g + 1 - e) / 2 + e := by
      have hc := hclose x
      rw [norm_sub_rev] at hc
      have hehx : e * ‖x‖ ≤ e := by nlinarith
      linarith

end KadisonKastler

end OAI
