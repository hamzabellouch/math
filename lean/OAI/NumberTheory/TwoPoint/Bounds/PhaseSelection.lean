import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI

/-! A numerical subfamily can retain complex mass without cancellation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

private lemma coordinate_mass_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (φ : ℂ →+ ℝ) (hφ : ∀ x, |φ x| ≤ ‖x‖) :
    (∑ i ∈ s, |φ (z i)|) ≤
      ‖∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), z i‖ +
        ‖∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), z i‖ := by
  have he : (∑ i ∈ s, |φ (z i)|) =
      (∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), φ (z i)) -
        ∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), φ (z i) := by
    simp only [sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ φ (z i)
    · simp [hi, abs_of_nonneg hi]
    · simp [hi, abs_of_neg (lt_of_not_ge hi)]
  rw [he, ← map_sum, ← map_sum]
  have hp := hφ (∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), z i)
  have hn := hφ (∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), z i)
  linarith [le_abs_self (φ (∑ i ∈ s.filter (fun i => 0 ≤ φ (z i)), z i)),
    neg_le_abs (φ (∑ i ∈ s.filter (fun i => ¬0 ≤ φ (z i)), z i))]

/-- Four half-plane selections suffice. The selected family depends only
on the numerical coefficients, so it can be used as graph eligibility. -/
theorem exists_subfamily_complex_mass {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∃ t ⊆ s, (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ t, z i‖ := by
  let rp := s.filter (fun i => 0 ≤ (z i).re)
  let rn := s.filter (fun i => ¬0 ≤ (z i).re)
  let ip := s.filter (fun i => 0 ≤ (z i).im)
  let inn := s.filter (fun i => ¬0 ≤ (z i).im)
  have hr := coordinate_mass_le s z Complex.reAddGroupHom Complex.abs_re_le_norm
  have hi := coordinate_mass_le s z Complex.imAddGroupHom Complex.abs_im_le_norm
  change (∑ i ∈ s, |(z i).re|) ≤ ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ at hr
  change (∑ i ∈ s, |(z i).im|) ≤ ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ at hi
  have ht : (∑ i ∈ s, ‖z i‖) ≤
      ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ + ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    have h := sum_le_sum (fun i (_ : i ∈ s) => Complex.norm_le_abs_re_add_abs_im (z i))
    rw [sum_add_distrib] at h
    dsimp only [rp, rn, ip, inn]
    linarith
  by_contra h
  push Not at h
  have h₁ := h rp (filter_subset _ _)
  have h₂ := h rn (filter_subset _ _)
  have h₃ := h ip (filter_subset _ _)
  have h₄ := h inn (filter_subset _ _)
  linarith

end TwoPointCorrelations

end OAI
