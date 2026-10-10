import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovRealMoment

namespace OAI

/-! The zero-representation inequality used for the translated complete
systems: any prescribed difference has at most as many representations
as zero. This is Proposition ZRD in Ford's mean-value argument. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped ComplexConjugate

noncomputable def halaszRepresentationCount {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) : ℕ := by
  classical
  exact (univ.filter (fun xy : ι × ι => f xy.1-f xy.2=w)).card

noncomputable def halaszRepresentationSum {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∑ x, halaszVinogradovCharacter (f x) α

noncomputable def halaszRepresentationWeight {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  halaszRepresentationSum f α * conj (halaszRepresentationSum f α) *
    halaszVinogradovCharacter (-w) α

theorem halasz_representation_integral {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) :
    (∫ α, halaszRepresentationWeight f w α ∂halaszVinogradovHaar k) =
      (halaszRepresentationCount f w:ℂ) := by
  classical
  have hi (x y : ι) : Integrable (fun α =>
      (halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (f y) α)) *
        halaszVinogradovCharacter (-w) α) (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  unfold halaszRepresentationWeight halaszRepresentationSum
  simp_rw [map_sum,sum_mul,mul_sum,sum_mul]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y),← halasz_vinogradov_character_neg,
    ← halasz_vinogradov_character_add,halasz_vinogradov_character_integral,
    ← sub_eq_add_neg,sub_eq_zero]
  rw [← Fintype.sum_prod_type']
  simp only [sum_boole,halaszRepresentationCount]

lemma halasz_representation_weight_norm {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    ‖halaszRepresentationWeight f w α‖ = ‖halaszRepresentationSum f α‖^2 := by
  simp only [halaszRepresentationWeight,norm_mul,Complex.norm_conj,
    halasz_vinogradov_character_norm,mul_one,pow_two]

lemma halasz_representation_energy {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) :
    (∫ α, ‖halaszRepresentationSum f α‖^2 ∂halaszVinogradovHaar k) =
      (halaszRepresentationCount f 0:ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hc := halasz_representation_integral f 0
  convert hc using 1
  · apply integral_congr_ae
    filter_upwards [] with α
    simp [halaszRepresentationWeight,halaszVinogradovCharacter,Complex.mul_conj']

theorem halasz_zero_representation_dominates {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) :
    halaszRepresentationCount f w ≤ halaszRepresentationCount f 0 := by
  have h := norm_integral_le_integral_norm (halaszRepresentationWeight f w)
    (μ := halaszVinogradovHaar k)
  rw [halasz_representation_integral] at h
  simp_rw [halasz_representation_weight_norm] at h
  rw [halasz_representation_energy,Complex.norm_natCast] at h
  exact_mod_cast h

end TwoPointCorrelations

end OAI
