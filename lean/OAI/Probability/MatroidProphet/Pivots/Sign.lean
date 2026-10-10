import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup X] [Module ℝ X]

def RealizesSigns (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (t : Finset ι) (x : X) : Prop :=
  ∀ i, if i ∈ t then 0 < v i x + c i else v i x + c i < 0

noncomputable def affinePatterns (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ) :
    Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun t => ∃ x, RealizesSigns v c t x)

lemma mem_affinePatterns {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ} {t : Finset ι} :
    t ∈ affinePatterns v c ↔ ∃ x, RealizesSigns v c t x := by
  classical
  simp [affinePatterns]

private lemma exists_positive_combination
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hreal : ∀ t : Finset ι, ∃ x, RealizesSigns v c t x)
    (a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    ∃ x, 0 < ∑ i, a i * (v i x + c i) := by
  classical
  obtain ⟨x, hx⟩ := hreal (Finset.univ.filter (fun i => 0 < a i))
  have hpos (i : ι) (hai : 0 < a i) : 0 < v i x + c i := by
    simpa [RealizesSigns, hai] using hx i
  have hneg (i : ι) (hai : ¬ 0 < a i) : v i x + c i < 0 := by
    simpa [RealizesSigns, hai] using hx i
  refine ⟨x, Finset.sum_pos' (fun i _ => ?_) ?_⟩
  · by_cases hai : 0 < a i
    · exact mul_nonneg (le_of_lt hai) (le_of_lt (hpos i hai))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hai) (le_of_lt (hneg i hai))
  · obtain ⟨i, hi⟩ := ha
    refine ⟨i, Finset.mem_univ i, ?_⟩
    by_cases hai : 0 < a i
    · exact mul_pos hai (hpos i hai)
    · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt hai) hi) (hneg i hai)

omit [DecidableEq ι] in
private lemma sum_affine_eq_of_linear_combination_zero
    {v : ι → X →ₗ[ℝ] ℝ} (c : ι → ℝ) {a : ι → ℝ}
    (ha : ∑ i, a i • v i = 0) (x : X) :
    (∑ i, a i * (v i x + c i)) = ∑ i, a i * c i := by
  have hz := congrArg (fun f : X →ₗ[ℝ] ℝ => f x) ha
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply] at hz
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hz, zero_add]

lemma linearIndependent_of_all_signs
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hreal : ∀ t : Finset ι, ∃ x, RealizesSigns v c t x) :
    LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hi
  obtain ⟨x, hx⟩ := exists_positive_combination v c hreal a ⟨i, hi⟩
  obtain ⟨y, hy⟩ := exists_positive_combination v c hreal (fun j => -a j)
    ⟨i, neg_ne_zero.mpr hi⟩
  simp only [neg_mul, Finset.sum_neg_distrib] at hy
  rw [sum_affine_eq_of_linear_combination_zero c ha x] at hx
  rw [sum_affine_eq_of_linear_combination_zero c ha y] at hy
  linarith

lemma all_signs_of_shatters {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ}
    {s : Finset ι} (hs : (affinePatterns v c).Shatters s) :
    ∀ t : Finset s, ∃ x,
      RealizesSigns (fun i : s => v i) (fun i : s => c i) t x := by
  classical
  intro t
  obtain ⟨u, hu, hsu⟩ := hs (t := t.image Subtype.val) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property)
  obtain ⟨x, hx⟩ := mem_affinePatterns.mp hu
  refine ⟨x, fun i => ?_⟩
  have hi : (i : ι) ∈ u ↔ i ∈ t := by
    have heq := congrArg (fun z : Finset ι => (i : ι) ∈ z) hsu
    simpa [Finset.mem_image, i.property] using heq
  simpa only [hi] using hx i

lemma shatters_card_le_finrank [FiniteDimensional ℝ X]
    {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ} {s : Finset ι}
    (hs : (affinePatterns v c).Shatters s) : s.card ≤ Module.finrank ℝ X := by
  have hli := linearIndependent_of_all_signs
    (fun i : s => v i) (fun i : s => c i) (all_signs_of_shatters hs)
  have hc := hli.fintype_card_le_finrank
  simpa using hc

lemma card_affinePatterns_le [FiniteDimensional ℝ X]
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ) :
    (affinePatterns v c).card ≤
      ∑ k ∈ Finset.Iic (Module.finrank ℝ X), (Fintype.card ι).choose k := by
  classical
  have hdim : (affinePatterns v c).vcDim ≤ Module.finrank ℝ X := by
    unfold Finset.vcDim
    exact Finset.sup_le (fun s hs => shatters_card_le_finrank (Finset.mem_shatterer.mp hs))
  exact (Finset.card_le_card_shatterer _).trans
    (Finset.card_shatterer_le_sum_vcDim.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hdim)
        (fun _ _ _ => Nat.zero_le _)))

end Pivots
end MatroidProphet

end OAI
