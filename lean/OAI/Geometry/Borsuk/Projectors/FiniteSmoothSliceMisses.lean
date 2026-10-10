import Mathlib
import OAI.Geometry.Borsuk.Projectors.NullImage

namespace OAI

namespace BorsukNine
open scoped BigOperators
open MeasureTheory Set

lemma finite_smooth_slice_misses (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (g : κ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c))
    {V : Set (EuclideanSpace ℝ (Fin m))} (hVo : IsOpen V) (hVn : V.Nonempty)
    (hVp : ∀ y ∈ V, ∀ i, 0 < y i) :
    ∃ z : EuclideanSpace ℝ (Fin m), (∃ y ∈ V, z = (∑ i, y i)⁻¹ • y) ∧
      (∀ i, 0 < z i) ∧ (∑ i, z i) = 1 ∧
      ∀ c x, L c x = 1 → g c x ≠ z := by
  classical
  let C (c : κ) (x : EuclideanSpace ℝ (Fin n)) := L c x • g c ((L c x)⁻¹ • x)
  have hCd (c : κ) : ∀ x ∈ {x | L c x ≠ 0}, DifferentiableAt ℝ (C c) x := by
    intro x hx
    exact (L c).differentiableAt.smul
      (((hg c).differentiable (by simp)).differentiableAt.comp x
        (((L c).differentiableAt.inv hx).smul differentiableAt_id))
  have hnull : volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) = 0 := by
    exact measure_iUnion_null (fun c => differentiable_image_null_of_dim_lt n m hnm (hCd c))
  obtain ⟨y,hy,hym⟩ : ∃ y ∈ V, y ∉ ⋃ c : κ, C c '' {x | L c x ≠ 0} := by
    by_contra hn
    push Not at hn
    have hl : volume V ≤ volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) := measure_mono hn
    rw [hnull] at hl
    exact hVo.measure_ne_zero volume hVn (le_antisymm hl (zero_le))
  let s : ℝ := ∑ i, y i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hVp y hy i)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,by omega⟩⟩)
  let z : EuclideanSpace ℝ (Fin m) := s⁻¹ • y
  refine ⟨z,⟨y,hy,rfl⟩,fun i => ?_,?_,?_⟩
  · change 0 < s⁻¹ * y i
    exact mul_pos (inv_pos.mpr hs) (hVp y hy i)
  · change (∑ i, s⁻¹ * y i) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hs)
  · intro c x hx he
    apply hym
    apply Set.mem_iUnion.mpr
    refine ⟨c,s • x,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,map_smul,hx,smul_eq_mul,mul_one]
      exact ne_of_gt hs
    · simp only [C,map_smul,hx,smul_eq_mul,mul_one,inv_smul_smul₀ (ne_of_gt hs),he,z,
        smul_inv_smul₀ (ne_of_gt hs)]

end BorsukNine

end OAI
