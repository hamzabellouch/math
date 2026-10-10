import OAI.Analysis.Pureness.Comparison.HereditaryCorner
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cfc_mem_hereditaryCorner {b : A} (hb : 0 ≤ b) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 = 0) :
    cfc f b ∈ hereditaryCorner b hb := by
  let : IsClosed (hereditaryCorner b hb : Set A) := isClosed_closure
  rw [← cfcₙ_eq_cfc hf.continuousOn hf0]
  exact cfcₙ_mem f (self_mem_hereditaryCorner b hb)

theorem orthogonal_pair_of_positive_spectral_values {b : A} (hb : 0 ≤ b)
    {s t : ℝ} (hs : s ∈ spectrum ℝ b) (ht : t ∈ spectrum ℝ b)
    (hs0 : 0 < s) (hst : s < t) :
    ∃ c d : A, 0 ≤ c ∧ 0 ≤ d ∧ c ≠ 0 ∧ d ≠ 0 ∧ c * d = 0 ∧
      c ∈ hereditaryCorner b hb ∧ d ∈ hereditaryCorner b hb := by
  let m := (s + t) / 2
  have hsm : s < m := by dsimp [m]; linarith
  have hmt : m < t := by dsimp [m]; linarith
  have hm : 0 < m := hs0.trans hsm
  let f : ℝ → ℝ := fun x => x * max (m - x) 0
  let g : ℝ → ℝ := fun x => max (x - m) 0
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hg0 : g 0 = 0 := by simp [g, hm.le]
  have hfg : ∀ x : ℝ, f x * g x = 0 := by
    intro x
    by_cases hx : x ≤ m
    · simp [f, g, max_eq_right (sub_nonpos.mpr hx)]
    · simp [f, g, max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))]
  have hsa := hb.isSelfAdjoint
  refine ⟨cfc f b, cfc g b, ?_, ?_, ?_, ?_, ?_,
    cfc_mem_hereditaryCorner hb f hf hf0, cfc_mem_hereditaryCorner hb g hg hg0⟩
  · apply cfc_nonneg
    intro x hx
    exact mul_nonneg (spectrum_nonneg_of_nonneg hb hx) (le_max_right _ _)
  · apply cfc_nonneg
    intro x hx
    exact le_max_right _ _
  · intro hz
    have heq : cfc f b = cfc (fun _ : ℝ => 0) b := by simpa using hz
    have h := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hsa hs
    have hp : 0 < f s := by
      dsimp [f]
      rw [max_eq_left (sub_nonneg.mpr hsm.le)]
      exact mul_pos hs0 (sub_pos.mpr hsm)
    exact (ne_of_gt hp) h
  · intro hz
    have heq : cfc g b = cfc (fun _ : ℝ => 0) b := by simpa using hz
    have h := eqOn_of_cfc_eq_cfc heq hg.continuousOn continuousOn_const hsa ht
    have hp : 0 < g t := by
      dsimp [g]
      rw [max_eq_left (sub_nonneg.mpr hmt.le)]
      exact sub_pos.mpr hmt
    exact (ne_of_gt hp) h
  · rw [← cfc_mul f g b hf.continuousOn hg.continuousOn]
    simp only [hfg, cfc_const_zero]

theorem positive_scalar_projection_or_orthogonal_pair {b : A}
    (hb : 0 ≤ b) (hbn : b ≠ 0) :
    (∃ r : ℝ, 0 < r ∧ ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧
      q ∈ hereditaryCorner b hb ∧ b = r • q) ∨
    (∃ c d : A, 0 ≤ c ∧ 0 ≤ d ∧ c ≠ 0 ∧ d ≠ 0 ∧ c * d = 0 ∧
      c ∈ hereditaryCorner b hb ∧ d ∈ hereditaryCorner b hb) := by
  classical
  have hsa := hb.isSelfAdjoint
  have hex : ∃ r ∈ spectrum ℝ b, 0 < r := by
    by_contra hn
    push Not at hn
    apply hbn
    apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) b
    intro x hx
    exact le_antisymm (hn x hx) (spectrum_nonneg_of_nonneg hb hx)
  obtain ⟨r, hr, hr0⟩ := hex
  by_cases hs : ∀ x ∈ spectrum ℝ b, x = 0 ∨ x = r
  · left
    have hb2 : b * b = r • b := by
      rw [← cfc_id' ℝ b, ← cfc_mul (fun x : ℝ => x) (fun x => x) b,
        ← cfc_smul r (fun x : ℝ => x) b]
      apply cfc_congr
      intro x hx
      rcases hs x hx with h | h <;> simp [h]
    let q : A := r⁻¹ • b
    have hq2 : q * q = q := by
      dsimp [q]
      rw [smul_mul_smul_comm, hb2, smul_smul]
      congr 1
      field_simp
    have hq : IsStarProjection q :=
      ⟨hq2, by change star q = q; simp [q, hb.star_eq]⟩
    have hfactor : b = r • q := by simp [q, smul_smul, hr0.ne']
    refine ⟨r, hr0, q, hq, ?_, ?_, hfactor⟩
    · intro hz
      rw [hz, smul_zero] at hfactor
      exact hbn hfactor
    · exact (hereditaryCorner b hb).smul_mem (r⁻¹ : ℝ) (self_mem_hereditaryCorner b hb)
  · push Not at hs
    obtain ⟨x, hx, hx0, hxr⟩ := hs
    have hxpos := lt_of_le_of_ne (spectrum_nonneg_of_nonneg hb hx) (Ne.symm hx0)
    right
    rcases lt_or_gt_of_ne hxr with h | h
    · exact orthogonal_pair_of_positive_spectral_values hb hx hr hxpos h
    · exact orthogonal_pair_of_positive_spectral_values hb hr hx hr0 h
end CuntzComparison

end OAI
