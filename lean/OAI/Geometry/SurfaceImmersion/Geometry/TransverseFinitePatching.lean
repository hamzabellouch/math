import OAI.Geometry.SurfaceImmersion.Geometry.TransverseSmallFunction

namespace OAI

/-! Finite patching of narrow corrections along defining curves. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem finite_small_correction {f g : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hgc : ∀ i, HasCompactSupport (g i)) {K : Set E}
    (hz : ∀ i x, x ∈ K → x ∈ tsupport (g i) → f i x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ ⋃ i, tsupport (g i) ∧ (∀ x, |H x| < ε) ∧
      ∀ x ∈ K, fderiv ℝ H x = ∑ i, g i x • fderiv ℝ (f i) x := by
  classical
  let e := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have he : 0 < e := div_pos hε hden
  have hbound (i : ι) : ∃ G : ℝ, 0 ≤ G ∧ ∀ x, |g i x| ≤ G := by
    obtain ⟨A, hA⟩ := (hg i).continuous.bounded_above_of_compact_support (hgc i)
    refine ⟨max 0 A, le_max_left _ _, ?_⟩
    intro x
    have hx : |g i x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x
    exact hx.trans (le_max_right _ _)
  choose G hG hb using hbound
  choose H hH hHs hHe hHd using fun i => exists_small_correction (hf i) (hg i) (hG i) (hb i) he
  let F : E → ℝ := fun x => ∑ i, H i x
  have hFs : tsupport F ⊆ ⋃ i, tsupport (g i) := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      have hn (i : ι) : x ∉ tsupport (H i) := by
        intro hh
        exact hnot (mem_iUnion.mpr ⟨i, hHs i hh⟩)
      have hFx : F x = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact image_eq_zero_of_notMem_tsupport (hn i)
      exact hx hFx
    · exact isClosed_iUnion_of_finite (fun i => isClosed_tsupport (g i))
  have hFc : HasCompactSupport F :=
    (isCompact_iUnion fun i => hgc i).of_isClosed_subset (isClosed_tsupport F) hFs
  refine ⟨F, ContDiff.sum (fun i _ => hH i), hFc, hFs, ?_, ?_⟩
  · intro x
    have hsum : |F x| ≤ (Fintype.card ι : ℝ) * e := by
      calc
        |F x| ≤ ∑ i, |H i x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, e := Finset.sum_le_sum (fun i _ => (hHe i x).le)
        _ = (Fintype.card ι : ℝ) * e := by simp
    apply lt_of_le_of_lt hsum
    change (Fintype.card ι : ℝ) * (ε / ((Fintype.card ι : ℝ) + 1)) < ε
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · intro x hx
    change fderiv ℝ (fun y => ∑ i, H i y) x = _
    rw [fderiv_fun_sum (fun i _ => (hH i).differentiable (by simp) x)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hgi : x ∈ tsupport (g i)
    · exact hHd i x (hz i x hx hgi)
    · have hHi : x ∉ tsupport (H i) := fun hh => hgi (hHs i hh)
      rw [fderiv_of_notMem_tsupport ℝ hHi, image_eq_zero_of_notMem_tsupport hgi, zero_smul]

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
