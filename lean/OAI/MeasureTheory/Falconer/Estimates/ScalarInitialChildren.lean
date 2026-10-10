import OAI.MeasureTheory.Falconer.Estimates.ScalarClosestScale

namespace OAI

/-! The local geometric extraction at a block of the original dyadic
 tree. Large child families retain a fixed proportion and have a
 witnessed intermediate separation scale; small families can collapse. -/
namespace Falconer

 theorem scalar_initial_children (E : Finset ℝ) (lo hi : ℕ)
    (hsize : 2050 ≤ E.card)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^hi ≤ |x-y|)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ (1/2:ℝ)^lo) :
    ∃ F ⊆ E, E.card ≤ 1025*F.card ∧ 2 ≤ F.card ∧
      ∃ n : ℕ, lo+3 < n ∧ n+6 ≤ hi ∧
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → 8*(1/2:ℝ)^n < |x-y|) ∧
        ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x-y| ≤ 16*(1/2:ℝ)^n := by
  obtain ⟨F,hFE,hcard,hFsep⟩ := scalar_grid_thinning (pow_pos (by norm_num) hi) E hsep
    1025 (by norm_num)
  have hFc : 2 ≤ F.card := by omega
  have hFd : ∀ x ∈ F, ∀ y ∈ F, |x-y| ≤ 16 := by
    intro x hx y hy
    have hp : (1/2:ℝ)^lo ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (hdiam x (hFE hx) y (hFE hy)).trans (by linarith)
  obtain ⟨n,hn,x,hx,y,hy,hxy,hbound⟩ := scalar_closest_dyadic_scale F hFc hFd
  have hindex := scalar_dyadic_scale_indices n lo hi |x-y| (hn x hx y hy hxy) hbound
    (hdiam x (hFE hx) y (hFE hy)) (by have hh := hFsep x hx y hy hxy; norm_num at hh; exact hh.le)
  exact ⟨F,hFE,hcard,hFc,n,hindex.1,hindex.2,hn,x,hx,y,hy,hxy,hbound⟩

 theorem scalar_small_children (E : Finset ℝ) (hE : E.Nonempty) (hsize : E.card < 2050) :
    ∃ F ⊆ E, F.card = 1 ∧ E.card ≤ 2050*F.card := by
  obtain ⟨x,hx⟩ := hE
  exact ⟨{x},Finset.singleton_subset_iff.mpr hx,by simp,by simpa using hsize.le⟩

end Falconer

end OAI
