import Mathlib

namespace OAI

/-! Compact Smooth Cutoff. -/

section

noncomputable section
open Set Filter Topology Function
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set E, ∃ χ : E → ℝ, IsCompact L ∧ L ⊆ U ∧ K ⊆ L ∧ ContDiff ℝ ∞ χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ K, χ x=1) ∧
      (∀ x ∈ L, χ x≠0 → x ∈ interior L) := by
  classical
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f,hfs,hfd,hfv⟩ := isOpen_interior.exists_contDiff_support_eq (n := ⊤) (s := interior L)
  obtain ⟨g,hgs,hgd,hgv⟩ := hK.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hfp (x : E) : 0 ≤ f x := (hfv ⟨x,rfl⟩).1
  have hgp (x : E) : 0 ≤ g x := (hgv ⟨x,rfl⟩).1
  have hd (x : E) : 0 < f x+g x := by
    by_cases hx : x ∈ K
    · have hf : f x ≠ 0 := by rw [← mem_support,hfs]; exact hKL hx
      have hp := lt_of_le_of_ne (hfp x) (Ne.symm hf)
      linarith [hgp x]
    · have hg : g x ≠ 0 := by rw [← mem_support,hgs]; exact hx
      have hp := lt_of_le_of_ne (hgp x) (Ne.symm hg)
      linarith [hfp x]
  refine ⟨L,fun x => f x/(f x+g x),hL,hLU,hKL.trans interior_subset,
    hfd.div (hfd.add hgd) (fun x => ne_of_gt (hd x)),?_,?_,?_⟩
  · intro x
    exact ⟨div_nonneg (hfp x) (hd x).le,(div_le_one (hd x)).mpr (by linarith [hgp x])⟩
  · intro x hx
    have hg : g x=0 := by
      by_contra hn
      have hh : x ∈ Kᶜ := by rw [← hgs]; exact hn
      exact hh hx
    change f x/(f x+g x)=1
    rw [hg,add_zero,div_self (ne_of_gt (by linarith [hd x]))]
  · intro x _ hn
    rw [← hfs]
    exact fun he => hn (by change f x/(f x+g x)=0; rw [he,zero_div])
end HigherJet

end
end

end OAI
