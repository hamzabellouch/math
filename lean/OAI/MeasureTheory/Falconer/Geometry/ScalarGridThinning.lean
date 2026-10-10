import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement
import Mathlib.Algebra.Order.Ring.Abs

namespace OAI

/-! Constant-loss separation before selecting the intermediate branching
scale. The selected points are original points, grouped by grid residue. -/
namespace Falconer

 theorem scalar_floor_distance_lt {δ x y : ℝ} :
    |(⌊x/δ⌋:ℝ)-(⌊y/δ⌋:ℝ)| < |x/δ-y/δ|+1 := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  have h1 := le_abs_self (x/δ-y/δ)
  have h2 := neg_le_abs (x/δ-y/δ)
  rw [abs_lt]
  constructor <;> linarith

 theorem scalar_residue_separation {δ x y : ℝ} (hδ : 0 < δ) (M : ℕ)
    (hcell : ⌊x/δ⌋ ≠ ⌊y/δ⌋)
    (hres : ⌊x/δ⌋ % (M:ℤ) = ⌊y/δ⌋ % (M:ℤ)) :
    ((M:ℝ)-1)*δ < |x-y| := by
  have hdvd : (M:ℤ) ∣ ⌊x/δ⌋-⌊y/δ⌋ :=
    Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hres)
  have hm : (M:ℤ) ≤ |⌊x/δ⌋-⌊y/δ⌋| := Int.le_abs_of_dvd (sub_ne_zero.mpr hcell) hdvd
  have hmR : (M:ℝ) ≤ |(⌊x/δ⌋:ℝ)-(⌊y/δ⌋:ℝ)| := by exact_mod_cast hm
  have hh := scalar_floor_distance_lt (δ := δ) (x := x) (y := y)
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  have hlt : (M:ℝ)-1 < |x-y|/δ := by linarith
  exact (lt_div_iff₀ hδ).mp hlt

 theorem scalar_grid_thinning {δ : ℝ} (hδ : 0 < δ) (E : Finset ℝ)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|)
    (M : ℕ) (hM : 0 < M) :
    ∃ F ⊆ E, E.card ≤ M*F.card ∧
      ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ((M:ℝ)-1)*δ < |x-y| := by
  classical
  by_cases hE : E.Nonempty
  · let code := fun x : ℝ => ⌊x/δ⌋ % (M:ℤ)
    let C := E.image code
    have hC : C.Nonempty := hE.image code
    obtain ⟨c,hc,hmax⟩ := C.exists_max_image (fun k => (E.filter fun x => code x = k).card) hC
    let F := E.filter fun x => code x = c
    have hCsub : C ⊆ Finset.Ico 0 (M:ℤ) := by
      intro k hk
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by exact_mod_cast hM.ne'),
        Int.emod_lt_of_pos _ (by exact_mod_cast hM)⟩
    have hCc : C.card ≤ M := by
      have hh := Finset.card_le_card hCsub
      simpa only [Int.card_Ico,sub_zero,Int.toNat_natCast] using hh
    refine ⟨F,Finset.filter_subset _ _,?_,?_⟩
    · calc
        E.card = ∑ k ∈ C, (E.filter fun x => code x = k).card := Finset.card_eq_sum_card_image code E
        _ ≤ ∑ _k ∈ C, F.card := Finset.sum_le_sum hmax
        _ = C.card*F.card := by simp
        _ ≤ M*F.card := Nat.mul_le_mul_right _ hCc
    · intro x hx y hy hxy
      have hxE := (Finset.mem_filter.mp hx).1
      have hyE := (Finset.mem_filter.mp hy).1
      have hcell : ⌊x/δ⌋ ≠ ⌊y/δ⌋ := fun hh => hxy (scalarCells_injective hδ hsep hxE hyE hh)
      exact scalar_residue_separation hδ M hcell
        ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · have hEe : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    subst E
    exact ⟨∅,Finset.Subset.refl _,by simp,by simp⟩

end Falconer

end OAI
