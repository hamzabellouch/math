import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace FiniteSpectralMatching

lemma card_filter_perm {n : ℕ} (e : Equiv.Perm (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i => p (e i)).card=(Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  exact Equiv.sum_comp e (fun i => if p i then 1 else 0)

lemma sorted_le_of_cumulative {n : ℕ} (x y : Fin n → ℝ) (δ : ℝ)
    (h : ∀ t : ℝ,(Finset.univ.filter fun i => x i≤t).card≤
      (Finset.univ.filter fun i => y i≤t+δ).card) (j : Fin n) :
    y (Tuple.sort y j)≤x (Tuple.sort x j)+δ := by
  classical
  have hj : j.val<(Finset.univ.filter fun i => x (Tuple.sort x i)≤x (Tuple.sort x j)).card :=
    (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort x)).mpr le_rfl
  have he₁ := card_filter_perm (Tuple.sort x) (fun i => x i≤x (Tuple.sort x j))
  rw [he₁] at hj
  have hj' := hj.trans_le (h (x (Tuple.sort x j)))
  have he₂ := card_filter_perm (Tuple.sort y) (fun i => y i≤x (Tuple.sort x j)+δ)
  rw [←he₂] at hj'
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort y)).mp hj'

theorem permutation_of_cumulative_counts {n : ℕ} (x y : Fin n → ℝ) (δ : ℝ)
    (hxy : ∀ t : ℝ,(Finset.univ.filter fun i => x i≤t).card≤
      (Finset.univ.filter fun i => y i≤t+δ).card)
    (hyx : ∀ t : ℝ,(Finset.univ.filter fun i => y i≤t).card≤
      (Finset.univ.filter fun i => x i≤t+δ).card) :
    ∃ e : Equiv.Perm (Fin n),∀ i,|x i-y (e i)|≤δ := by
  let e := (Tuple.sort x).symm.trans (Tuple.sort y)
  refine ⟨e,?_⟩
  intro i
  let j := (Tuple.sort x).symm i
  have hx := sorted_le_of_cumulative x y δ hxy j
  have hy := sorted_le_of_cumulative y x δ hyx j
  have hxi : x (Tuple.sort x j)=x i := by simp [j]
  have hyi : y (Tuple.sort y j)=y (e i) := rfl
  rw [hxi,hyi] at hx hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end FiniteSpectralMatching

end
end

end OAI
