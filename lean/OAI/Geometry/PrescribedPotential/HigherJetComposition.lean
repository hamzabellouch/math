import Mathlib

namespace OAI

/-! Higher Jet Composition. -/

section

 

noncomputable section
open Finset
open scoped ContDiff
namespace HigherJet

lemma prod_one_exception {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {B T : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hf : ∀ i, 0 ≤ f i) (hb : ∀ i, f i ≤ T ∨ f i ≤ B)
    (hunique : ∀ i j, B < f i → B < f j → i = j) :
    ∏ i, f i ≤ B^(Fintype.card ι)*T := by
  by_cases he : ∃ i, B < f i
  · obtain ⟨j,hj⟩ := he
    have h_bound (i : ι) : f i ≤ B*(if i=j then T else 1) := by
      by_cases hij : i=j
      · subst i
        simp only [ite_true]
        obtain hi | hi := hb j
        · exact hi.trans (le_mul_of_one_le_left (by linarith) hB)
        · exact hi.trans (le_mul_of_one_le_right (by linarith) hT)
      · rw [ite_eq_right hij,mul_one]
        exact le_of_not_gt (fun hi => hij (hunique i j hi hj))
    exact (Finset.prod_le_prod₀ (fun index _ => hf index) (fun index _ => h_bound index)).trans_eq
      (by rw [Finset.prod_mul_distrib]; simp)
  · have hh (i) : f i ≤ B := le_of_not_gt (fun hi => he ⟨i,hi⟩)
    exact (Finset.prod_le_prod₀ (fun index _ => hf index) (fun index _ => hh index)).trans
      (by simpa using le_mul_of_one_le_right (pow_nonneg (by linarith : 0 ≤ B) _) hT)

lemma OrderedFinpartition.large_part_unique {m r : ℕ}
    (c : OrderedFinpartition m) (hr : m < 2*r) (i j : Fin c.length)
    (hi : r ≤ c.partSize i) (hj : r ≤ c.partSize j) : i=j := by
  by_contra hij
  have hsum : ∑ k, c.partSize k = m := by
    simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
  have htwo : c.partSize i+c.partSize j ≤ ∑ k, c.partSize k := by
    simpa [hij] using (Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i,j} : Finset (Fin c.length)) ⊆ univ from subset_univ _)
      (fun _ _ _ => Nat.zero_le _) : ∑ k ∈ ({i,j} : Finset (Fin c.length)), c.partSize k ≤
        ∑ k, c.partSize k)
  omega

lemma OrderedFinpartition.prod_jet_bound {m r : ℕ}
    (c : OrderedFinpartition m) (hr : m < 2*r)
    (a : ℕ → ℝ) {B T : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T)
    (ha : ∀ j, 0 ≤ a j) (hlow : ∀ j, 0 < j → j < r → a j ≤ B)
    (hhigh : ∀ j, r ≤ j → j ≤ m → a j ≤ T) :
    ∏ i, a (c.partSize i) ≤ B^m*T := by
  have hb (i : Fin c.length) : a (c.partSize i) ≤ T ∨ a (c.partSize i) ≤ B := by
    by_cases hi : c.partSize i < r
    · exact Or.inr (hlow _ (c.partSize_pos i) hi)
    · exact Or.inl (hhigh _ (le_of_not_gt hi) (c.partSize_le i))
  have hu (i j : Fin c.length) (hi : B < a (c.partSize i)) (hj : B < a (c.partSize j)) : i=j := by
    have hi' : r ≤ c.partSize i := le_of_not_gt (fun hh => (not_lt_of_ge (hlow _ (c.partSize_pos i) hh)) hi)
    have hj' : r ≤ c.partSize j := le_of_not_gt (fun hh => (not_lt_of_ge (hlow _ (c.partSize_pos j) hh)) hj)
    exact OrderedFinpartition.large_part_unique c hr i j hi' hj'
  exact (prod_one_exception (fun i => a (c.partSize i)) hB hT
    (fun _ => ha _) hb hu).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hB (by simpa using c.length_le)) (by linarith))

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

 

lemma composition_top_jet_bound {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    {m r : ℕ} (hr : m < 2*r) {B T C : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hlow : ∀ j, 0 < j → j < r → ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hhigh : ∀ j, r ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ T)
    (hgjet : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤
      (Fintype.card (OrderedFinpartition m) : ℝ)*C*B^m*T := by
  rw [iteratedFDeriv_comp (i := m) hg hf (by exact WithTop.coe_le_coe.mpr le_top),FormalMultilinearSeries.taylorComp]
  calc
    _ ≤ ∑ c : OrderedFinpartition m, ‖c.compAlongOrderedFinpartition
      (iteratedFDeriv ℝ c.length g (f x)) (fun i => iteratedFDeriv ℝ (c.partSize i) f x)‖ := norm_sum_le _ _
    _ ≤ ∑ _c : OrderedFinpartition m, C*(B^m*T) := by
      apply Finset.sum_le_sum
      intro c _
      exact c.norm_compAlongOrderedFinpartition_le _ _ |>.trans
        (mul_le_mul (hgjet _ c.length_le)
          (OrderedFinpartition.prod_jet_bound c hr _ hB hT (fun _ => norm_nonneg _) hlow hhigh)
          (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC)
    _ = _ := by simp [mul_assoc]
end HigherJet

end
end

end OAI
