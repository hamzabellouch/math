import Mathlib

namespace OAI

/-! Second Jet Composition. -/

section

 

noncomputable section
open Finset
open scoped ContDiff
namespace HigherJet
lemma positive_list_sum_two {l : List ℕ} (hp : ∀ j ∈ l, 0 < j) (hs : l.sum = 2) :
    l = [2] ∨ l = [1,1] := by
  cases l with
  | nil => simp at hs
  | cons a l =>
    have ha := hp a (by simp)
    cases l with
    | nil => simp at hs; simp [hs]
    | cons b l =>
      have hb := hp b (by simp)
      cases l with
      | nil =>
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hs
        have : a=1 ∧ b=1 := by omega
        simp [this.1,this.2]
      | cons c l =>
        have hc := hp c (by simp)
        simp only [List.sum_cons] at hs
        omega

lemma OrderedFinpartition.prod_second_bound (c : OrderedFinpartition 2)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a (c.partSize i) ≤ a 2+(a 1)^2 := by
  have hsum : (List.ofFn c.partSize).sum = 2 := by
    rw [List.sum_ofFn]
    simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
  have hpos : ∀ j ∈ List.ofFn c.partSize, 0 < j := by
    intro j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    exact c.partSize_pos i
  have he : ∏ i, a (c.partSize i) = ((List.ofFn c.partSize).map a).prod := by
    rw [List.map_ofFn,List.prod_ofFn]
    rfl
  rw [he]
  obtain h | h := positive_list_sum_two hpos hsum
  · simp only [h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · simp only [h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    nlinarith only [ha 2]

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma composition_second_jet_bound {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    {C : ℝ} (hC : 0 ≤ C)
    (hgjet : ∀ j, j ≤ 2 → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 (g ∘ f) x‖ ≤
      (Fintype.card (OrderedFinpartition 2) : ℝ)*C*
        (‖iteratedFDeriv ℝ 2 f x‖+‖iteratedFDeriv ℝ 1 f x‖^2) := by
  rw [iteratedFDeriv_comp (i := 2) hg hf (by exact WithTop.coe_le_coe.mpr le_top),FormalMultilinearSeries.taylorComp]
  calc
    _ ≤ ∑ c : OrderedFinpartition 2, ‖c.compAlongOrderedFinpartition
      (iteratedFDeriv ℝ c.length g (f x)) (fun i => iteratedFDeriv ℝ (c.partSize i) f x)‖ := norm_sum_le _ _
    _ ≤ ∑ _c : OrderedFinpartition 2, C*(‖iteratedFDeriv ℝ 2 f x‖+‖iteratedFDeriv ℝ 1 f x‖^2) := by
      apply Finset.sum_le_sum
      intro c _
      exact c.norm_compAlongOrderedFinpartition_le _ _ |>.trans
        (mul_le_mul (hgjet _ c.length_le)
          (OrderedFinpartition.prod_second_bound c (fun j => ‖iteratedFDeriv ℝ j f x‖) (fun j => norm_nonneg _))
          (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC)
    _ = _ := by simp [mul_assoc]
end HigherJet

end
end

end OAI
