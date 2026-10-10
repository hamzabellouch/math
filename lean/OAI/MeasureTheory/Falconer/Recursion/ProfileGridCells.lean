import OAI.MeasureTheory.Falconer.Recursion.InnerProfileGrid
import OAI.MeasureTheory.Falconer.Recursion.OrderedProfileIntervals

namespace OAI

/-! Finite interval accounting after inward rounding to the block grid. -/
namespace Falconer

noncomputable def innerProfileCell (n : ℕ) (c : ℝ × ℝ) : ℝ × ℝ :=
  (profileGridLeft n c.1,profileGridRight n (c.1+c.2)-profileGridLeft n c.1)

@[simp] theorem innerProfileCell_end (n : ℕ) (c : ℝ × ℝ) :
    (innerProfileCell n c).1+(innerProfileCell n c).2 = profileGridRight n (c.1+c.2) := by
  simp [innerProfileCell]

theorem innerProfileCell_length_bounds {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) :
    c.2-2/(n : ℝ) ≤ (innerProfileCell n c).2 ∧ (innerProfileCell n c).2 ≤ c.2 := by
  exact ⟨(profileGrid_interval_bounds hn c.1 c.2).2.1,(profileGrid_interval_bounds hn c.1 c.2).1⟩

theorem innerProfileCells_ordered {n : ℕ} (hn : 0 < n) {S : List (ℝ × ℝ)}
    (hS : S.Pairwise (fun c d => c.1+c.2 ≤ d.1)) :
    (S.map (innerProfileCell n)).Pairwise (fun c d => c.1+c.2 ≤ d.1) := by
  rw [List.pairwise_map]
  apply hS.imp
  intro c d hcd
  rw [innerProfileCell_end]
  exact (profileGridRight_bounds hn (c.1+c.2)).2.trans
    (hcd.trans (profileGridLeft_bounds hn d.1).1)

theorem innerProfileCells_length_lower {n : ℕ} (hn : 0 < n) (S : List (ℝ × ℝ)) :
    (S.map Prod.snd).sum-(2/(n : ℝ))*(S.length : ℝ) ≤
      ((S.map (innerProfileCell n)).map Prod.snd).sum := by
  induction S with
  | nil => simp
  | cons c S ih =>
    have hc := (innerProfileCell_length_bounds hn c).1
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

theorem innerProfileCells_min_length {n : ℕ} (hn : 0 < n) {τ : ℝ}
    (hmesh : 2/(n : ℝ) ≤ τ/2) {S : List (ℝ × ℝ)}
    (hmin : ∀ c ∈ S, τ ≤ c.2) :
    ∀ c ∈ S.map (innerProfileCell n), τ/2 ≤ c.2 := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hh := (innerProfileCell_length_bounds hn d).1
  linarith [hmin d hd]

theorem innerProfileCells_total_loss {n : ℕ} (hn : 0 < n) {τ κ : ℝ} (hτ : 0 < τ)
    {S : List (ℝ × ℝ)} (hS : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ 1 ∧ τ ≤ c.2)
    (hcover : 1-κ ≤ (S.map Prod.snd).sum) :
    1-κ-2/((n : ℝ)*τ) ≤ ((S.map (innerProfileCell n)).map Prod.snd).sum := by
  have hcount := ordered_interval_count_bound (show (0 : ℝ) ≤ 1 by norm_num) hS
    (fun c hc => ⟨(hb c hc).1,(hb c hc).2.1,hτ.le.trans (hb c hc).2.2⟩)
    (fun c hc => (hb c hc).2.2)
  have hcount' : (S.length : ℝ) ≤ 1/τ := by
    apply (le_div_iff₀ hτ).2
    simpa only [sub_zero,mul_comm] using hcount
  have hmul := mul_le_mul_of_nonneg_left hcount' (by positivity : 0 ≤ 2/(n : ℝ))
  have hloss := innerProfileCells_length_lower hn S
  have he : (2/(n : ℝ))*(1/τ) = 2/((n : ℝ)*τ) := by ring
  rw [he] at hmul
  linarith

end Falconer

end OAI
