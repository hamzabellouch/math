import OAI.MeasureTheory.Falconer.Estimates.DyadicAveraging

namespace OAI

/-! An explicit ordered dyadic interval partition and its weighted averages. -/
namespace Falconer
open Set

noncomputable def dyadicCells (a h : ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => [(a,h)]
  | n+1 => dyadicCells a (h/2) n ++ dyadicCells (a+h/2) (h/2) n

@[simp] theorem dyadicCells_length (a h : ℝ) (n : ℕ) :
    (dyadicCells a h n).length = 2^n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicCells,List.length_append,ih,pow_succ]; omega

theorem dyadicCells_bounds (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {u l : ℝ} (hu : (u,l) ∈ dyadicCells a h n) :
    a ≤ u ∧ u+l ≤ a+h ∧ l = h/(2 : ℝ)^n := by
  induction n generalizing a h with
  | zero =>
    simp only [dyadicCells,List.mem_singleton,Prod.mk.injEq] at hu
    rcases hu with ⟨rfl,rfl⟩
    simp
  | succ n ih =>
    rw [dyadicCells,List.mem_append] at hu
    rcases hu with hu | hu
    · obtain ⟨hlo,hhi,he⟩ := ih a (h := h/2) (by positivity) hu
      refine ⟨hlo,by linarith,he.trans ?_⟩
      simp only [div_div,pow_succ,mul_comm]
    · obtain ⟨hlo,hhi,he⟩ := ih (a+h/2) (h := h/2) (by positivity) hu
      refine ⟨by linarith,by linarith,he.trans ?_⟩
      simp only [div_div,pow_succ,mul_comm]

theorem dyadicCells_cover (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc a (a+h)) :
    ∃ c ∈ dyadicCells a h n, x ∈ Icc c.1 (c.1+c.2) := by
  induction n generalizing a h with
  | zero => exact ⟨(a,h),by simp [dyadicCells],hx⟩
  | succ n ih =>
    by_cases hm : x ≤ a+h/2
    · obtain ⟨c,hc,hxc⟩ := ih a (h := h/2) (by positivity) ⟨hx.1,hm⟩
      exact ⟨c,List.mem_append_left _ hc,hxc⟩
    · obtain ⟨c,hc,hxc⟩ := ih (a+h/2) (h := h/2) (by positivity)
        ⟨le_of_not_ge hm,by linarith [hx.2]⟩
      exact ⟨c,List.mem_append_right _ hc,hxc⟩

theorem dyadicCells_ordered (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    (dyadicCells a h n).Pairwise (fun c d => c.1+c.2 ≤ d.1) := by
  induction n generalizing a h with
  | zero => simp [dyadicCells]
  | succ n ih =>
    rw [dyadicCells,List.pairwise_append]
    refine ⟨ih a (by positivity),ih (a+h/2) (by positivity),?_⟩
    intro c hc d hd
    have hl := dyadicCells_bounds a (h := h/2) (by positivity) n hc
    have hr := dyadicCells_bounds (a+h/2) (h := h/2) (by positivity) n hd
    exact hl.2.1.trans hr.1

theorem dyadicCells_sum (g : ℝ → ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    ((dyadicCells a h n).map (fun c => g c.1 c.2)).sum =
      (2 : ℝ)^n*dyadicAverage g a h n := by
  induction n generalizing a h with
  | zero => simp [dyadicCells,dyadicAverage]
  | succ n ih =>
    simp only [dyadicCells,List.map_append,List.sum_append,ih,dyadicAverage,pow_succ]
    ring

theorem dyadicCells_selected_length (P : ℝ → ℝ → Prop) [DecidableRel P]
    (a h : ℝ) (n : ℕ) :
    (((dyadicCells a h n).filter (fun c => P c.1 c.2)).map Prod.snd).sum =
      h*dyadicAverage (fun a h => if P a h then 1 else 0) a h n := by
  induction n generalizing a h with
  | zero => by_cases hp : P a h <;> simp [dyadicCells,dyadicAverage,hp]
  | succ n ih =>
    simp only [dyadicCells,List.filter_append,List.map_append,List.sum_append,ih,dyadicAverage]
    ring

end Falconer

end OAI
