import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Filter Metric
open scoped Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem smooth_time_localization {A : ℝ × E → G} {t : ℝ}
    (ht0 : -1<t) (ht1 : t<1)
    (hA : ∀p : ℝ × E, -1<p.1 → p.1<1 → ContDiffAt ℝ (⊤:ℕ∞) A p) :
    ∃B : ℝ × E → G, ContDiff ℝ (⊤:ℕ∞) B ∧
      ∀ᶠs in nhds t, ∀y,B (s,y)=A (s,y) := by
  let δ := min (t+1) (1-t)/2
  have hd : 0<δ := half_pos (lt_min (by linarith) (by linarith))
  have hd0 : δ<t+1 := by
    have := min_le_left (t+1) (1-t)
    dsimp [δ] at *
    linarith
  have hd1 : δ<1-t := by
    have := min_le_right (t+1) (1-t)
    dsimp [δ] at *
    linarith
  let c : ContDiffBump t := ⟨δ/2,δ,half_pos hd,half_lt_self hd⟩
  let B : ℝ × E → G := fun p => c p.1 • A p
  refine ⟨B,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1∈tsupport c
    · rw [c.tsupport_eq] at hp
      have hb : |p.1-t|≤δ := by simpa only [mem_closedBall,Real.dist_eq,c] using hp
      have hlo : -1<p.1 := by have := (abs_le.mp hb).1; linarith
      have hhi : p.1<1 := by have := (abs_le.mp hb).2; linarith
      exact (c.contDiff.contDiffAt.comp p contDiffAt_fst).smul (hA p hlo hhi)
    · have he : c=ᶠ[nhds p.1]0 := notMem_tsupport_iff_eventuallyEq.mp hp
      apply (contDiffAt_const (c:=(0:G))).congr_of_eventuallyEq
      filter_upwards [he.comp_tendsto continuousAt_fst] with q hq
      change c q.1=0 at hq
      simp [B,hq]
  · filter_upwards [c.eventuallyEq_one] with s hs
    intro y
    simp [B,hs]

end LogConcaveSampling

end

end

end

end OAI
