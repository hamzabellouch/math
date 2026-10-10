import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartTrace
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothBump

namespace OAI

noncomputable section
namespace VelocityDetection.ChartTrace
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting
variable (A : RoutingData) (tr : RoutingArray.Trace A) (N : ℕ)

theorem route_is_installed (hN : 0 < N) (h : ∀ n < N, tr.stopped n = false) (s : ℝ) :
    ∃ n : ℕ, ∃ hn : n < N, route A tr N s = path A N n (tr.instruction n (h n hn)) s := by
  by_cases hs : s ≤ 0
  · refine ⟨0,hN,?_⟩
    rw [route_before A tr N hs,← segment_eq_installed A tr N 0 (h 0 hN),
      segment_before A tr N 0 (by simpa using hs)]
  by_cases ht : N ≤ s
  · have hn : N-1 < N := by omega
    refine ⟨N-1,hn,?_⟩
    rw [route_after A tr N ht,← segment_eq_installed A tr N (N-1) (h (N-1) hn),segment_after]
    · rw [Nat.sub_add_cancel hN]
    · have hh : ((N-1:ℕ):ℝ)+1 = N := by exact_mod_cast Nat.sub_add_cancel hN
      rwa [hh]
  have hs0 := le_of_lt (lt_of_not_ge hs)
  have hn : ⌊s⌋₊ < N := (Nat.floor_lt hs0).mpr (lt_of_not_ge ht)
  refine ⟨⌊s⌋₊,hn,?_⟩
  rw [route_eq_segment A tr N _ hn ⟨Nat.floor_le hs0,(Nat.lt_floor_add_one s).le⟩,
    segment_eq_installed A tr N _ (h _ hn)]

theorem route_bounds (hN : 0 < N) (h : ∀ n < N, tr.stopped n = false) (s : ℝ) :
    route A tr N s 0 ∈ Icc (1/4:ℝ) (1/4+1/1024) ∧
    route A tr N s 1 ∈ Icc (1/16:ℝ) (1/2) := by
  obtain ⟨n,hn,he⟩ := route_is_installed A tr N hN h s
  rw [he]
  exact path_bounds A N n _ hn s

theorem route_nonterminal (hN : 0 < N) (h : ∀ n ≤ N, tr.stopped n = false) (s : ℝ) :
    (1/2-1/1024:ℝ) ≤ route A tr N s 1 := by
  obtain ⟨n,hn,he⟩ := route_is_installed A tr N hN (fun n hn => h n hn.le) s
  rw [he]
  apply nonterminal_bounds A N n _ hn
  rw [tr.sign_eq,h (n+1) (by omega)]
  norm_num

theorem packet_support_chart (hN : 0 < N) (h : ∀ n < N, tr.stopped n = false)
    (s : ℝ) (X : Coord 2) (hX : SmoothBump.packet (radius A N) (X-route A tr N s) ≠ 0) :
    X ∈ chartSet := by
  obtain ⟨n,hn,he⟩ := route_is_installed A tr N hN h s
  apply path_neighborhood A N n _ hn s X
  intro i
  have hh : |X i-route A tr N s i| < radius A N :=
    lt_of_not_ge (fun hi => hX (SmoothBump.packet_zero (radius_pos A N) ⟨i,hi⟩))
  rw [he] at hh
  linarith [radius_pos A N]

theorem packet_zero_detector (hN : 0 < N) (h : ∀ n ≤ N, tr.stopped n = false)
    (s : ℝ) (X : Coord 2) (hX : X 1 < 1/8) :
    SmoothBump.packet (radius A N) (X-route A tr N s) = 0 := by
  apply SmoothBump.packet_zero (radius_pos A N)
  refine ⟨1,?_⟩
  have hroute := route_nonterminal A tr N hN h s
  have hR : radius A N ≤ (1/65536:ℝ) := by unfold radius; linarith [scale_small A N]
  change radius A N ≤ |X 1-route A tr N s 1|
  rw [abs_of_neg (by linarith)]
  linarith

end VelocityDetection.ChartTrace
end

end OAI
