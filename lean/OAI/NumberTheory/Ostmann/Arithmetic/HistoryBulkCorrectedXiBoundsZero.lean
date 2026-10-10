import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedReindex

namespace OAI

open Erdos970

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Characters.RationalHistory HistoryActiveCoordinates

theorem deriv_eq_zero_below_support (f : ℝ → ℂ) (g : ℝ → ℝ) (a : ℝ)
    (hg : ContinuousAt g 0) (hs : ∀t, f t ≠ 0 → a ≤ g t) (h0 : g 0 < a) :
    deriv f 0 = 0 := by
  have he : f =ᶠ[𝓝 0] fun _ => (0:ℂ) := by
    filter_upwards [hg.eventually (eventually_lt_nhds h0)] with t ht
    by_contra hn
    exact (not_le_of_gt ht) (hs t hn)
  rw [he.deriv_eq,deriv_const]

theorem logCurve_positive {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀i,0 < x i) (i : ι) (t : ℝ) :
    ∀j,0 < Expr.logCurve x i t j := by
  intro j
  exact mul_pos (hx j) (Real.exp_pos _)

theorem log_product_insert_logCurve_continuousAt {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (I : Finset κ) (background : κ → ℝ) (hbackground : ∀i,0 < background i)
    (e : ι ≃ I) (x : ι → ℝ) (hx : ∀i,0 < x i) (i : ι) (keys : List κ) :
    ContinuousAt (fun t => Real.log ((keys.map
      (insert I background (fun j => Expr.logCurve x i t (e.symm j)))).prod)) 0 := by
  apply ContinuousAt.log
  · apply (continuous_list_prod keys ?_).continuousAt
    intro j hj
    unfold HistoryActiveCoordinates.insert
    split_ifs with hj
    · dsimp only [Expr.logCurve]
      split_ifs <;> fun_prop
    · fun_prop
  · apply (List.prod_pos ?_).ne'
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact insert_positive I background _ hbackground
      (fun j => logCurve_positive x hx i 0 (e.symm j)) j

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI
