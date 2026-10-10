import OAI.MeasureTheory.Falconer.Recursion.OrderedEndpointIntervals

namespace OAI

/-! Power accounting for the actual ordered-interval induction. -/
namespace Falconer
open Regularization

theorem list_prod_two_rpow {α : Type*} (S : List α) (e : α → ℝ) :
    (S.map fun c => (2:ℝ)^(e c)).prod = (2:ℝ)^((S.map e).sum) := by
  induction S with
  | nil => simp
  | cons c S ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,ih]
    exact (Real.rpow_add (by norm_num) _ _).symm

theorem profileEndpointBound_ordered_power {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (R : List (ℕ × ℕ)) (i j : ℕ) (hR : OrderedBlockIntervals i j R) (hi : i ≤ K)
    (e : ℕ × ℕ → ℝ) (W : ℕ → ℝ) (hW : ∀ k, 1 ≤ W k) (hWmono : Monotone W)
    (hWstep : ∀ k, W (k+1) = profileStepBudget (4*(N+2)+11:ℕ)
      ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) (W k))
    (hbase : ∀ c ∈ R, ProfileEndpointBound N B K L f p Q c.1 c.2 s (W (2*R.length)) ((2:ℝ)^(e c)))
    {target loss : ℝ} (hgain : target+loss ≤ (R.map e).sum)
    (hcost : (43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length) ≤ (2:ℝ)^loss) :
    ProfileEndpointBound N B K L f p Q i j s (W 0) ((2:ℝ)^target) := by
  have hh := profileEndpointBound_ordered_intervals hL f p Q hQ hs hs1 R i j hR hi
    (fun c => (2:ℝ)^(e c)) (fun _ _ => by positivity) W hW hWmono hWstep hbase
  apply hh.mono_value
  apply (le_div_iff₀ (show 0 < (43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length) by positivity)).2
  calc
    _ ≤ (2:ℝ)^target*(2:ℝ)^loss := mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = (2:ℝ)^(target+loss) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2:ℝ)^((R.map e).sum) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hgain
    _ = _ := (list_prod_two_rpow R e).symm

end Falconer

end OAI
