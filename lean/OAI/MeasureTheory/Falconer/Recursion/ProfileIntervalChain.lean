import OAI.MeasureTheory.Falconer.Recursion.ProfileScaleInduction

namespace OAI

/-! Finite composition of actual profile interval estimates. Every splitting
step uses the proved endpoint construction and its explicit next budget. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

noncomputable def profileBudgetSequence (H G W : ℝ) : ℕ → ℝ
  | 0 => W
  | n+1 => profileStepBudget H G (profileBudgetSequence H G W n)

theorem profileBudgetSequence_one_le {H G W : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) (n : ℕ) :
    1 ≤ profileBudgetSequence H G W n := by
  induction n with
  | zero => exact hW
  | succ n ih => exact ih.trans (profile_step_budget_bounds hH hG ih).1

theorem profileBudgetSequence_monotone {H G W : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    Monotone (profileBudgetSequence H G W) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (profile_step_budget_bounds hH hG (profileBudgetSequence_one_le hH hG hW n)).1

theorem profileEndpointBound_interval_chain {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (n : ℕ) (v : ℕ → ℕ) (hv : Antitone v) (hvK : v 0 ≤ K)
    (F W : ℕ → ℝ) (hF : ∀ k < n, 0 ≤ F k) (hW : ∀ k, 1 ≤ W k)
    (hWmono : Monotone W)
    (hWstep : ∀ k, W (k+1) = profileStepBudget (4*(N+2)+11:ℕ)
      ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) (W k))
    (hbase : ∀ k < n, ProfileEndpointBound N B K L f p Q (v k) (v (k+1)) s (W n) (F k)) :
    ProfileEndpointBound N B K L f p Q (v 0) (v n) s (W 0)
      ((∏ k ∈ Finset.range n, F k)/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^n) := by
  induction n generalizing v F W with
  | zero => simpa using profileEndpointBound_trivial N B K L f p Q (v 0) (v 0) s (W 0)
  | succ n ih =>
    have hv1 : v 1 ≤ K := (hv (by omega : 0 ≤ 1)).trans hvK
    have hfirst := (hbase 0 (by omega)).mono_budget (hWmono (by omega : 1 ≤ n+1))
    have htail := ih (fun k => v (k+1)) (fun a b hab => hv (Nat.add_le_add_right hab 1)) hv1
      (fun k => F (k+1)) (fun k => W (k+1)) (fun k hk => hF (k+1) (by omega))
      (fun k => hW (k+1)) (fun a b hab => hWmono (Nat.add_le_add_right hab 1))
      (fun k => hWstep (k+1)) (fun k hk => hbase (k+1) (by omega))
    have htail0 : 0 ≤ (∏ k ∈ Finset.range n, F (k+1))/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^n := by
      apply div_nonneg (Finset.prod_nonneg fun k hk => hF (k+1) (by have := Finset.mem_range.mp hk; omega))
      positivity
    rw [hWstep 0] at hfirst htail
    have hh := profileEndpointBound_split hL f p Q hQ (hv (by omega : 1 ≤ n+1))
      (hv (by omega : 0 ≤ 1)) hvK hs hs1 (hW 0) (hF 0 (by omega)) htail0 hfirst htail
    have he : F 0*((∏ k ∈ Finset.range n, F (k+1))/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^n)/
        (43264*((4*(N+2)+11:ℕ):ℝ)^4) =
        (∏ k ∈ Finset.range (n+1), F k)/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(n+1) := by
      rw [Finset.prod_range_succ',pow_succ]
      ring
    simpa only [he] using hh

end Falconer

end OAI
