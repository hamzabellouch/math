import Mathlib
import OAI.Combinatorics.KMedian.Process.RoundWithCount
import OAI.Combinatorics.KMedian.Process.AdaptiveCount
import OAI.Combinatorics.KMedian.Reduction.CompletionEndpoint

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

theorem exists_final_law (A : Finset (Copy (F := F) Δ))
    (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) {b g h φ : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b)
    (hp1 : (1+φ)*(2*h*g) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hsurv : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1)
    (hcount : 8*(2*h*g)*(Δ:ℝ) ≤ φ*g)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hmax : ∀ j, ∃ i ∈ S₀ j, R j=dist (client j) (location i.1))
    (hA : 1 ≤ mass g A) (hS : ∀ j, S₀ j ⊆ A) (T : ℕ) :
    ∃ ν : FiniteLaw (State F J Δ),
      (∀ s, 0 < ν.weight s → Valid g location client R S₀ s) ∧
      (ν.prob (fun s => mass g A+(T:ℝ)*(4/(g*b)) < mass g s.1) ≤
        (T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g))) ∧
      (∀ j, ν.expect (fun s => mass g (s.2 j)) ≤ Real.exp (-(T:ℝ)*h/2)) ∧
      ∀ j, ν.expect (fun s => statePotential R (fun j f => dist (client j) (location f))
          (Real.exp (-(T:ℝ)*h)) g s j) ≤
        (1+2/Real.exp 1)*PhysicalPotential.cost g (fun i => dist (client j) (location i.1)) (S₀ j)+
        (T:ℝ)*(h*g*PhysicalPotential.cost g (fun i => dist (client j) (location i.1)) (S₀ j)+
          batchConstant Δ*h*(φ+h)*R j) := by
  classical
  let s₀ : State F J Δ := (A,S₀)
  let valid := Valid g location client R S₀
  let d := fun j f => dist (client j) (location f)
  let x := fun n : ℕ => Real.exp (-(n:ℝ)*h)
  let err := fun j => h*g*PhysicalPotential.cost g (fun i => d j i.1) (S₀ j)+
    batchConstant Δ*h*(φ+h)*R j
  let ρ := 96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g)
  have hx0 : ∀ n, 0 ≤ x n := fun _ => (Real.exp_pos _).le
  have hx1 : ∀ n, x n ≤ 1 := fun n => Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hh.le)
  have hxs : ∀ n, x (n+1)=x n*Real.exp (-h) := by
    intro n
    dsimp only [x]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hex : ∀ n s, ∃ ν : FiniteLaw (State F J Δ), valid s →
      (∀ t, 0 < ν.weight t → valid t) ∧
      (∀ j, ν.expect (fun t => mass g (t.2 j)) ≤ (1-h/2)*mass g (s.2 j)) ∧
      (ν.prob (fun t => mass g s.1+4/(g*b) < mass g t.1) ≤ ρ) ∧
      ∀ j, ν.expect (fun t => statePotential R d (x (n+1)) g t j) ≤
        statePotential R d (x n) g s j+err j := by
    intro n s
    by_cases hv : valid s
    · obtain ⟨ν,hvν,hyν,hcν,hfν⟩ := exists_round_with_count s S₀ location client R b hg hg1 hunit
        (hx0 n) (hx1 n) hh.le hh1 hφ.le hφ1 hh hφ hb hcount hp1 hsmall hsurv hR hm hd hmax hv
      refine ⟨ν,fun _ => ⟨hvν,hyν,hcν,fun j => ?_⟩⟩
      rw [hxs]
      apply (hfν j).trans
      have hcost := cost_mono hg.le (d := fun i : Copy (F := F) Δ => d j i.1)
        (fun _ _ => dist_nonneg) (hv.2.2.1 j)
      have hs := mul_le_mul_of_nonneg_left hcost (show 0 ≤ h*g by positivity)
      change _ ≤ statePotential R d (x n) g s j+err j
      dsimp only [err,d] at hs ⊢
      linarith only [hs]
    · exact ⟨FiniteLaw.dirac s, fun hs => (hv hs).elim⟩
  choose K hK using hex
  let ν := FiniteLaw.run (FiniteLaw.dirac s₀) K T
  have hvalid : ∀ n s, 0 < (FiniteLaw.run (FiniteLaw.dirac s₀) K n).weight s → valid s := by
    apply FiniteLaw.run_invariant _ _ (fun _ => valid)
    · intro s hs
      by_cases he : s=s₀
      · subst s
        exact valid_initial A S₀ g location client R hA hS
      · simp only [FiniteLaw.dirac,ite_eq_right he] at hs
        exact (lt_irrefl _ hs).elim
    · intro n s hs
      exact (hK n s hs).1
  refine ⟨ν,hvalid T,?_,?_,?_⟩
  · exact FiniteLaw.run_count_tail s₀ K (fun s => mass g s.1)
      (show 0 ≤ ρ by dsimp [ρ]; positivity) (fun n s hs => (hK n s (hvalid n s hs)).2.2.1) T
  · intro j
    have ht := FiniteLaw.run_survival (FiniteLaw.dirac s₀) K (fun _ s => mass g (s.2 j))
      (h := h) (Λ := (T:ℝ)*h) (by linarith only [hh1]) (by simpa only [FiniteLaw.expect_dirac] using hm j)
      (le_refl _) (fun n s hs => (hK n s (hvalid n s hs)).2.1 j)
    simpa only [neg_mul] using ht
  · intro j
    have ht := FiniteLaw.run_drift (FiniteLaw.dirac s₀) K (fun n s => statePotential R d (x n) g s j)
      (fun _ => err j) (fun n s hs => (hK n s (hvalid n s hs)).2.2.2 j) T
    simpa only [FiniteLaw.expect_dirac,x,Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,
      s₀,initial_potential A S₀ R d hm j,sum_const,card_range,nsmul_eq_mul] using ht

end MetricKMedian.CopyState
end
end

end OAI
