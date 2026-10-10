import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments
import OAI.Combinatorics.KMedian.Probability.FiniteClipping
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw
import OAI.Combinatorics.KMedian.Sparse.SparseOuterLaw

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open SparseGridRounding (base)
open SparseSignedPreparation (State)
variable {n m : ℕ}

def targetMean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (i : Fin n) : ℚ :=
  ∑ e, if i∈D e then q e else 0

def deficit (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (g : ℚ)
    (z : State n m) (i : Fin n) : ℚ := g*∑ e, activation D q z e i

theorem activation_real_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ))=
      ((if i∈D e then q e else 0:ℚ):ℝ) := by
  exact ((law D c q hc hq).realIndex_expect (fun z => activation D q z e i)).trans
    (congrArg (fun x : ℚ => (x:ℝ)) (activation_mean D c q hc hq e i))

theorem activation_real_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a =>
      (activation D q (law D c q hc hq).states[a.val] e i:ℝ)*
        (activation D q (law D c q hc hq).states[a.val] f j:ℝ)) ≤
      ((if i∈D e then q e else 0:ℚ):ℝ)*((if j∈D f then q f else 0:ℚ):ℝ) := by
  have hh := activation_pair D c q hc hq e f hef i j
  have he := SparseIntegerLaw.realIndex_expect (law D c q hc hq)
    (fun z => activation D q z e i*activation D q z f j)
  simp only [Rat.cast_mul] at he
  rw [he]
  exact_mod_cast hh

theorem activation_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).realIndex.variance
      (fun a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ)) ≤
      ((if i∈D e then q e else 0:ℚ):ℝ) := by
  apply FiniteLaw.adjacent_variance _ _
    (m := ((if i∈D e then (base q e:ℚ) else 0:ℚ):ℝ)) ?_ ?_
    (activation_real_mean D c q hc hq e i)
  · split_ifs <;> positivity
  · intro a _
    rcases activation_adjacent D c q hc hq a e i with hh | hh
    · exact Or.inl (by exact_mod_cast hh)
    · exact Or.inr (by exact_mod_cast hh)

theorem deficit_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (i : Fin n) :
    (law D c q hc hq).realIndex.expect (fun a => (deficit D q g (law D c q hc hq).states[a.val] i:ℝ))=
      (g:ℝ)*(targetMean D q i:ℝ) := by
  simp only [deficit,Rat.cast_mul,Rat.cast_sum,FiniteLaw.expect_mul,FiniteLaw.expect_sum,
    activation_real_mean,targetMean]

theorem deficit_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (i : Fin n) :
    (law D c q hc hq).realIndex.variance (fun a => (deficit D q g (law D c q hc hq).states[a.val] i:ℝ)) ≤
      (g:ℝ)^2*(targetMean D q i:ℝ) := by
  have hh := FiniteLaw.variance_sum_le (law D c q hc hq).realIndex
    (fun e a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ))
    (fun e => ((if i∈D e then q e else 0:ℚ):ℝ))
    (fun e => ((if i∈D e then q e else 0:ℚ):ℝ))
    (fun e => activation_real_mean D c q hc hq e i)
    (fun e => activation_variance D c q hc hq e i)
    (fun e f hef => activation_real_pair D c q hc hq e f hef i i)
  simp only [deficit,Rat.cast_mul,Rat.cast_sum,FiniteLaw.variance_mul,targetMean]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)

theorem clipping_budget (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (δ : Fin n → ℝ) {γ : ℝ} (hg : 0 ≤ g) (hγ : 0 < γ) (hδ : ∀ i, 0 ≤ δ i)
    (hmean : ∀ i, (g:ℝ)*(targetMean D q i:ℝ)=(1+γ)*δ i)
    (hsmall : ∀ i, (1+γ)*δ i ≤ 1/4) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (law D c q hc hq).realIndex.prob (fun a =>
      (∑ i, ((deficit D q g (law D c q hc hq).states[a.val] i:ℝ)-
        min (deficit D q g (law D c q hc hq).states[a.val] i:ℝ) (1/2))) ≤ γ*∑ i,δ i) := by
  classical
  apply FiniteLaw.clipping_budget _ _ δ (by exact_mod_cast hg) hγ hδ
  · intro i
    rw [deficit_mean,hmean]
    exact hsmall i
  · intro i
    have hh := deficit_variance D c q g hc hq i
    have he : (g:ℝ)^2*(targetMean D q i:ℝ)=(g:ℝ)*(1+γ)*δ i := by
      rw [pow_two,mul_assoc,hmean]
      ring
    exact hh.trans_eq he

end MetricKMedian.SparseOuterLaw
end
end

end OAI
