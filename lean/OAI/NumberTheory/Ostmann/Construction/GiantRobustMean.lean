import OAI.NumberTheory.Ostmann.Construction.GiantBlockError

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

def giantRobustMean (d : Decomposition) (X p : ℕ) : ℝ :=
  giantSupportMean d p-2*|giantEmpiricalMean d X p-giantSupportMean d p|

theorem eventually_robust_favorable_mean (d : Decomposition) {δ : ℝ} (hδ : 0<δ)
    (r : ℝ) (hr : 4≤r) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ, ∀ P : Finset ℕ,
      Real.exp ((1/20:ℝ)*L)≤G → G≤Real.exp ((9/10:ℝ)*L) →
      P⊆Supply.nonsparsePrimes d δ L →
      (∀p∈P,G≤Real.log p ∧ Real.log p≤G+favorableBlockWidth L) →
      (1/10:ℝ)*favorableBlockWidth L≤primeLogMass P →
      (δ/(20*Real.sqrt 2))*favorableBlockWidth L≤
        ∑p∈P,(Real.log p/(p:ℝ))*giantRobustMean d (giantWindowScale r G L) p := by
  let a := δ/(20*Real.sqrt 2)
  have ha : 0<a := div_pos hδ (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
  filter_upwards [eventually_giant_block_error d (ε := a/2) (by positivity) r hr]
    with L herror
  intro G P hGlo hGhi hP hwindow hmass
  let X := giantWindowScale r G L
  let h := favorableBlockWidth L
  have hprime (p : ℕ) (hp : p∈P) : p.Prime := (Finset.mem_filter.mp (hP hp)).2.1
  have he := herror G P hGlo hGhi hprime hwindow
  have hs : (δ/Real.sqrt 2)*primeLogMass P≤
      ∑p∈P,(Real.log p/(p:ℝ))*giantSupportMean d p := by
    unfold primeLogMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have ht := (Finset.mem_filter.mp (hP hp)).2
    have hl := giantSupportMean_lower d ht.1 hδ.le ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2
    have hw : 0≤Real.log p/(p:ℝ) := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl hw
  have hcoef : 0≤δ/Real.sqrt 2 := (div_pos hδ (Real.sqrt_pos.mpr (by norm_num))).le
  have hl := mul_le_mul_of_nonneg_left hmass hcoef
  have hconst : (δ/Real.sqrt 2)*((1/10:ℝ)*h)=2*a*h := by dsimp [a]; ring
  rw [hconst] at hl
  have heq : (∑p∈P,(Real.log p/(p:ℝ))*giantRobustMean d X p)=
      (∑p∈P,(Real.log p/(p:ℝ))*giantSupportMean d p)-
      2*(∑p∈P,(Real.log p/(p:ℝ))*|giantEmpiricalMean d X p-giantSupportMean d p|) := by
    simp only [giantRobustMean,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  change a*h≤∑p∈P,(Real.log p/(p:ℝ))*giantRobustMean d X p
  rw [heq]
  linarith

end Ostmann.Construction

end

end OAI
