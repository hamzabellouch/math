import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! Fixing all but k variables in the complete system leaves at most k!
solutions. This elementary fiber estimate is the initial counting bound
before the translation and differencing steps. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_vinogradov_tail_fiber {k r N : ℕ}
    (x : Fin (k+r) → Fin N) (z : Fin r → Fin N) :
    ((halaszVinogradovFiber x k).filter
      (fun y => (fun i : Fin r => y (i.natAdd k)) = z)).card ≤ k.factorial := by
  classical
  let A := halaszVinogradovFiber x k
  let pre : (Fin (k+r) → Fin N) → (Fin k → Fin N) :=
    fun y i => y (i.castAdd r)
  let tail : (Fin (k+r) → Fin N) → (Fin r → Fin N) :=
    fun y i => y (i.natAdd k)
  let B := A.filter (fun y => tail y=z)
  change B.card ≤ k.factorial
  by_cases hb : B.Nonempty
  · obtain ⟨w,hw⟩ := hb
    have hinj : Set.InjOn pre (B : Set (Fin (k+r) → Fin N)) := by
      intro y hy v hv he
      have ht : tail y=tail v := (mem_filter.mp hy).2.trans (mem_filter.mp hv).2.symm
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · exact congrFun he j
      · exact congrFun ht j
    have hsub : B.image pre ⊆ halaszVinogradovFiber (pre w) k := by
      intro v hv
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
      apply mem_halaszVinogradovFiber.mpr
      intro j hj
      have hyA := (mem_filter.mp hy).1
      have hwA := (mem_filter.mp hw).1
      have ht : tail w=tail y := (mem_filter.mp hw).2.trans (mem_filter.mp hy).2.symm
      have hp := ((mem_halaszVinogradovFiber.mp hwA) j hj).symm.trans
        ((mem_halaszVinogradovFiber.mp hyA) j hj)
      rw [Fin.sum_univ_add,Fin.sum_univ_add] at hp
      have htail : (∑ i : Fin r, ((w (i.natAdd k)).val+1)^j) =
          ∑ i : Fin r, ((y (i.natAdd k)).val+1)^j := by
        apply sum_congr rfl
        intro i _
        rw [show w (i.natAdd k)=y (i.natAdd k) from congrFun ht i]
      rw [htail] at hp
      exact Nat.add_right_cancel hp
    calc
      B.card = (B.image pre).card := (card_image_of_injOn hinj).symm
      _ ≤ (halaszVinogradovFiber (pre w) k).card := card_le_card hsub
      _ ≤ k.factorial := halasz_vinogradov_fiber_card le_rfl _
  · simp only [not_nonempty_iff_eq_empty.mp hb,card_empty]
    exact Nat.zero_le _

theorem halasz_vinogradov_general_fiber {k r N : ℕ} (x : Fin (k+r) → Fin N) :
    (halaszVinogradovFiber x k).card ≤ N^r*k.factorial := by
  classical
  calc
    _ = ∑ z : Fin r → Fin N, ((halaszVinogradovFiber x k).filter
        (fun y => (fun i : Fin r => y (i.natAdd k)) = z)).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _z : Fin r → Fin N, k.factorial :=
      sum_le_sum (fun z _ => halasz_vinogradov_tail_fiber x z)
    _ = _ := by simp

/-- The elementary complete-system bound, valid before mean-value iteration. -/
theorem halasz_vinogradov_initial_bound (k r N : ℕ) :
    halaszVinogradovCount (k+r) k N ≤ N^(k+2*r)*k.factorial := by
  classical
  unfold halaszVinogradovCount
  calc
    _ ≤ ∑ _x : Fin (k+r) → Fin N, N^r*k.factorial :=
      sum_le_sum (fun x _ => halasz_vinogradov_general_fiber x)
    _ = _ := by simp [← mul_assoc,← pow_add,show k+r+r=k+2*r by omega]

end TwoPointCorrelations

end OAI
