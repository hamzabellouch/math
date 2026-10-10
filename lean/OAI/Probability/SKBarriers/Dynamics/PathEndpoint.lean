import Mathlib
import OAI.Probability.SKBarriers.Dynamics.GreedyRecursion

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

theorem walkWeight_last {n : ℕ} (β : ℝ) (J : Disorder n) (m : ℕ) (x : Config n) (f : Config n → ℝ) :
    (∑ s : Fin m → Config n,FiniteMarkov.walkWeight (heatBath β J) m x s*f ((Fin.cons x s : Fin (m+1) → Config n) (Fin.last m)))=
      ∑ y,discreteKernel β J m x y*f y := by
  induction m generalizing x with
  | zero => simp [FiniteMarkov.walkWeight,discreteKernel]
  | succ m ih =>
    rw [FiniteMarkov.sum_cons]
    have hlast : Fin.last (m+1)=(Fin.last m).succ := rfl
    simp only [FiniteMarkov.walkWeight_cons,hlast,Fin.cons_succ,mul_assoc,← Finset.mul_sum,ih,discreteKernel]
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem pathFiniteLaw_joint {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (m : ℕ) (f : Config n → Config n → ℝ) :
    (pathFiniteLaw hn β J m).expect (fun s => f (s 0) (s (Fin.last m)))=
      ∑ x,gibbs β J x*∑ y,discreteKernel β J m x y*f x y := by
  unfold FiniteLaw.expect pathFiniteLaw stationaryPathWeight
  rw [FiniteMarkov.sum_cons]
  simp only [FiniteMarkov.pathWeight,Fin.cons_zero,Fin.tail_cons,mul_assoc,← Finset.mul_sum,walkWeight_last]

namespace FiniteLaw
variable {X : Type*} [Fintype X]
theorem prob_mono_on_support (P : FiniteLaw X) {E F : X → Prop}
    (h : ∀x,0<P.weight x → E x → F x) : P.prob E ≤ P.prob F := by
  unfold prob expect
  apply Finset.sum_le_sum
  intro x _
  by_cases hw : 0<P.weight x
  · by_cases hE : E x
    · simp only [ite_eq_left hE,ite_eq_left (h x hw hE),le_refl]
    · simp only [ite_eq_right hE,mul_zero]
      split_ifs <;> positivity
  · have he : P.weight x=0 := le_antisymm (le_of_not_gt hw) (P.nonneg x)
    simp only [he,zero_mul,le_refl]
end FiniteLaw

def extendPath {n m : ℕ} (s : Fin (m+1) → Config n) (k : ℕ) : Config n :=
  if h : k ≤ m then s ⟨k,by omega⟩ else s 0

@[simp] theorem extendPath_at {n m : ℕ} (s : Fin (m+1) → Config n) (k : Fin (m+1)) :
    extendPath s k.val=s k := by simp only [extendPath,dite_eq_left (show k.val ≤ m by omega)]

theorem extendPath_jump {n m : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (s : Fin (m+1) → Config n) (hs : 0<(pathFiniteLaw hn β J m).weight s) :
    ∀ v k, k < m → |overlap v (extendPath s (k+1))-overlap v (extendPath s k)| ≤ 2/(n:ℝ) := by
  intro v k hk
  simp only [extendPath,dite_eq_left (show k+1 ≤ m by omega),dite_eq_left (show k ≤ m by omega)]
  exact stationaryPathWeight_pos_jump hn β J m s hs v ⟨k,hk⟩

theorem pathFiniteLaw_visit {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (m : ℕ) (V : Config n → Prop) :
    (pathFiniteLaw hn β J m).prob (fun s => ∃k : Fin (m+1),V (s k)) ≤ (m+1)*(gibbsFiniteLaw β J).prob V := by
  refine (FiniteLaw.prob_exists _ _).trans ?_
  have he (k : Fin (m+1)) : (pathFiniteLaw hn β J m).prob (fun s => V (s k))=(gibbsFiniteLaw β J).prob V :=
    pathFiniteLaw_marginal hn β J m k (fun x => if V x then 1 else 0)
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,le_refl]

def initialBankReference {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (t q : ℝ) (x : Config n) : Config n :=
  bankPick pool fallback B (fun _ => x) t q 0 fallback 0

@[simp] theorem initialBankReference_path {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (t q : ℝ) (x : ℕ → Config n) :
    initialBankReference pool fallback B t q (x 0)=bankPick pool fallback B x t q 0 fallback 0 := rfl

theorem stationary_sign_crossing_bound {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (v : Config n → Config n) (V : Config n → Prop)
    (hpath : ∀s : Fin (m+1) → Config n,0<(pathFiniteLaw hn β J m).weight s →
      (∀k : Fin (m+1),¬V (s k)) → 0<overlap (v (s 0)) (s (Fin.last m))) :
    (∑ x,gibbs β J x*∑ y,if overlap (v x) y ≤ 0 then discreteKernel β J m x y else 0)  ≤
      (m+1)*(gibbsFiniteLaw β J).prob V := by
  have HE : (∑ x,gibbs β J x*∑ y,if overlap (v x) y ≤ 0 then discreteKernel β J m x y else 0)=
      (pathFiniteLaw hn β J m).prob (fun s => overlap (v (s 0)) (s (Fin.last m)) ≤ 0) := by
    rw [FiniteLaw.prob,pathFiniteLaw_joint hn β J m (fun x y => if overlap (v x) y ≤ 0 then 1 else 0)]
    simp only [mul_ite,mul_one,mul_zero]
  rw [HE]
  refine (FiniteLaw.prob_mono_on_support _ (fun s hs hpass => ?_)).trans (pathFiniteLaw_visit hn β J m V)
  by_contra H
  have hgood : ∀k : Fin (m+1),¬V (s k) := by simpa only [not_exists] using H
  exact (not_lt_of_ge hpass) (hpath s hs hgood)

end SK.Analytic

end
end

end OAI
