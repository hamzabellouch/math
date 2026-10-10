import OAI.Combinatorics.ContingencyTables.Rooted.RootedReturnWords

namespace OAI

/-! # Successive selected-root restart stages

The reference law is refreshed by the exact trace at each successive
parameter. Only that reference law is asserted to be warm. The actual
bounded-return law is compared to it by contraction and accumulated error.
-/

namespace ContingencyTables.RootedRestartStages

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates RootedAnnealing RootedWarmStart RootedTargetTrace
open RootedTargetMixing RootedWarmReturn RootedReturnIteration
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma accumulate (j : ℕ) (r s u e : ℝ)
    (hr : r ≤ s+e) (hs : s ≤ u+(j:ℝ)*e) :
    r ≤ u+((j+1:ℕ):ℝ)*e := by
  push_cast
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

def reference (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q) :
    ℕ → PlainIndex (pairs : List (Pair A)) → ℝ
  | 0 => fun S => law A R 0 S.val.val
  | j+1 => ((actualTrace A R (j+1) hp (w (j+1)) (hw (j+1))).kernel.power
      (restartTime A H L)).push (reference A R H L hp w hw j)

lemma reference_nonnegative (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q) (j : ℕ) :
    ∀ S,0 ≤ reference A R H L hp w hw j S := by
  induction j with
  | zero =>
    intro S
    exact (div_pos (weight_positive A R 0 _) (total_positive A R 0)).le
  | succ j ih =>
    exact ((actualTrace A R (j+1) hp (w (j+1)) (hw (j+1))).kernel.power
      (restartTime A H L)).push_nonneg _ ih

lemma reference_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q) (j : ℕ) :
    ∑ S,reference A R H L hp w hw j S=1 := by
  induction j with
  | zero =>
    exact (by simpa only [reference,actualTrace_pi] using
      (actualTrace A R 0 hp (w 0) (hw 0)).normalized)
  | succ j ih =>
    change ∑ S,((actualTrace A R (j+1) hp (w (j+1)) (hw (j+1))).kernel.power
      (restartTime A H L)).push (reference A R H L hp w hw j) S=1
    rw [FiniteChain.power_push_mass]
    exact ih

theorem reference_two_warm (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (hgood : ∀ j,j ≤ H → GoodMultipliers pairs (weight A R j)
      (fun p q => (w j p q:ℝ))) (j : ℕ) (hj : j ≤ H)
    (S : PlainIndex (pairs : List (Pair A))) :
    reference A R H L hp w hw j S ≤ 2*law A R j S.val.val := by
  cases j with
  | zero =>
    change law A R 0 S.val.val ≤ 2*law A R 0 S.val.val
    have h := div_pos (weight_positive A R 0 S.val.val) (total_positive A R 0)
    change 0 < law A R 0 S.val.val at h
    linarith
  | succ j =>
    exact restart_warm A R H L (j+1) hj hbox hp (w (j+1)) (hw (j+1))
      (hgood (j+1) hj) (reference A R H L hp w hw j)
      (reference_nonnegative A R H L hp w hw j)
      (reference_mass A R H L hp w hw j).le S

theorem reference_next_four_warm (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (hgood : ∀ j,j ≤ H → GoodMultipliers pairs (weight A R j)
      (fun p q => (w j p q:ℝ))) (j : ℕ) (hj : j ≤ H)
    (S : PlainIndex (pairs : List (Pair A))) :
    reference A R H L hp w hw j S ≤ 4*law A R (j+1) S.val.val := by
  have h := reference_two_warm A R H L hbox hp w hw hgood j hj S
  have ha := law_adjacent A R j S.val.val
  linarith

def implemented (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (w : ℕ → Pair A → Pair A → ℚ)
    (initial : PlainIndex (pairs : List (Pair A)) → ℝ) :
    ℕ → PlainIndex (pairs : List (Pair A)) → ℝ
  | 0 => initial
  | j+1 => ((returnKernel A R C K (j+1) k n hK hW xi v (w (j+1))).power
      (restartTime A H L)).push (implemented A R C K H L k n hK hW xi v w initial j)

/-- Every new stage starts from a four-warm exact reference. Errors of
the actual bounded-word implementation add, without conditioning on a
successful return or requiring its incoming distribution to be warm. -/
theorem implemented_distance (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K H L k n : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (hH : H ≤ CompanionOracleDensity.rationalHeight A C)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (CompanionOracleDensity.dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger
      (Grid (I := Fin (CompanionOracleDensity.dimension A)) K))
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (hgood : ∀ j,j ≤ H → GoodMultipliers pairs (weight A R j)
      (fun p q => (w j p q:ℝ))) (hn : 0 < n)
    (initial : PlainIndex (pairs : List (Pair A)) → ℝ) (j : ℕ) (hj : j ≤ H) :
    distance (implemented A R C K H L k n hK hW xi v w initial j)
      (reference A R H L hp w hw j) ≤
      distance initial (fun S => law A R 0 S.val.val)+
      (j:ℝ)*((restartTime A H L:ℝ)*
        ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))) := by
  revert hj
  induction j with
  | zero =>
    intro _
    simp only [implemented,reference,Nat.cast_zero,zero_mul,add_zero]
    exact le_rfl
  | succ j ih =>
    intro hj
    have hj0 : j ≤ H := by omega
    have hs := repeated_return_distance A R C hC K (j+1) k n hK hW hB
      (hj.trans hH) xi hx0 hx1 hPL hCheeger v hp (w (j+1)) (hw (j+1))
      (hgood (j+1) hj) hn (reference A R H L hp w hw j)
      (reference_nonnegative A R H L hp w hw j)
      (reference_mass A R H L hp w hw j).le 4 (by norm_num)
      (reference_next_four_warm A R H L hbox hp w hw hgood j hj0)
      (restartTime A H L)
    have hc := distance_push
      ((returnKernel A R C K (j+1) k n hK hW xi v (w (j+1))).power (restartTime A H L))
      (implemented A R C K H L k n hK hW xi v w initial j)
      (reference A R H L hp w hw j)
    have ht := distance_triangle
      (implemented A R C K H L k n hK hW xi v w initial (j+1))
      (((returnKernel A R C K (j+1) k n hK hW xi v (w (j+1))).power
        (restartTime A H L)).push (reference A R H L hp w hw j))
      (reference A R H L hp w hw (j+1))
    have hprev := ih hj0
    rw [show 5*(Fintype.card (Labels A):ℝ)^2*4=
      20*(Fintype.card (Labels A):ℝ)^2 by ring] at hs
    have hsum := _root_.add_le_add hc hs
    have hstep := ht.trans hsum
    exact accumulate j _ _ _ _ hstep hprev

end
end ContingencyTables.RootedRestartStages

end OAI
