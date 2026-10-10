import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartStages

namespace OAI

/-! # Restart accuracy from only the learned multiplier prefix

The horizon controls the fixed mixing schedule. Goodness is required only
at the parameters which the actual restart has visited.
-/

namespace ContingencyTables.RootedRestartPrefix

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates RootedAnnealing RootedWarmStart RootedTargetTrace
open RootedTargetMixing RootedWarmReturn RootedReturnIteration RootedRestartStages
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

private lemma accumulate (j : ℕ) (r s u e : ℝ)
    (hr : r ≤ s+e) (hs : s ≤ u+(j:ℝ)*e) :
    r ≤ u+((j+1:ℕ):ℝ)*e := by
  push_cast
  linarith

theorem reference_two_warm_at (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (j : ℕ) (hj : j ≤ H)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w j p q:ℝ)))
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
      hgood (reference A R H L hp w hw j)
      (reference_nonnegative A R H L hp w hw j)
      (reference_mass A R H L hp w hw j).le S

theorem reference_next_four_warm_at (A : Instance I J) (R : RootedCompletion.Selection A.T) (H L : ℕ)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ j p q,0 < w j p q)
    (j : ℕ) (hj : j ≤ H)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w j p q:ℝ)))
    (S : PlainIndex (pairs : List (Pair A))) :
    reference A R H L hp w hw j S ≤ 4*law A R (j+1) S.val.val := by
  have h := reference_two_warm_at A R H L hbox hp w hw j hj hgood S
  have ha := law_adjacent A R j S.val.val
  linarith

theorem implemented_distance_prefix (A : Instance I J) (R : RootedCompletion.Selection A.T)
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
    (hn : 0 < n)
    (initial : PlainIndex (pairs : List (Pair A)) → ℝ) (j : ℕ) (hj : j ≤ H)
    (hgood : ∀ i,i ≤ j → GoodMultipliers pairs (weight A R i)
      (fun p q => (w i p q:ℝ))) :
    distance (implemented A R C K H L k n hK hW xi v w initial j)
      (reference A R H L hp w hw j) ≤
      distance initial (fun S => law A R 0 S.val.val)+
      (j:ℝ)*((restartTime A H L:ℝ)*
        ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))) := by
  revert hj hgood
  induction j with
  | zero =>
    intro _ _
    simp only [implemented,reference,Nat.cast_zero,zero_mul,add_zero]
    exact le_rfl
  | succ j ih =>
    intro hj hgood
    have hj0 : j ≤ H := by omega
    have hs := repeated_return_distance A R C hC K (j+1) k n hK hW hB
      (hj.trans hH) xi hx0 hx1 hPL hCheeger v hp (w (j+1)) (hw (j+1))
      (hgood (j+1) le_rfl) hn (reference A R H L hp w hw j)
      (reference_nonnegative A R H L hp w hw j)
      (reference_mass A R H L hp w hw j).le 4 (by norm_num)
      (reference_next_four_warm_at A R H L hbox hp w hw j hj0 (hgood j (Nat.le_succ j)))
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
    have hprev := ih hj0 (fun i hi => hgood i (hi.trans (Nat.le_succ j)))
    rw [show 5*(Fintype.card (Labels A):ℝ)^2*4=
      20*(Fintype.card (Labels A):ℝ)^2 by ring] at hs
    have hsum := _root_.add_le_add hc hs
    have hstep := ht.trans hsum
    exact accumulate j _ _ _ _ hstep hprev


end
end ContingencyTables.RootedRestartPrefix

end OAI
