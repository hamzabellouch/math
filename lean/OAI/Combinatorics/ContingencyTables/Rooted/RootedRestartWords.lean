import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartPrefix
import OAI.Combinatorics.ContingencyTables.Machines.FiniteVaryingWordWalk

namespace OAI

/-! # Actual finite Boolean words for all successive restart stages -/

namespace ContingencyTables.RootedRestartWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open CompanionTargetMixing (restartTime)
open CompanionReturnWords (returnBits)
open RootedReturnWords RootedWarmStart RootedRestartStages RootedRestartPrefix
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def stageWidth (A : Instance I J) (C K H L k n : ℕ) (xi : ℚ) (i : ℕ) : ℕ :=
  returnBits A C K (i+1) k n (restartTime A H L) xi

def stageStep (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ) (i : ℕ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (stageWidth A C K H L k n xi i) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  booleanReturns A R C K (i+1) k n (restartTime A H L) hK hW xi v (w (i+1)) S bits

def stages (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (∑ i : Fin j,stageWidth A C K H L k n xi i.val) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  varyingWalk (stageWidth A C K H L k n xi)
    (stageStep A R C K H L k n hK hW xi v w) S j
    (varyingWordEquiv (stageWidth A C K H L k n xi) j bits)

theorem stages_law (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    mapLaw (uniformLaw (α := Fin (∑ i : Fin j,stageWidth A C K H L k n xi i.val) → Bool))
      (stages A R C K H L k n j hK hW xi v w S)=
      varyingLaw (stageWidth A C K H L k n xi)
        (stageStep A R C K H L k n hK hW xi v w) (pointLaw S) j :=
  flatVaryingWalk_law _ _ S j

private lemma stageStep_law (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (i : ℕ) (S : PlainIndex (pairs : List (Pair A))) :
    mapLaw (uniformLaw (α := Fin (stageWidth A C K H L k n xi i) → Bool))
      (stageStep A R C K H L k n hK hW xi v w i S)=
      booleanReturnsLaw A R C K (i+1) k n (restartTime A H L) hK hW xi v (w (i+1)) S := by
  rfl

theorem stageLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (p : RationalLaw (PlainIndex (pairs : List (Pair A)))) (j : ℕ)
    (T : PlainIndex (pairs : List (Pair A))) :
    ((varyingLaw (stageWidth A C K H L k n xi)
      (stageStep A R C K H L k n hK hW xi v w) p j).mass T:ℝ)=
      implemented A R C K H L k n hK hW xi v w (fun S => (p.mass S:ℝ)) j T := by
  induction j generalizing T with
  | zero => rfl
  | succ j ih =>
    simp only [varyingLaw,stageStep_law,bindLaw,Rat.cast_sum,Rat.cast_mul,
      ih,booleanReturnsLaw_cast,implemented,FiniteKernel.push]

def initialStageBits (A : Instance I J) (C K H L k n h j : ℕ) (xi : ℚ) : ℕ :=
  CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A h)+
    ∑ i : Fin j,stageWidth A C K H L k n xi i.val

def initializedStages (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n h j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (bits : Fin (initialStageBits A C K H L k n h j xi) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  let z := splitWordEquiv (CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A h))
    (∑ i : Fin j,stageWidth A C K H L k n xi i.val) bits
  stages A R C K H L k n j hK hW xi v w
    (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h) z.1) z.2

theorem initializedStages_law (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n h j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ) :
    mapLaw (uniformLaw (α := Fin (initialStageBits A C K H L k n h j xi) → Bool))
      (initializedStages A R C K H L k n h j hK hW xi v w)=
      varyingLaw (stageWidth A C K H L k n xi)
        (stageStep A R C K H L k n hK hW xi v w)
        (mapLaw (uniformLaw (α := Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A h)) → Bool))
          (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h))) j := by
  let r := CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A h)
  let s := ∑ i : Fin j,stageWidth A C K H L k n xi i.val
  let init := CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h)
  let run := stages A R C K H L k n j hK hW xi v w
  change mapLaw (uniformLaw (α := Fin (r+s) → Bool))
    (fun bits => run (init (splitWordEquiv r s bits).1) (splitWordEquiv r s bits).2)=_
  have he := map_equiv (splitWordEquiv r s)
    (uniformLaw (α := Fin (r+s) → Bool)) (fun z => run (init z.1) z.2)
  rw [uniform_equiv,←uniform_product] at he
  refine he.symm.trans ?_
  rw [mapLaw_product_finish]
  dsimp only [run]
  have hf : (fun x => mapLaw (uniformLaw (α := Fin s → Bool))
      (stages A R C K H L k n j hK hW xi v w x))=
      (fun x => varyingLaw (stageWidth A C K H L k n xi)
        (stageStep A R C K H L k n hK hW xi v w) (pointLaw x) j) := by
    funext x
    exact stages_law A R C K H L k n j hK hW xi v w x
  have heq := congrArg (fun F : PlainIndex (pairs : List (Pair A)) →
      RationalLaw (PlainIndex (pairs : List (Pair A))) =>
        bindLaw (mapLaw (uniformLaw (α := Fin r → Bool)) init) F) hf
  exact heq.trans (varyingLaw_start _ _ _ _)

/-- The actual initialized finite word is close to the exact warm
restart reference; it includes every fresh stage and initializer word. -/
theorem initializedStages_distance (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K H L k n h j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hH : H ≤ rationalHeight A C)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : ℕ → Pair A → Pair A → ℚ) (hw : ∀ i p q,0 < w i p q)
    (hgood : ∀ i,i ≤ j → GoodMultipliers pairs (RootedAnnealing.weight A R i)
      (fun p q => (w i p q:ℝ))) (hn : 0 < n) (hj : j ≤ H) :
    distance (fun T => ((mapLaw (uniformLaw
      (α := Fin (initialStageBits A C K H L k n h j xi) → Bool))
      (initializedStages A R C K H L k n h j hK hW xi v w)).mass T:ℝ))
      (reference A R H L hp w hw j) ≤ 1/(2:ℝ)^h+
        (j:ℝ)*((restartTime A H L:ℝ)*((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))) := by
  rw [initializedStages_law]
  simp_rw [stageLaw_cast]
  let initial : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ((mapLaw (uniformLaw (α := Fin (CompanionInitialDraw.initialBits A
      (CompanionInitialDraw.precision A h)) → Bool))
      (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h))).mass S:ℝ)
  have h0 : distance initial (fun S => law A R 0 S.val.val) ≤ 1/(2:ℝ)^h :=
    initial_distance A R h
  have hh := implemented_distance_prefix A R C hC K H L k n hK hW hB hH hbox xi hx0 hx1
    hPL hCheeger v hp w hw hn initial j hj hgood
  have hadd := _root_.add_le_add h0 (le_refl ((j:ℝ)*((restartTime A H L:ℝ)*
    ((20*(Fintype.card (Labels A):ℝ)^2)/(n:ℝ)+
      ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)))))
  have hb := hh.trans hadd
  simpa only [initial] using hb

end
end ContingencyTables.RootedRestartWords

end OAI
