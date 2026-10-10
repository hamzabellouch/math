import OAI.Combinatorics.ContingencyTables.Rooted.RootedBooleanKernel
import OAI.Combinatorics.ContingencyTables.Machines.FiniteTraceSlowdown

namespace OAI

/-! # Actual selected-root dyadic phase concentration -/

namespace ContingencyTables.RootedSlowConcentration

open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing RootedMultiplierUpdate
open RootedBooleanPhase CompanionRationalUpdates TwoLiftStates ObservableBounds
open RootedWarmStart (actual_degree)
open CompanionConcentration (pairs_ne_nil square_width_one_le)
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open ObservableTrajectory FiniteChainSlowdown
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

private lemma constant_nonnegative (A : Instance I J) :
    0≤observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
  unfold observableConstant
  positivity

lemma target_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (G : Set (Labels A×Bool) → ℝ) :
    (targetChain A R j hp w hw).mean (fun S => G S.val)=
      chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G := by
  change (referenceChain A R j hp w hw).mean (fun S => G S.val)=_
  exact metropolisChain_mean _ _ _ _ _ _ _ _ _

lemma target_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (S : State A) :
    (targetChain A R j hp w hw).π S=
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := rfl

/-- Mean-square concentration of the real chain implemented by the
actual padded proposal. -/
theorem bounded_MSE (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (o : PhaseObservables (pairs : List (Pair A)))
    (nu : State A → ℝ)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (N : ℕ) (hN : 0<N) :
    let D := targetChain A R j hp w hw
    let G := fun S : State A => phaseObservable pairs (ratio A R j) o S.val
    (∑ S,nu S*D.squareMoment (fun S => G S-D.mean G) N S)/(N:ℝ)^2≤
      40*(Fintype.card (Labels A):ℝ)^2*
        observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/N := by
  let C := referenceChain A R j hp w hw
  let D := targetChain A R j hp w hw
  let G : Set (Labels A×Bool) → ℝ := phaseObservable pairs (ratio A R j) o
  let g : State A → ℝ := fun S => G S.val-
    chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G
  let K := observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)
  have hdual (H : State A → ℝ) : (C.inner g H)^2≤K*C.inner g g*C.energy H := by
    dsimp only [C]
    rw [referenceChain_eq_completed]
    simpa only [K,PairedLabels.length,g,G] using
      omission_chain_dual pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
        (fun p q => (w p q:ℝ)) (weight A R j) G hgood.positive
        (actual_degree A R j).1 (actual_degree A R j).2 ((A.W:ℝ)^2) (square_width_one_le A)
        (phaseObservable_class pairs (ratio A R j) o) hgood.lower hgood.upper H
  have hcmean : C.mean (fun S => G S.val)=
      chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G := by
    exact target_mean A R j hp w hw G
  have hvar : C.inner g g≤1 := by
    have hb := C.variance_le_one (fun S => G S.val) (by
      intro S
      exact phaseObservable_bounded pairs (ratio A R j)
        (fun T _ => ⟨by linarith [(ratio_bounds A R j T).1],(ratio_bounds A R j T).2⟩) o S.val)
    simpa only [FiniteChain.variance,hcmean,g] using hb
  have hwm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*C.π S := by
    intro S
    have hpi : C.π S=chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := rfl
    rw [hpi]
    simpa only [mul_div_assoc] using hwarm S
  have hm := warm_moment_bound C (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2
    (slowdown_bounds A hp).1 K (10*(Fintype.card (Labels A):ℝ)^2)
    (constant_nonnegative A) (by positivity) g hdual nu hwm N hN
  have hmean : D.mean (fun S => G S.val)=
      chainMean pairs (fun p q => (w p q:ℝ)) (weight A R j) G := target_mean A R j hp w hw G
  change (∑ S,nu S*D.squareMoment (fun S => G S.val-D.mean (fun S => G S.val)) N S)/(N:ℝ)^2≤_
  rw [hmean]
  apply hm.trans
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  apply div_le_div_of_nonneg_right _ hN0
  have hmul := mul_le_mul_of_nonneg_left hvar
    (show 0≤4*(10*(Fintype.card (Labels A):ℝ)^2)*K from by
      have := constant_nonnegative A
      dsimp only [K]
      positivity)
  nlinarith

/-- The full collection of phase observables obeys the source union
bound for the actual dyadic holding chain. -/
theorem phase_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : State A → ℝ) (hnu : ∀ S,0≤nu S)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (N : ℕ) (hN : 0<N) (eta : ℝ) (heta : 0<eta) :
    let D := targetChain A R j hp w hw
    D.pathProbability nu (N-1) (fun l => ∃ o : PhaseObservables (pairs : List (Pair A)),
      eta*D.mean (fun S => phaseObservable pairs (ratio A R j) o S.val)<
        |FiniteChain.pathSum (fun S => phaseObservable pairs (ratio A R j) o S.val) l/(N:ℝ)-
          D.mean (fun S => phaseObservable pairs (ratio A R j) o S.val)|)≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/((N:ℝ)*eta^2) := by
  let D := targetChain A R j hp w hw
  let p : ℝ := Fintype.card (Labels A)
  let K := observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)
  have hpR : 0<p := by dsimp only [p]; exact_mod_cast hp
  have hK : 0≤K := constant_nonnegative A
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hmean (o : PhaseObservables (pairs : List (Pair A))) :
      1/(20*p^2)≤D.mean (fun S => phaseObservable pairs (ratio A R j) o S.val) := by
    rw [target_mean]
    have hh := phaseObservable_mean_lower pairs PairedLabels.fresh (pairs_ne_nil A hp)
      PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
      hgood.positive (weight_positive A R j) (fun S _ => (ratio_bounds A R j S).1)
      hgood.lower hgood.upper o
    simpa only [p,PairedLabels.length] using hh
  have hb := D.relative_union_bound nu hnu
    (fun o S => phaseObservable pairs (ratio A R j) o S.val)
    (1/(20*p^2)) eta (40*p^2*K/N) (by positivity) heta (by positivity)
    hmean N hN (fun o => bounded_MSE A R j hp w hw hgood o nu hwarm N hN)
  have hJ : (Fintype.card (PhaseObservables (pairs : List (Pair A))):ℝ)≤2*p^2 := by
    have hc := phaseObservables_card pairs PairedLabels.fresh (pairs_ne_nil A hp)
    simp only [PairedLabels.length] at hc
    dsimp only [p]
    exact_mod_cast hc
  apply hb.trans
  calc
    _ ≤ (2*p^2)*(40*p^2*K/N)/(eta*(1/(20*p^2)))^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hJ (by positivity)) (sq_nonneg _)
    _ = 32000*p^8*K/((N:ℝ)*eta^2) := by
      field_simp [hpR.ne',heta.ne',hNR.ne']
      ring

end
end ContingencyTables.RootedSlowConcentration

end OAI
