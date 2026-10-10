import OAI.Combinatorics.ContingencyTables.Rooted.RootedMultiplierUpdate
import OAI.Combinatorics.ContingencyTables.Rooted.RootedWarmStart
import OAI.Combinatorics.ContingencyTables.Counting.CompanionConcentration
import OAI.Combinatorics.ContingencyTables.Transport.ObservableTrajectory

namespace OAI

/-! # Concentration of the selected-root phase observables -/

namespace ContingencyTables.RootedConcentration

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing RootedMultiplierUpdate
open RootedWarmStart (actual_degree)
open CompanionConcentration (pairs_ne_nil square_width_one_le)
open TwoLiftStates BinaryContraction DegreeCompletion ObservableBounds

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma observable_constant_nonnegative (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ observableConstant p q := by
  unfold observableConstant
  positivity

private lemma bounded_variance_factor (p K v N : ℝ) (hK : 0 ≤ K)
    (hN : 0 ≤ N) (hv : v ≤ 1) :
    2*(10*p^2)*K*v/N ≤ 20*p^2*K/N := by
  apply div_le_div_of_nonneg_right _ hN
  nlinarith [mul_le_mul_of_nonneg_left hv (show 0 ≤ 2*(10*p^2)*K by positivity)]

/-- Every actual phase observable has the source's mean-square bound
20 p² Kobs/N under a 10 p²-warm start of its original labelled chain. -/
theorem bounded_MSE (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0< Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A R j) w) (o : PhaseObservables (pairs : List ((Labels A×Bool)×(Labels A×Bool))))
    (nu : ChainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs w (weight A R j) S.val/chainTotal pairs w (weight A R j))
    (N : ℕ) (hN : 0< N) :
    let C := metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w
      (completeDegree (weight A R j) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
      hw.positive (completeDegree_positive _ _ (actual_degree A R j).1)
    let G := fun S : ChainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) =>
      phaseObservable pairs (ratio A R j) o S.val
    (∑ S,nu S*C.squareMoment (fun S => G S-C.mean G) N S)/(N:ℝ)^2≤
      20*(Fintype.card (Labels A):ℝ)^2*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/N := by
  let gs : List ((Labels A×Bool)×(Labels A×Bool)) := pairs
  let F := completeDegree (weight A R j) gs.length
  have hF := completeDegree_positive (weight A R j) gs.length (actual_degree A R j).1
  let C := metropolisChain gs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w F hw.positive hF
  let G : Set (Labels A×Bool) → ℝ := phaseObservable gs (ratio A R j) o
  have hG : ∀ S,0≤ G S ∧ G S≤1 := by
    intro S
    exact phaseObservable_bounded gs (ratio A R j)
      (fun T _ => ⟨by linarith [(ratio_bounds A R j T).1],(ratio_bounds A R j T).2⟩) o S
  have h := ObservableTrajectory.omission_chain_timeAverage gs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover w (weight A R j) G hw.positive (actual_degree A R j).1 (actual_degree A R j).2
    ((A.W:ℝ)^2) (square_width_one_le A) (phaseObservable_class gs (ratio A R j) o)
    hw.lower hw.upper (10*(Fintype.card (Labels A):ℝ)^2) (by positivity) nu hwarm N hN
  have hv := C.variance_le_one (fun S => G S.val) (fun S => hG S.val)
  change C.variance (fun S => G S.val)≤1 at hv
  rw [metropolisChain_variance,chainVariance_completion gs (weight A R j) G w
    PairedLabels.fresh PairedLabels.cover] at hv
  have hm : C.mean (fun S => G S.val)=chainMean gs w (weight A R j) G := by
    rw [metropolisChain_mean,chainMean_completion gs (weight A R j) G w
      PairedLabels.fresh PairedLabels.cover]
  change (∑ S,nu S*C.squareMoment (fun S => G S.val-C.mean (fun T => G T.val)) N S)/(N:ℝ)^2≤ _
  rw [hm]
  calc
    _ ≤ 2*(10*(Fintype.card (Labels A):ℝ)^2)*ObservableBounds.observableConstant gs.length ((A.W:ℝ)^2)*
        chainVariance gs w (weight A R j) G/N := h
    _ ≤ 20*(Fintype.card (Labels A):ℝ)^2*observableConstant gs.length ((A.W:ℝ)^2)/N :=
      bounded_variance_factor _ _ _ _
        (observable_constant_nonnegative _ _ (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _) hv
    _ = _ := by simp only [gs,PairedLabels.length]

/-- The source's finite union bound for all actual phase observables.
The warm-start hypothesis is the restart endpoint condition, rather than
an independent phase-concentration assumption. -/
theorem phase_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0< Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : GoodMultipliers pairs (weight A R j) w)
    (nu : ChainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) → ℝ)
    (hnu : ∀ S,0≤ nu S)
    (hwarm : ∀ S,nu S≤(10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs w (weight A R j) S.val/chainTotal pairs w (weight A R j))
    (N : ℕ) (hN : 0< N) (eta : ℝ) (heta : 0< eta) :
    let C := metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w
      (completeDegree (weight A R j) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
      hw.positive (completeDegree_positive _ _ (actual_degree A R j).1)
    C.pathProbability nu (N-1) (fun l => ∃ o : PhaseObservables (pairs : List ((Labels A×Bool)×(Labels A×Bool))),
      eta*C.mean (fun S => phaseObservable pairs (ratio A R j) o S.val)<
        |FiniteChain.pathSum (fun S => phaseObservable pairs (ratio A R j) o S.val) l/(N:ℝ)-
          C.mean (fun S => phaseObservable pairs (ratio A R j) o S.val)|)≤
      16000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/((N:ℝ)*eta^2) := by
  let gs : List ((Labels A×Bool)×(Labels A×Bool)) := pairs
  let F := completeDegree (weight A R j) gs.length
  have hF := completeDegree_positive (weight A R j) gs.length (actual_degree A R j).1
  let C := metropolisChain gs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w F hw.positive hF
  let p : ℝ := Fintype.card (Labels A)
  let K := ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)
  have hpR : 0< p := by dsimp only [p]; exact_mod_cast hp
  have hK : 0≤ K := observable_constant_nonnegative _ _ (Nat.cast_nonneg _) (sq_nonneg _)
  have hNR : (0:ℝ)< N := by exact_mod_cast hN
  have hmean (o : PhaseObservables gs) :
      1/(20*p^2)≤ C.mean (fun S => phaseObservable gs (ratio A R j) o S.val) := by
    rw [metropolisChain_mean,chainMean_completion gs (weight A R j)
      (phaseObservable gs (ratio A R j) o) w PairedLabels.fresh PairedLabels.cover]
    have hh := phaseObservable_mean_lower gs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      w (weight A R j) (ratio A R j) hw.positive (weight_positive A R j)
      (fun S _ => (ratio_bounds A R j S).1) hw.lower hw.upper o
    simpa only [p,gs,PairedLabels.length] using hh
  have hb := C.relative_union_bound nu hnu
    (fun o S => phaseObservable gs (ratio A R j) o S.val)
    (1/(20*p^2)) eta (20*p^2*K/N) (by positivity) heta (by positivity) hmean N hN
    (fun o => bounded_MSE A R j hp w hw o nu hwarm N hN)
  have hJ : (Fintype.card (PhaseObservables gs):ℝ)≤2*p^2 := by
    have hc := phaseObservables_card gs PairedLabels.fresh (pairs_ne_nil A hp)
    simp only [gs,PairedLabels.length] at hc
    dsimp only [p,gs]
    exact_mod_cast hc
  apply hb.trans
  calc
    _ ≤ (2*p^2)*(20*p^2*K/N)/(eta*(1/(20*p^2)))^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hJ (by positivity)) (sq_nonneg _)
    _ = 16000*p^8*K/((N:ℝ)*eta^2) := by
      field_simp [hpR.ne',heta.ne',hNR.ne']
      ring

end ContingencyTables.RootedConcentration

end OAI
