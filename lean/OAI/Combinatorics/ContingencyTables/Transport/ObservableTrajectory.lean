import OAI.Combinatorics.ContingencyTables.Transport.TraceBounds

namespace OAI

/-!
# Warm trajectory averages of the paper's class observables

The dual estimate is derived from the proved original-coordinate observable
Poincaré inequality. The existing finite-chain covariance and warm moment
lemmas then give the paper's 2UKobs Var/N mean-square bound. Completion is
absent from the observable mean, variance, and warm-start law.
-/

namespace ContingencyTables.ObservableTrajectory

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableVariance ObservableBounds ComplementChain

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Dual observable bound for the genuine omission-lift chain. -/
theorem omission_chain_dual (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q) (hG : ClassObservable gs G)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (H : ChainIndex gs → ℝ) :
    let C := metropolisChain gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    let g := fun S : ChainIndex gs => G S.val-chainMean gs w f G
    (C.inner g H)^2 ≤ observableConstant gs.length q*C.inner g g*C.energy H := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  let C := metropolisChain gs hgs hne hcover w F hw hF
  let a := chainMean gs w f G
  let g := fun S : ChainIndex gs => G S.val-a
  let H' := extendChainFun gs H
  let QH := fun S : ChainIndex gs => observableProjection gs F H' S.val
  have hext : (fun S : ChainIndex gs => H' S.val) = H := by
    funext S
    exact extendChainFun_apply gs H S
  have hmean : C.mean g = 0 := by
    have hm := metropolisChain_mean gs hgs hne hcover w F G hw hF
    rw [chainMean_completion gs f G w hgs hcover] at hm
    change C.mean (fun S => G S.val-a) = 0
    change C.mean (fun S : ChainIndex gs => G S.val) = a at hm
    rw [← hm]
    exact C.centered_mean _
  have hpair : C.inner g H = C.inner g QH := by
    rw [← hext]
    change C.inner (fun S => G S.val-a) (fun S => H' S.val) =
      C.inner (fun S => G S.val-a) (fun S => observableProjection gs F H' S.val)
    dsimp only [C]
    rw [metropolisChain_inner gs hgs hne hcover w F (fun S => G S-a) H' hw hF,
      metropolisChain_inner gs hgs hne hcover w F (fun S => G S-a) (observableProjection gs F H') hw hF]
    exact congrArg (fun t => t/chainTotal gs w F)
      (chain_pairing_projection gs hgs hcover w F (fun S => G S-a) H' hF (hG.sub_const a))
  have hbound : C.variance QH ≤ observableConstant gs.length q*C.energy H := by
    change (metropolisChain gs hgs hne hcover w F hw hF).variance
      (fun S => observableProjection gs F H' S.val) ≤ _
    rw [metropolisChain_variance]
    have hb := omission_observable_poincare gs hgs hne hcover w hw f H' hf hsig q hq hlower hupper
    have hproj : observableProjection gs F H' = observableProjection gs f H' :=
      funext (observableProjection_completion gs f H' hgs)
    rw [hproj, chainVariance_completion gs f _ w hgs hcover]
    rw [← chainDirichlet_completion gs f H' w hgs hcover,
      ← metropolisChain_energy gs hgs hne hcover w F H' hw hF, hext] at hb
    exact hb
  dsimp only
  rw [hpair, ← C.inner_center_right g QH hmean (C.mean QH)]
  calc
    _ ≤ C.inner g g*C.variance QH := C.inner_cauchy _ _
    _ ≤ C.inner g g*(observableConstant gs.length q*C.energy H) :=
      mul_le_mul_of_nonneg_left hbound (C.inner_nonneg g)
    _ = _ := by ring

/-- The manuscript's trajectory mean-square estimate, using its original
conditional class observable, stationary variance, and warm-start density. -/
theorem omission_chain_timeAverage (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q) (hG : ClassObservable gs G)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (U : ℝ) (hU : 0 ≤ U) (ν : ChainIndex gs → ℝ)
    (hwarm : ∀ S, ν S ≤ U*chainWeight gs w f S.val/chainTotal gs w f)
    (N : ℕ) (hN : 0 < N) :
    let C := metropolisChain gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    let g := fun S : ChainIndex gs => G S.val-chainMean gs w f G
    (∑ S, ν S*C.squareMoment g N S)/(N:ℝ)^2 ≤
      2*U*observableConstant gs.length q*chainVariance gs w f G/N := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  let C := metropolisChain gs hgs hne hcover w F hw hF
  let g := fun S : ChainIndex gs => G S.val-chainMean gs w f G
  have hi : C.inner g g = chainVariance gs w f G := by
    rw [← chainVariance_completion gs f G w hgs hcover,
      ← metropolisChain_variance gs hgs hne hcover w F G hw hF]
    unfold FiniteChain.variance
    rw [metropolisChain_mean, chainMean_completion gs f G w hgs hcover]
  have hK : 0 ≤ observableConstant gs.length q := by
    unfold observableConstant
    have hq0 : 0 ≤ q := by linarith
    positivity
  have hwarm' : ∀ S, ν S ≤ U*C.π S := by
    intro S
    change ν S ≤ U*(chainWeight gs w F S.val/chainTotal gs w F)
    rw [chainTotal_completion gs f w hgs hcover]
    have hd := S.property.ncard hgs hcover
    simpa only [chainWeight, F, completeDegree, hd, ite_true, mul_div_assoc] using hwarm S
  have h := C.warm_squareMoment_bound g (observableConstant gs.length q) U hK hU
    (omission_chain_dual gs hgs hne hcover w f G hw hf hsig q hq hG hlower hupper) ν hwarm' N hN
  rw [hi] at h
  exact h

end ContingencyTables.ObservableTrajectory

end OAI
