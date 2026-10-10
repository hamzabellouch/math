import OAI.Combinatorics.ContingencyTables.Transport.ComplementChain

namespace OAI

/-!
# Trace mixing for the actual omission-lift Metropolis chain

The finite-chain constructor receives the proved positive completion.
Its state weights equal the original valid-degree weights, and the
transversal trace has the original normalized factorial-lift law.
The trace Poincaré bound uses the proved manuscript-coordinate variance
bound, followed by the existing harmonic-extension and spectral arguments.
-/

namespace ContingencyTables.TraceBounds

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableVariance ObservableBounds ComplementChain RecursiveSignedTransport

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma completed_trace_pi (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r) (hf : DegreePositive f gs.length)
    (S : PlainIndex gs) :
    (metropolisTrace gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)).π S = f S.val.val / slotTotal gs f ∅ := by
  rw [metropolisTrace_pi, slotTotal_completeDegree gs f gs.length ∅ (by simp)]
  simp only [completeDegree, S.property.ncard hgs hcover, ite_true]

/-- Exact inverse-gap bound 2p²Cp from the actual two-lift variance theorem. -/
theorem omission_trace_poincare (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : OmissionProperty f gs.length) (hsigg : AdditionProperty g gs.length)
    (q : ℝ) (hq : 0 ≤ q)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S)
    (h : PlainIndex gs → ℝ) :
    let T := metropolisTrace gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    T.variance h ≤ (2*(gs.length:ℝ)^2*((gs.length:ℝ)*(1+8*(gs.length:ℝ)*q^2)))*T.energy h := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  let := plainIndex_nonempty gs hgs hcover
  let C := metropolisChain gs hgs hne hcover w F hw hF
  let Q := metropolisKilled gs hgs hne hcover w F hw hF
  let H := C.harmonicExtension (plainPredicate gs) Q h
  let J := extendChainFun gs H
  have hJ (S : ChainIndex gs) : J S.val = H S := extendChainFun_apply gs H S
  have hh (S : PlainIndex gs) : J S.val.val = h S := by
    rw [hJ]
    exact C.harmonicExtension_inside (plainPredicate gs) Q h S
  have hvar := metropolisTrace_variance gs hgs hne hcover w F hw hF J
  have hefun : (fun S : PlainIndex gs => J S.val.val) = h := funext hh
  rw [hefun, slotVariance_completeDegree gs f J gs.length ∅ (by simp),
    slotTotal_completeDegree gs f gs.length ∅ (by simp)] at hvar
  have hv := omission_twoLift_transversal_variance gs f g J w q hq hf hg hsigf hsigg
    hgs hcover hw hgood hagree hcompare
  have hz : 0 < slotTotal gs f ∅ := slotTotal_degree_positive gs f gs.length hf ∅ (by simp) hgs
  have henergy : restrictedEnergy (chainEdges gs) (chainConductance gs w f) J ∅ ∅ =
      (2*(gs.length:ℝ)^2*slotTotal gs f ∅)*(metropolisTrace gs hgs hne hcover w F hw hF).energy h := by
    have hc := metropolisChain_energy gs hgs hne hcover w F J hw hF
    have hfJn : (fun S : ChainIndex gs => J S.val) = H := funext hJ
    rw [hfJn] at hc
    change C.energy (C.harmonicExtension (plainPredicate gs) Q h) = _ at hc
    rw [C.traceChain_energy (plainPredicate gs) Q (by intro _ _; rfl)] at hc
    change C.insideMass (plainPredicate gs)*(metropolisTrace gs hgs hne hcover w F hw hF).energy h = _ at hc
    rw [metropolis_insideMass gs hgs hne hcover w F hw hF] at hc
    unfold chainDirichlet at hc
    rw [restrictedEnergy_completeDegree gs f J w hgs hcover ∅ ∅,
      slotTotal_completeDegree gs f gs.length ∅ (by simp)] at hc
    have hΛ := chainTotal_pos gs hgs hcover w F hF hw
    have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
    field_simp [ne_of_gt hn] at hc
    nlinarith
  rw [henergy] at hv
  dsimp only
  rw [hvar]
  apply (div_le_iff₀ hz).mpr
  nlinarith

lemma trace_constant_le_observable (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2*p^2*(p*(1+8*p*q^2)) ≤ observableConstant p q := by
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hcoef : 2*p^2 ≤ 90*p^4 := by
    have hp2 : 1 ≤ p^2 := by nlinarith
    have hp4 : p^2 ≤ p^4 := by nlinarith [sq_nonneg (p^2-1)]
    nlinarith
  have hc : 0 ≤ p*(1+8*p*q^2) := by positivity
  have ht : 0 ≤ 10*p^4*(2*(8+32*p*q^3)) := by positivity
  calc
    _ ≤ 90*p^4*(p*(1+8*p*q^2)) := mul_le_mul_of_nonneg_right hcoef hc
    _ ≤ observableConstant p q := by unfold observableConstant; nlinarith

/-- Pointwise relative mixing of the actual transversal trace with Kobs.
The lower bound m applies to the original normalized lift masses. -/
theorem omission_trace_relative_mixing (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hg : DegreePositive g gs.length)
    (hsigf : OmissionProperty f gs.length) (hsigg : AdditionProperty g gs.length)
    (q : ℝ) (hq : 1 ≤ q)
    (hgood : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hagree : ∀ S, PlainState gs S → f S = g S)
    (hcompare : ∀ S, ChainState gs S → f S ≤ q*g S)
    (m : ℝ) (hm : 0 < m) (hmin : ∀ S : PlainIndex gs, m ≤ f S.val.val/slotTotal gs f ∅)
    (s : ℕ) (x y : PlainIndex gs) :
    let T := metropolisTrace gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    |(T.kernel.power s).P x y/(f y.val.val/slotTotal gs f ∅)-1| ≤
      Real.exp (-(s:ℝ)/observableConstant gs.length q)/m := by
  let T := metropolisTrace gs hgs hne hcover w (completeDegree f gs.length) hw
    (completeDegree_positive f gs.length hf)
  have hp : (1:ℝ) ≤ gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hK : 1 ≤ observableConstant gs.length q := by
    have hpow : (1:ℝ) ≤ (gs.length:ℝ)^5 := one_le_pow₀ hp
    have hlow := observableConstant_lower gs.length q hp hq
    nlinarith
  have hπ : ∀ S, m ≤ T.π S := by
    intro S
    rw [completed_trace_pi gs hgs hne hcover w f hw hf S]
    exact hmin S
  have hP : ∀ h, T.variance h ≤ observableConstant gs.length q*T.energy h := by
    intro h
    exact (omission_trace_poincare gs hgs hne hcover w f g hw hf hg hsigf hsigg q
      (by linarith) hgood hagree hcompare h).trans
      (mul_le_mul_of_nonneg_right (trace_constant_le_observable gs.length q hp hq) (T.energy_nonneg h))
  have ht := T.kernel_point_mixing (observableConstant gs.length q) m hK hm hπ hP s x y
  rwa [completed_trace_pi gs hgs hne hcover w f hw hf y] at ht

/-- A U-warm trace start costs at most 5p²U original-chain steps per
return, with the exact original normalized transversal law. -/
theorem omission_trace_returnCost (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r) (hf : DegreePositive f gs.length)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (U : ℝ) (hU : 0 ≤ U) (ν : PlainIndex gs → ℝ)
    (hwarm : ∀ S, ν S ≤ U*(f S.val.val/slotTotal gs f ∅)) :
    let F := completeDegree f gs.length
    let hF := completeDegree_positive f gs.length hf
    let C := metropolisChain gs hgs hne hcover w F hw hF
    let Q := metropolisKilled gs hgs hne hcover w F hw hF
    (∑ S, ν S*C.returnCost (plainPredicate gs) Q S) ≤ 5*(gs.length:ℝ)^2*U := by
  let F := completeDegree f gs.length
  have hF := completeDegree_positive f gs.length hf
  let C := metropolisChain gs hgs hne hcover w F hw hF
  let Q := metropolisKilled gs hgs hne hcover w F hw hF
  let := plainIndex_nonempty gs hgs hcover
  have hwarm' : ∀ S, ν S ≤ U*(metropolisTrace gs hgs hne hcover w F hw hF).π S := by
    intro S
    rw [completed_trace_pi gs hgs hne hcover w f hw hf S]
    exact hwarm S
  have hr := C.warm_returnCost (plainPredicate gs) Q (by intro _ _; rfl) ν U hwarm'
  have hu : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs F ∅/slotDefect gs F ∅ p r := by
    intro p hp r hr hpr
    dsimp only [F]
    rw [slotTotal_completeDegree gs f gs.length ∅ (by simp),
      slotDefect_completeDegree gs f gs.length ∅ (by simp) hgs p r hp hr hpr]
    exact hupper p hp r hr hpr
  have htotal := chainTotal_le gs hgs hne hcover w F hF hu
  have hz := slotTotal_pos gs F hF ∅ hgs
  have hΛ := chainTotal_pos gs hgs hcover w F hF hw
  rw [metropolis_insideMass gs hgs hne hcover w F hw hF] at hr
  have heq : U/(slotTotal gs F ∅/chainTotal gs w F) = U*chainTotal gs w F/slotTotal gs F ∅ := by
    field_simp
  have hbound : U/(slotTotal gs F ∅/chainTotal gs w F) ≤ 5*(gs.length:ℝ)^2*U := by
    rw [heq]
    apply (div_le_iff₀ hz).mpr
    nlinarith [mul_le_mul_of_nonneg_left htotal hU]
  exact hr.trans hbound

end ContingencyTables.TraceBounds

end OAI
