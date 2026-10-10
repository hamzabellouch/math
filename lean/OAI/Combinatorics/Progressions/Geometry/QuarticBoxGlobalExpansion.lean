import OAI.Combinatorics.Progressions.Estimates.QuarticFrozenMiddleExpansion

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quartic_box_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      {N : ℕ} [NeZero N] (i j : Fin W.outputDim)
      (R : NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
        (W.quarticAntisymmetricBoxPolynomial i j)
        (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ)) q),
      0 ≤ q → R.HasOuterValueControl ((p + q + C) ^ C) ∧
        ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + q + C) ^ C) ∧
          (∀ x y : QuarticBoxIndex → ℤ, (∀ k, (P : ℤ) ∣ x k - y k) →
            ((QuotientGroup.mk (R.rationalValue x) :
                (pi (fun _ : QuarticBoxFactor => W.model)).Space) =
              QuotientGroup.mk (R.rationalValue y))) ∧
          (letI := rightMetricSpace
              (hnil := (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realification.lowerCentralSeries_eq_bot)
              ((pi (fun _ : QuarticBoxFactor => W.model)).basis.baseChange ℝ)
           ∀ (x y : QuarticBoxIndex → ℤ) (δ : ℝ), 0 ≤ δ →
             (∀ k, |(x k : ℝ)| ≤ (N : ℝ)) → (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
             (∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ (N : ℝ) * δ) →
             dist (R.slowValue x) (R.slowValue y) ≤ Real.exp ((p + q + C) ^ C) * δ) := by
  obtain ⟨a, _, houter⟩ := exists_native_orbit_outer_control (∑ _ : QuarticReplicatedIndex, 1) 8
  obtain ⟨b, _, hlocal⟩ := exists_native_orbit_local_control (∑ _ : QuarticReplicatedIndex, 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C a) ^ a + (T + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p q W _ _ _ _ N _ i j R hq
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := productNiltestBudget (v + 32) + v + 8
  have hv : 0 ≤ v := add_nonneg hp hq
  have hpv : p ≤ v := le_add_of_nonneg_right hq
  have hqv : q ≤ v := le_add_of_nonneg_left hp
  have hprod : 0 ≤ productNiltestBudget (v + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hvt : v ≤ t := by dsimp only [t]; linarith only [hprod]
  have ht : 0 ≤ t := hv.trans hvt
  have hqt : q ≤ t := hqv.trans hvt
  have hcard : (Fintype.card QuarticBoxIndex : ℝ) ≤ t := by
    norm_num [QuarticBoxIndex]
    dsimp only [t]
    linarith only [hprod, hv]
  have hmono : productNiltestBudget (p + 32) ≤ productNiltestBudget (v + 32) :=
    productNiltestBudget_mono (by positivity) (by linarith only [hpv])
  have htest : productNiltestBudget (p + 32) ≤ t := by
    dsimp only [t]
    linarith only [hmono, hv]
  let D := pi (fun _ : QuarticBoxFactor => W.model)
  have hD : D.GeometryComplexityLE t :=
    (W.quarticAntisymmetricBoxNiltest_complexity hp i j).1.mono D htest
  have hN : ∀ _k : QuarticBoxIndex, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hcost : (t + a) ^ a + (t + b) ^ b ≤ (p + q + C) ^ C := by
    simpa [X, Q, T, t, v, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget v hv
  have haC : (t + a) ^ a ≤ (p + q + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hcost
  have hbC : (t + b) ^ b ≤ (p + q + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hcost
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    houter (R.mono hqt hN) ht hD hN (by simp [QuarticBoxIndex])
  refine ⟨R.hasOuterValueControl_mono hout haC, ?_⟩
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hlocal (R.mono hqt hN) ht hD hcard hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hbC), fun x y hxy => (hcosets x y hxy).1, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  intro x y δ hδ hx hy hxy
  exact (hmotion x y δ hδ hx hy hxy).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbC) hδ)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem quartic_box_frozen_error {p q : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
    [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
    (hp : 0 ≤ p) {N : ℕ} (i j : Fin W.outputDim)
    (R : NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
      (W.quarticAntisymmetricBoxPolynomial i j)
      (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ)) q)
    (x y : QuarticBoxIndex → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) :
      (pi (fun _ : QuarticBoxFactor => W.model)).Space) = QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi (fun _ : QuarticBoxFactor => W.model)).basis.baseChange ℝ)
    ‖W.quarticAntisymmetricBoxValue i j x -
        (W.quarticAntisymmetricBoxNiltest hp i j).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x))‖ ≤
      Real.exp (productNiltestBudget (p + 32)) * dist (R.slowValue x) (R.slowValue y) := by
  let D := pi (fun _ : QuarticBoxFactor => W.model)
  let S := W.quarticAntisymmetricBoxNiltest hp i j
  let middle := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : QuarticBoxIndex => 1) (fun k => (x k : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq S.observable (R.slowValue x) middle
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left S.observable S.lipschitz
    (R.slowValue x) (R.slowValue y) middle (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (S.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (p + 32)) := by
    have h := S.observable_budget (W.quarticAntisymmetricBoxNiltest_complexity hp i j)
    linarith [S.normBound.coe_nonneg]
  rw [quartic_box_eval_factors W i j R hp x]
  exact hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)

theorem exists_quartic_box_local_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      {N : ℕ} [NeZero N] (i j : Fin W.outputDim)
      (_R : NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
        (W.quarticAntisymmetricBoxPolynomial i j)
        (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ)) q),
      0 ≤ q → ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + q + C) ^ C) ∧
        ∀ y : QuarticBoxIndex → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
          ∃ F : (QuarticBoxIndex → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : QuarticBoxIndex => 1) 3 ((p + q + C) ^ C) F) ∧
            (∀ x, ‖F x‖ ≤ 1) ∧
            ∀ (x : QuarticBoxIndex → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ k, |(x k : ℝ)| ≤ (N : ℝ)) → (∀ k, (P : ℤ) ∣ x k - y k) →
              (∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ (N : ℝ) * δ) →
              ‖W.quarticAntisymmetricBoxValue i j x - F x‖ ≤
                Real.exp ((p + q + C) ^ C) * δ := by
  obtain ⟨a, _, houter⟩ := exists_quartic_box_outer_control
  obtain ⟨b, _, hfrozen⟩ := exists_quartic_frozen_middle_expansion_of_bounds
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  let U := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + T + (X + U + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p q W _ _ _ _ N _ i j R hq
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let u := (v + a) ^ a
  let t := productNiltestBudget (v + 32)
  have hv : 0 ≤ v := add_nonneg hp hq
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have ht : 0 ≤ t := by unfold t productNiltestBudget productObservableLipBudget; positivity
  have hsum : u + t + (v + u + b) ^ b ≤ (p + q + C) ^ C := by
    simpa [X, Q, T, U, t, u, v, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget v hv
  have hpow : 0 ≤ (v + u + b) ^ b := by positivity
  have huC : u ≤ (p + q + C) ^ C := by linarith only [hsum, ht, hpow]
  have herror : t + u ≤ (p + q + C) ^ C := by linarith only [hsum, hpow]
  have hexpand : (v + u + b) ^ b ≤ (p + q + C) ^ C := by linarith only [hsum, hu, ht]
  have htest : productNiltestBudget (p + 32) ≤ t := by
    have hpv : p ≤ v := le_add_of_nonneg_right hq
    exact productNiltestBudget_mono (by positivity) (by linarith only [hpv])
  obtain ⟨⟨m, hm, hmb, hrat, hslow⟩, P, hP, hPb, hcosets, hmotion⟩ := houter W i j R hq
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr huC), ?_⟩
  intro y hy
  let F := fun x => (W.quarticAntisymmetricBoxNiltest hp i j).observable
    (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x))
  obtain ⟨E⟩ := hfrozen W hp i j R hq hu m hm hmb
    (R.slowValue y) (R.rationalValue y) (hslow y hy) (hrat y)
  refine ⟨F, ⟨E.mono hexpand⟩, fun x => W.quarticAntisymmetricBoxNiltest_norm i j hp _, ?_⟩
  intro x δ hδ hx hres hnear
  let D := pi (fun _ : QuarticBoxFactor => W.model)
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have herr := quartic_box_frozen_error W hp i j R x y (hcosets x y hres)
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herr.trans
  calc
    _ ≤ Real.exp t * (Real.exp u * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist dist_nonneg (Real.exp_nonneg t)
    _ = Real.exp (t + u) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr herror) hδ

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quartic_box_global_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      {N : ℕ} [NeZero N] (i j : Fin W.outputDim)
      (_R : NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
        (W.quarticAntisymmetricBoxPolynomial i j)
        (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ)) q),
      0 ≤ q → 0 ≤ r → Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      ∃ F : (QuarticBoxIndex → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : QuarticBoxIndex => 1) 3 ((p + q + r + C) ^ C) F) ∧
        (∀ x : QuarticBoxIndex → ZMod N, ‖F (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
        (𝔼 x : QuarticBoxIndex → ZMod N,
          ‖W.quarticAntisymmetricBoxValue i j (fun k => ((x k).val : ℤ)) -
            F (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-r) := by
  obtain ⟨A, _, hlocal⟩ := exists_quartic_box_local_expansion
  obtain ⟨B, _, hpatch⟩ := exists_bounded_variable_patch_expansion 8 2 (by norm_num)
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := U + X + 300
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r W _ _ _ _ N _ i j R hq hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let w := p + q + r
  let b := (w + A) ^ A
  let t := b + w + 300
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hlocalt : (p + q + A) ^ A ≤ t := by
    have hmono : (p + q + A) ^ A ≤ b := by
      dsimp only [b]
      apply pow_le_pow_left₀ (by positivity)
      dsimp only [w]
      linarith only [hr]
    exact hmono.trans (by dsimp only [t]; linarith only [hw])
  have hsum : (t + B) ^ B + 2 * t ≤ (p + q + r + C) ^ C := by
    simpa [X, U, T, b, w, t, Polynomial.eval₂_pow] using hbudget w hw
  have hcost : (t + B) ^ B ≤ (p + q + r + C) ^ C := by linarith only [hsum, ht]
  have hscale : 2 * t ≤ (p + q + r + C) ^ C := by
    have hpow : 0 ≤ (t + B) ^ B := by positivity
    linarith only [hsum, hpow]
  let ρ := Real.exp (-(2 * t))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((t + 2) ^ 2) := by
    dsimp only [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg t]
  obtain ⟨P, hP, hPb, hmodels⟩ := hlocal W i j R hq
  let : NeZero P := ⟨hP.ne'⟩
  have hunit (x : QuarticBoxIndex → ℤ) : ‖W.quarticAntisymmetricBoxValue i j x‖ ≤ 1 :=
    W.quarticAntisymmetricBoxValue_norm i j x
  obtain ⟨F, ⟨E⟩, hFnorm, herr⟩ := hpatch (s := 3) (N := N) (P := P)
    (by simp [QuarticBoxIndex]) (by norm_num) ht (hPb.trans (Real.exp_le_exp.mpr hlocalt)) hρ hprec
    (W.quarticAntisymmetricBoxValue i j) hunit (by
      intro y hy
      obtain ⟨G, ⟨EG⟩, hGnorm, hGerror⟩ := hmodels y hy
      refine ⟨G, ⟨EG.mono hlocalt⟩, hGnorm, ?_⟩
      intro x δ hδ hx hres hnear
      exact (hGerror x δ hδ hx hres hnear).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlocalt) hδ))
  rw [show (18 : ℝ) * (8 : ℕ) + 2 = 146 by norm_num] at herr
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * t))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  refine ⟨F, ⟨E.mono hcost⟩, hFnorm, herr.trans ?_⟩
  calc
    _ ≤ Real.exp (t + 146) * (2 * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrecip]) (Real.exp_nonneg _)
    _ = 2 * Real.exp (146 - t) := by
      dsimp only [ρ]
      rw [← mul_assoc, mul_comm (Real.exp (t + 146)) 2, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2 * (Real.exp (-r) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.exp_le_exp.mpr (show 146 - t ≤ -r - 1 by
        dsimp only [t, w]
        linarith only [hb, hp, hq])).trans
      exact exp_sub_one_le_half_exp (-r)
    _ = _ := by ring

end Erdos3

end

end OAI
