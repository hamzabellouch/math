import OAI.Combinatorics.Progressions.Estimates.CubicFrozenMiddleExpansion
import OAI.Combinatorics.Progressions.Estimates.NativeSixVariablePatchExpansion

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

theorem cubicAntisymmetricBoxFactors_normBound (i j : Fin V.outputDim × Fin V.outputDim)
    (shift : ℤ) (a : Fin 8 × Fin 4) :
    (V.cubicAntisymmetricBoxFactors i j shift a).normBound = 1 := by
  rcases a with ⟨c, k⟩
  unfold cubicAntisymmetricBoxFactors
  split_ifs <;> fin_cases k <;> rfl

theorem cubicAntisymmetricBoxNiltest_norm
    [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    (hp : 0 ≤ p) (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
    (x : (pi (fun _ : Fin 8 × Fin 4 => V.model)).Space) :
    ‖(V.cubicAntisymmetricBoxNiltest hp i j shift).observable x‖ ≤ 1 := by
  change ‖∏ a, (V.cubicAntisymmetricBoxFactors i j shift a).observable
    (productProjection (fun _ : Fin 8 × Fin 4 => V.model) a x)‖ ≤ 1
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro a _
  simpa only [V.cubicAntisymmetricBoxFactors_normBound, NNReal.coe_one] using
    (V.cubicAntisymmetricBoxFactors i j shift a).norm_le
      (productProjection (fun _ : Fin 8 × Fin 4 => V.model) a x)

end NativeMultidegreeNilcharacter

theorem exists_cubic_frozen_middle_expansion_of_bounds :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q u : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      (hp : 0 ≤ p) {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
      (R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
        (V.cubicAntisymmetricBoxPolynomial i j shift)
        (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) q),
      0 ≤ q → 0 ≤ u → ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
      ∀ a r : (pi (fun _ : Fin 8 × Fin 4 => V.model)).RealGroup,
        (∀ k, |((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.baseChange ℝ).repr a.coord k| ≤ Real.exp u) →
        ((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) 2 ((p + q + u + C) ^ C)
          (fun x => (V.cubicAntisymmetricBoxNiltest hp i j shift).observable
            (QuotientGroup.mk (R.frozenMiddleValue a r x)))) := by
  obtain ⟨c, _, hdesc⟩ := exists_native_frozen_middle_expansion 2
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q u V _ _ _ _ hp N _ i j shift R hq hu m hm hmb a r ha hrat
  let v := p + q + u
  let t := productNiltestBudget (v + 32) + v + 6
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hpv : p ≤ v := by dsimp only [v]; linarith only [hq, hu]
  have hqv : q ≤ v := by dsimp only [v]; linarith only [hp, hu]
  have huv : u ≤ v := le_add_of_nonneg_left (add_nonneg hp hq)
  have hprod : 0 ≤ productNiltestBudget (v + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hvt : v ≤ t := by dsimp only [t]; linarith only [hprod]
  have ht : 0 ≤ t := hv.trans hvt
  have hut : u ≤ t := huv.trans hvt
  have htest : productNiltestBudget (p + 32) ≤ t := by
    have hmono : productNiltestBudget (p + 32) ≤ productNiltestBudget (v + 32) := by
      unfold productNiltestBudget productObservableLipBudget
      gcongr
    exact hmono.trans (by dsimp only [t]; linarith only [hv])
  let R' := R.mono (hqv.trans hvt) (fun _ => by exact_mod_cast NeZero.pos N)
  let S := V.cubicAntisymmetricBoxNiltest hp i j shift
  obtain ⟨E⟩ := hdesc (pi (fun _ : Fin 8 × Fin 4 => V.model)) R' S ht
    ((V.cubicAntisymmetricBoxNiltest_complexity hp i j shift).mono htest)
    (cubic_box_top_layer_invariant V i j shift R' hp) m hm
    (hmb.trans (Real.exp_le_exp.mpr hut)) a r
    (fun k => (ha k).trans (Real.exp_le_exp.mpr hut)) hrat
  have hcost : (t + c) ^ c ≤ (p + q + u + C) ^ C := by
    simpa [X, Q, T, t, v, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget v hv
  exact ⟨E.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_cubic_box_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
      (R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
        (V.cubicAntisymmetricBoxPolynomial i j shift)
        (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) q),
      0 ≤ q → R.HasOuterValueControl ((p + q + C) ^ C) ∧
        ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + q + C) ^ C) ∧
          (∀ x y : Fin 6 → ℤ, (∀ k, (P : ℤ) ∣ x k - y k) →
            ((QuotientGroup.mk (R.rationalValue x) :
                (pi (fun _ : Fin 8 × Fin 4 => V.model)).Space) =
              QuotientGroup.mk (R.rationalValue y))) ∧
          (letI := rightMetricSpace
              (hnil := (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realification.lowerCentralSeries_eq_bot)
              ((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.baseChange ℝ)
           ∀ (x y : Fin 6 → ℤ) (δ : ℝ), 0 ≤ δ →
             (∀ k, |(x k : ℝ)| ≤ (N : ℝ)) → (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
             (∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ (N : ℝ) * δ) →
             dist (R.slowValue x) (R.slowValue y) ≤ Real.exp ((p + q + C) ^ C) * δ) := by
  obtain ⟨a, _, houter⟩ := exists_native_orbit_outer_control (∑ _ : CubicReplicatedIndex, 1) 6
  obtain ⟨b, _, hlocal⟩ := exists_native_orbit_local_control (∑ _ : CubicReplicatedIndex, 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C a) ^ a + (T + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p q V _ _ _ _ N _ i j shift R hq
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q
  let t := productNiltestBudget (v + 32) + v + 6
  have hv : 0 ≤ v := add_nonneg hp hq
  have hpv : p ≤ v := le_add_of_nonneg_right hq
  have hqv : q ≤ v := le_add_of_nonneg_left hp
  have hprod : 0 ≤ productNiltestBudget (v + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hvt : v ≤ t := by dsimp only [t]; linarith only [hprod]
  have ht : 0 ≤ t := hv.trans hvt
  have hqt : q ≤ t := hqv.trans hvt
  have hcard : (Fintype.card (Fin 6) : ℝ) ≤ t := by
    norm_num
    dsimp only [t]
    linarith only [hprod, hv]
  have htest : productNiltestBudget (p + 32) ≤ t := by
    have hmono : productNiltestBudget (p + 32) ≤ productNiltestBudget (v + 32) := by
      unfold productNiltestBudget productObservableLipBudget
      gcongr
    exact hmono.trans (by dsimp only [t]; linarith only [hv])
  let D := pi (fun _ : Fin 8 × Fin 4 => V.model)
  have hD : D.GeometryComplexityLE t :=
    (V.cubicAntisymmetricBoxNiltest_complexity hp i j shift).1.mono D htest
  have hN : ∀ _k : Fin 6, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hcost : (t + a) ^ a + (t + b) ^ b ≤ (p + q + C) ^ C := by
    simpa [X, Q, T, t, v, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget v hv
  have haC : (t + a) ^ a ≤ (p + q + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hcost
  have hbC : (t + b) ^ b ≤ (p + q + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hcost
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    houter (R.mono hqt hN) ht hD hN (by simp)
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

theorem cubic_box_frozen_error {p q : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
    (hp : 0 ≤ p) {N : ℕ} (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
    (R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
      (V.cubicAntisymmetricBoxPolynomial i j shift)
      (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) q)
    (x y : Fin 6 → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) :
      (pi (fun _ : Fin 8 × Fin 4 => V.model)).Space) = QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.baseChange ℝ)
    ‖V.cubicAntisymmetricBoxValue i j shift x -
        (V.cubicAntisymmetricBoxNiltest hp i j shift).observable
          (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x))‖ ≤
      Real.exp (productNiltestBudget (p + 32)) * dist (R.slowValue x) (R.slowValue y) := by
  let D := pi (fun _ : Fin 8 × Fin 4 => V.model)
  let S := V.cubicAntisymmetricBoxNiltest hp i j shift
  let middle := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 6 => 1) (fun k => (x k : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq S.observable (R.slowValue x) middle
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left S.observable S.lipschitz
    (R.slowValue x) (R.slowValue y) middle (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (S.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (p + 32)) := by
    have h := S.observable_budget (V.cubicAntisymmetricBoxNiltest_complexity hp i j shift)
    linarith [S.normBound.coe_nonneg]
  rw [cubic_box_eval_factors V i j shift R hp x]
  exact hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)

theorem exists_cubic_box_local_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
      (_R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
        (V.cubicAntisymmetricBoxPolynomial i j shift)
        (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) q),
      0 ≤ q → ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + q + C) ^ C) ∧
        ∀ y : Fin 6 → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
          ∃ F : (Fin 6 → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) 2 ((p + q + C) ^ C) F) ∧
            (∀ x, ‖F x‖ ≤ 1) ∧
            ∀ (x : Fin 6 → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ k, |(x k : ℝ)| ≤ (N : ℝ)) → (∀ k, (P : ℤ) ∣ x k - y k) →
              (∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ (N : ℝ) * δ) →
              ‖V.cubicAntisymmetricBoxValue i j shift x - F x‖ ≤
                Real.exp ((p + q + C) ^ C) * δ := by
  obtain ⟨a, _, houter⟩ := exists_cubic_box_outer_control
  obtain ⟨b, _, hfrozen⟩ := exists_cubic_frozen_middle_expansion_of_bounds
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  let U := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + T + (X + U + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p q V _ _ _ _ N _ i j shift R hq
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
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
    unfold t productNiltestBudget productObservableLipBudget
    gcongr
  obtain ⟨⟨m, hm, hmb, hrat, hslow⟩, P, hP, hPb, hcosets, hmotion⟩ := houter V i j shift R hq
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr huC), ?_⟩
  intro y hy
  let F := fun x => (V.cubicAntisymmetricBoxNiltest hp i j shift).observable
    (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue y) (R.rationalValue y) x))
  obtain ⟨E⟩ := hfrozen V hp i j shift R hq hu m hm hmb
    (R.slowValue y) (R.rationalValue y) (hslow y hy) (hrat y)
  refine ⟨F, ⟨E.mono hexpand⟩, fun x => V.cubicAntisymmetricBoxNiltest_norm hp i j shift _, ?_⟩
  intro x δ hδ hx hres hnear
  let D := pi (fun _ : Fin 8 × Fin 4 => V.model)
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have herr := cubic_box_frozen_error V hp i j shift R x y (hcosets x y hres)
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

theorem exists_cubic_box_global_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
      (_R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
        (V.cubicAntisymmetricBoxPolynomial i j shift)
        (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) q),
      0 ≤ q → 0 ≤ r → Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      ∃ F : (Fin 6 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) 2 ((p + q + r + C) ^ C) F) ∧
        (∀ x : Fin 6 → ZMod N, ‖F (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
        (𝔼 x : Fin 6 → ZMod N,
          ‖V.cubicAntisymmetricBoxValue i j shift (fun k => ((x k).val : ℤ)) -
            F (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-r) := by
  obtain ⟨A, _, hlocal⟩ := exists_cubic_box_local_expansion
  obtain ⟨B, _, hpatch⟩ := exists_six_variable_patch_expansion 2
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := U + X + 200
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r V _ _ _ _ N _ i j shift R hq hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let w := p + q + r
  let b := (w + A) ^ A
  let t := b + w + 200
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
  obtain ⟨P, hP, hPb, hmodels⟩ := hlocal V i j shift R hq
  let : NeZero P := ⟨hP.ne'⟩
  have hunit (x : Fin 6 → ℤ) : ‖V.cubicAntisymmetricBoxValue i j shift x‖ ≤ 1 := by
    rw [← V.cubicAntisymmetricBoxNiltest_eval hp]
    exact V.cubicAntisymmetricBoxNiltest_norm hp i j shift _
  obtain ⟨F, ⟨E⟩, hFnorm, herr⟩ := hpatch (s := 2) (N := N) (P := P)
    (by norm_num) ht (hPb.trans (Real.exp_le_exp.mpr hlocalt)) hρ hprec
    (V.cubicAntisymmetricBoxValue i j shift) hunit (by
      intro y hy
      obtain ⟨G, ⟨EG⟩, hGnorm, hGerror⟩ := hmodels y hy
      refine ⟨G, ⟨EG.mono hlocalt⟩, hGnorm, ?_⟩
      intro x δ hδ hx hres hnear
      exact (hGerror x δ hδ hx hres hnear).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlocalt) hδ))
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * t))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  refine ⟨F, ⟨E.mono hcost⟩, hFnorm, herr.trans ?_⟩
  calc
    _ ≤ Real.exp (t + 110) * (2 * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrecip]) (Real.exp_nonneg _)
    _ = 2 * Real.exp (110 - t) := by
      dsimp only [ρ]
      rw [← mul_assoc, mul_comm (Real.exp (t + 110)) 2, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2 * (Real.exp (-r) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.exp_le_exp.mpr (show 110 - t ≤ -r - 1 by
        dsimp only [t, w]
        linarith only [hb, hp, hq])).trans
      exact exp_sub_one_le_half_exp (-r)
    _ = _ := by ring

end Erdos3

end

end OAI
