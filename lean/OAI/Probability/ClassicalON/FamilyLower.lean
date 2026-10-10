import OAI.Probability.ClassicalON.FamilyEstimate

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

theorem norm_avg_row_sum (S : SpinSystem 3 V E) (u : I → E → ℂ)
    (F : E → C((V → Spin 3), ℂ)) (c : ℝ)
    (hF : ∀ e, ‖S.averageComplexLinear (F e)‖ ≤ c * rowSquare u e) :
    ‖S.averageComplexLinear (∑ e, F e)‖ ≤ c * familyHSSquare u := by
  simpa only [familyHSSquare, Finset.mul_sum] using
    S.norm_averageComplex_sum_le F (fun e => c * rowSquare u e) hF

omit [Fintype I] in
theorem norm_avg_add_le (S : SpinSystem 3 V E) (F G : C((V → Spin 3), ℂ))
    (a b : ℝ) (hF : ‖S.averageComplexLinear F‖ ≤ a)
    (hG : ‖S.averageComplexLinear G‖ ≤ b) :
    ‖S.averageComplexLinear (F+G)‖ ≤ a+b := by
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add hF hG)

theorem norm_familyRemainder_le (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    ‖S.averageComplexLinear (S.familyRemainder (fun i => S.differential (f i)))‖ ≤
      (6*β^2+4*β*Real.sqrt β+β) * familyHSSquare (fun i => S.differential (f i)) := by
  let u := fun i => S.differential (f i)
  let T := familyKernel u
  let X := fun M e => S.currentObservable M (T e)
  let C := S.coefficientObservable
  let bar := conjugateObservable (Ω := V → Spin 3)
  let k : ℂ → C((V → Spin 3), ℂ) := ContinuousMap.const (V → Spin 3)
  let H := familyHSSquare u
  have ha (e : E) : S.averageLinear (normObservable (X axisA e) * normObservable (X axisA e)) ≤
      β * rowSquare u e := S.row_current_moment β hb axisA axisA_skew axisA_norm_le f hP e
  have hb' (e : E) : S.averageLinear (normObservable (X axisB e) * normObservable (X axisB e)) ≤
      β * rowSquare u e := S.row_current_moment β hb axisB axisB_skew axisB_norm_le f hP e
  have hac (e : E) : S.averageLinear (normObservable (bar (X axisA e)) *
      normObservable (bar (X axisA e))) ≤ β * rowSquare u e := by
    simpa only [bar, normObservable_conjugate] using ha e
  have hbc (e : E) : S.averageLinear (normObservable (bar (X axisB e)) *
      normObservable (bar (X axisB e))) ≤ β * rowSquare u e := by
    simpa only [bar, normObservable_conjugate] using hb' e
  have row (M : SpinOperator 3) (hM : ‖M‖ ≤ 1)
      (F G : E → C((V → Spin 3), ℂ))
      (hF : ∀ e, S.averageLinear (normObservable (F e)*normObservable (F e)) ≤ β*rowSquare u e)
      (hG : ∀ e, S.averageLinear (normObservable (G e)*normObservable (G e)) ≤ β*rowSquare u e) :
      ‖S.averageComplexLinear (∑ e, C M e * F e * G e)‖ ≤ β^2*H := by
    apply S.norm_avg_row_sum u _ (β^2)
    intro e
    exact (S.norm_avg_coeff_two β (β*rowSquare u e) hβ hb M hM e (F e) (G e)
      (hF e) (hG e)).trans_eq (by ring)
  have b1 := row (axisA^2) (norm_square_le_one axisA axisA_norm_le)
    (X axisB) (fun e => bar (X axisB e)) hb' hbc
  have b2 := row mixedAB mixedAB_norm_le (X axisB) (X axisA) hb' ha
  have b3 := row mixedAB mixedAB_norm_le (fun e => bar (X axisA e))
    (fun e => bar (X axisB e)) hac hbc
  have b4 := row (axisB^2) (norm_square_le_one axisB axisB_norm_le)
    (fun e => bar (X axisA e)) (X axisA) hac ha
  have pair (M N : SpinOperator 3) (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1)
      (z : E → E → ℂ) (hz : ∀ e l, ‖z e l‖ = ‖T e l‖^2) :
      ‖S.averageComplexLinear (∑ e, ∑ l, C M e * C N l * k (z e l))‖ ≤ β^2*H := by
    apply S.norm_avg_row_sum u _ (β^2)
    intro e
    calc _ ≤ ∑ l, β^2*‖T e l‖^2 := by
          apply S.norm_averageComplex_sum_le
          intro l
          exact (S.norm_avg_coeff_coeff_const β hβ hb M N hM hN e l (z e l)).trans_eq
            (by rw [hz e l])
         _ = _ := by rw [← Finset.mul_sum]; rfl
  have b5 := pair (axisA^2) (axisB^2) (norm_square_le_one axisA axisA_norm_le)
    (norm_square_le_one axisB axisB_norm_le) (fun e l => T e l*conj (T e l))
    (by intro e l; simp only [norm_mul, Complex.norm_conj, pow_two])
  have b6 := pair mixedAB mixedAB mixedAB_norm_le mixedAB_norm_le (fun e l => T e l^2)
    (by intro e l; exact norm_pow _ _)
  have triple (M : SpinOperator 3) (hM : ‖M‖ ≤ 1)
      (z : E → ℂ) (hz : ∀ e, ‖z e‖ ≤ Real.sqrt (rowSquare u e))
      (F : E → C((V → Spin 3), ℂ))
      (hF : ∀ e, S.averageLinear (normObservable (F e)*normObservable (F e)) ≤ β*rowSquare u e) :
      ‖S.averageComplexLinear (∑ e, C M e * k (z e) * F e)‖ ≤ β*Real.sqrt β*H := by
    apply S.norm_avg_row_sum u _ (β*Real.sqrt β)
    intro e
    exact S.norm_avg_coeff_const_current β (rowSquare u e) hβ (rowSquare_nonneg u e)
      hb M hM e (z e) (hz e) (F e) (hF e)
  have hz (e : E) : ‖T e e‖ ≤ Real.sqrt (rowSquare u e) := kernel_diag_norm_le_sqrt u e
  have hzc (e : E) : ‖conj (T e e)‖ ≤ Real.sqrt (rowSquare u e) := by
    rw [Complex.norm_conj]; exact hz e
  have b7 := triple mixedAAB mixedAAB_norm_le (fun e => T e e) hz
    (fun e => bar (X axisB e)) hbc
  have b8 := triple mixedABB mixedABB_norm_le (fun e => T e e) hz (X axisA) ha
  have b9 := triple mixedAAB mixedAAB_norm_le (fun e => conj (T e e)) hzc (X axisB) hb'
  have b10 := triple mixedABB mixedABB_norm_le (fun e => conj (T e e)) hzc
    (fun e => bar (X axisA e)) hac
  have b11 : ‖S.averageComplexLinear (∑ e, C mixedAABB e * k (T e e*conj (T e e)))‖ ≤ β*H := by
    apply S.norm_avg_row_sum u _ β
    intro e
    calc _ ≤ β*‖T e e*conj (T e e)‖ := S.norm_avg_coeff_const β hb mixedAABB mixedAABB_norm_le e _
         _ = β*‖T e e‖^2 := by rw [norm_mul, Complex.norm_conj, pow_two]
         _ ≤ β*rowSquare u e := mul_le_mul_of_nonneg_left (kernel_diag_sq_le_row u e) hβ
  have hadd := S.norm_avg_add_le
  have h := hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _
    (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ b1 b2)
      b3) b4) b5) b6) b7) b8) b9) b10) b11
  change ‖S.averageComplexLinear (S.familyRemainder u)‖ ≤ _ at h ⊢
  exact h.trans_eq (by dsimp only [H]; ring)

theorem fourth_family_lower (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    -((6*β^2+4*β*Real.sqrt β+β)*familyHSSquare (fun i => S.differential (f i))) ≤
      (S.averageComplexLinear (∑ i, ∑ j,
        S.complexMixedObservable (S.differential (f i)) (fun e => conj (S.differential (f i) e))
          (fun e => conj (S.differential (f j) e)) (S.differential (f j)))).re := by
  rw [S.familyObservable_contraction, map_add, Complex.add_re]
  have hp := S.averageComplex_pos_square (S.familyPaired (fun i => S.differential (f i)))
  have hr := S.norm_familyRemainder_le β hβ hb f hP
  have hre := (abs_le.mp (Complex.abs_re_le_norm (S.averageComplexLinear
    (S.familyRemainder (fun i => S.differential (f i)))))).1
  linarith

end ClassicalON.SpinSystem

end

end OAI
