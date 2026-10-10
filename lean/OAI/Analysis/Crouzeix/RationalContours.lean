import Mathlib
import OAI.Analysis.Crouzeix.ContourPolynomials

namespace OAI

/-! Rational Contours. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.integral_deriv_mul_inv_pow_succ_succ (Γ : SmoothContour)
    {a : ℂ} (ha : a ∉ Γ.trace) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2)) = 0 := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    exact ha ((sub_eq_zero.mp he) ▸ mem_image_of_mem Γ.path ht)
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => -(n + 1 : ℂ)⁻¹ * ((Γ.path r - a)⁻¹) ^ (n + 1))
        (deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2)) t := by
    have h := ((((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).inv
      (hnz t ht)).pow (n + 1)).const_mul (-(n + 1 : ℂ)⁻¹)
    convert! h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    simp only [Pi.inv_apply, div_eq_mul_inv, ← inv_pow]
    have hscalar : -(n + 1 : ℂ)⁻¹ * ((n + 1) * (Γ.path t - a)⁻¹ ^ n *
        (-deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ 2)) =
        ((n + 1 : ℂ)⁻¹ * (n + 1)) * deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2) := by
      rw [pow_add]
      ring
    rw [hscalar, inv_mul_cancel₀ hn, one_mul]
  have hc : ContinuousOn (fun t => (Γ.path t - a)⁻¹) (Icc (0 : ℝ) 1) :=
    (Γ.smooth.continuous.sub continuous_const).continuousOn.inv₀ hnz
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 2))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.mul (hc.pow (n + 2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -(n + 1 : ℂ)⁻¹ * ((Γ.path t - a)⁻¹) ^ (n + 1))
    (fun t ht => hder t (by simpa using ht)) hi
  simpa only [Γ.closed, sub_self] using he

theorem SmoothContour.integral_deriv_mul_inv_pow (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.trace) (hind : Γ.index a = 0) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (n + 1)) = 0 := by
  cases n with
  | zero => simpa only [zero_add, pow_one, div_eq_mul_inv] using
      Γ.integral_deriv_div_eq_zero hind
  | succ n => exact Γ.integral_deriv_mul_inv_pow_succ_succ ha n

theorem SmoothContour.integral_deriv_mul_polynomial (Γ : SmoothContour) (p : Polynomial ℂ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * p.eval (Γ.path t)) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · have he (k : ℕ) : (fun t => deriv Γ.path t * (p.coeff k * Γ.path t ^ k)) =
        fun t => p.coeff k * (deriv Γ.path t * Γ.path t ^ k) := by ext t; ring
    simp_rw [he, intervalIntegral.integral_const_mul, Γ.integral_deriv_mul_pow, mul_zero]
    simp
  · intro k _
    exact (Γ.smooth.continuous_deriv_one.mul
      (continuous_const.mul (Γ.smooth.continuous.pow k))).intervalIntegrable _ _

theorem denominator_eq_prod (r : RatFunc ℂ) :
    r.denom = ∏ a ∈ r.denom.roots.toFinset,
      (Polynomial.X - Polynomial.C a) ^ r.denom.roots.count a := by
  classical
  exact ((IsAlgClosed.splits r.denom).eq_prod_roots_of_monic (RatFunc.monic_denom r)).trans
    (Finset.prod_multiset_map_count _ _)

theorem polynomial_quotient_partialFractions (p q : Polynomial ℂ) (hq : q.Monic)
    (S : Set ℂ) (hS : ∀ z ∈ S, q.eval z ≠ 0) :
    ∃ (p₀ : Polynomial ℂ) (c : (a : ℂ) → Fin (q.roots.count a) → ℂ),
      ∀ z ∈ S, p.eval z / q.eval z = p₀.eval z +
        ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a),
          c a j * ((z - a)⁻¹) ^ (j.1 + 1) := by
  classical
  let φ : Polynomial ℂ →+* (S → ℂ) :=
    RingHom.pi (fun z : S => Polynomial.evalRingHom (z : ℂ))
  let : Algebra (Polynomial ℂ) (S → ℂ) := φ.toAlgebra
  let gi : ℂ → S → ℂ := fun a z => ((z : ℂ) - a)⁻¹
  have hmap (p : Polynomial ℂ) (z : S) :
      algebraMap (Polynomial ℂ) (S → ℂ) p z = p.eval (z : ℂ) := rfl
  have hgi (a : ℂ) (ha : a ∈ q.roots.toFinset) :
      gi a * algebraMap (Polynomial ℂ) (S → ℂ) (Polynomial.X - Polynomial.C a) = 1 := by
    ext z
    change ((z : ℂ) - a)⁻¹ * ((Polynomial.X - Polynomial.C a).eval (z : ℂ)) = 1
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply inv_mul_cancel₀
    intro he
    exact hS z z.property ((sub_eq_zero.mp he) ▸
      ((Polynomial.mem_roots hq.ne_zero).mp (Multiset.mem_toFinset.mp ha)))
  obtain ⟨p₀, r, hr, he⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := S → ℂ) (s := q.roots.toFinset) p
    (g := fun a => Polynomial.X - Polynomial.C a)
    (fun a _ => Polynomial.monic_X_sub_C a)
    (fun _ _ _ _ hne => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hne)
    (fun a => q.roots.count a) hgi
  have hconst (a : ℂ) (ha : a ∈ q.roots.toFinset) (j : Fin (q.roots.count a)) :
      r a j = Polynomial.C ((r a j).coeff 0) := by
    apply Polynomial.degree_le_zero_iff.mp
    have h := hr a ha j
    rw [Polynomial.degree_X_sub_C] at h
    exact Order.le_of_lt_succ h
  refine ⟨p₀, fun a j => (r a j).coeff 0, fun z hz => ?_⟩
  have hden : q = ∏ a ∈ q.roots.toFinset, (Polynomial.X - Polynomial.C a) ^ q.roots.count a := by
    exact ((IsAlgClosed.splits q).eq_prod_roots_of_monic hq).trans
      (Finset.prod_multiset_map_count _ _)
  have hez := congrFun he (⟨z, hz⟩ : S)
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply,
    Pi.add_apply, Finset.sum_apply, hmap, gi] at hez
  have hnume : ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a),
        (r a j).eval z * ((z - a)⁻¹) ^ (j.1 + 1) =
      ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a),
        (r a j).coeff 0 * ((z - a)⁻¹) ^ (j.1 + 1) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro j _
    rw [hconst a ha j, Polynomial.eval_C, Polynomial.coeff_C_zero]
  rw [← hnume, ← hez]
  conv_lhs => rw [hden]
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv, Finset.prod_inv_distrib, inv_pow]

theorem SmoothContour.integral_deriv_mul_quotient (Γ : SmoothContour)
    (p q : Polynomial ℂ) (hq : q.Monic)
    (hnz : ∀ z ∈ Γ.trace, q.eval z ≠ 0)
    (hind : ∀ a ∈ q.roots, Γ.index a = 0) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * (p.eval (Γ.path t) / q.eval (Γ.path t))) = 0 := by
  classical
  obtain ⟨p₀, c, he⟩ := polynomial_quotient_partialFractions p q hq Γ.trace hnz
  have ha (a : ℂ) (ha : a ∈ q.roots.toFinset) : a ∉ Γ.trace := by
    intro he
    exact hnz a he ((Polynomial.mem_roots hq.ne_zero).mp (Multiset.mem_toFinset.mp ha))
  have hc (a : ℂ) (ha' : a ∈ q.roots.toFinset) :
      ContinuousOn (fun t : ℝ => (Γ.path t - a)⁻¹) (Icc (0 : ℝ) 1) := by
    apply (Γ.smooth.continuous.sub continuous_const).continuousOn.inv₀
    intro t ht he
    exact ha a ha' ⟨t, ht, sub_eq_zero.mp he⟩
  have hi (a : ℂ) (ha' : a ∈ q.roots.toFinset) (j : Fin (q.roots.count a)) :
      IntervalIntegrable (fun t : ℝ => deriv Γ.path t *
        (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.mul (continuousOn_const.mul ((hc a ha').pow _))
  have hiinner (a : ℂ) (ha' : a ∈ q.roots.toFinset) :
      IntervalIntegrable (fun t : ℝ => ∑ j : Fin (q.roots.count a), deriv Γ.path t *
        (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) MeasureTheory.volume 0 1 := by
    exact IntervalIntegrable.congr (fun t _ => Finset.sum_apply t _ _)
      (IntervalIntegrable.sum Finset.univ (fun j _ => hi a ha' j))
  have hisum : IntervalIntegrable (fun t : ℝ =>
      ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a), deriv Γ.path t *
        (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) MeasureTheory.volume 0 1 := by
    exact IntervalIntegrable.congr (fun t _ => Finset.sum_apply t _ _)
      (IntervalIntegrable.sum q.roots.toFinset hiinner)
  have hip : IntervalIntegrable (fun t => deriv Γ.path t * p₀.eval (Γ.path t))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Γ.smooth.continuous_deriv_one.mul (p₀.continuous.comp Γ.smooth.continuous)).intervalIntegrable 0 1
  calc
    _ = ∫ t in (0 : ℝ)..1, deriv Γ.path t * p₀.eval (Γ.path t) +
        ∑ a ∈ q.roots.toFinset, ∑ j : Fin (q.roots.count a), deriv Γ.path t *
          (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [he (Γ.path t) (mem_image_of_mem _ (by simpa using ht))]
      simp only [mul_add, Finset.mul_sum]
    _ = 0 := by
      rw [intervalIntegral.integral_add hip hisum, Γ.integral_deriv_mul_polynomial, zero_add,
        intervalIntegral.integral_finsetSum hiinner]
      apply Finset.sum_eq_zero
      intro a ha'
      rw [intervalIntegral.integral_finsetSum (fun j _ => hi a ha' j)]
      apply Finset.sum_eq_zero
      intro j _
      have heq : (fun t : ℝ => deriv Γ.path t * (c a j * ((Γ.path t - a)⁻¹) ^ (j.1 + 1))) =
          fun t => c a j * (deriv Γ.path t * ((Γ.path t - a)⁻¹) ^ (j.1 + 1)) := by
        ext t
        ring
      rw [heq, intervalIntegral.integral_const_mul,
        Γ.integral_deriv_mul_inv_pow (ha a ha') (hind a (Multiset.mem_toFinset.mp ha')), mul_zero]

theorem contourEval_pow_mul_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : ∀ n : ℕ, (∫ t in (0 : ℝ)..1,
      deriv Γ.path t * (Γ.path t ^ n * f (Γ.path t))) = 0) (n : ℕ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n * f z) =
      A ^ n * contourEval A Γ.toSmoothContour f := by
  induction n with
  | zero => simp only [pow_zero, one_mul]
  | succ n ih =>
    have he := contourEval_mul_id_of_integral_eq_zero A Γ (f := fun z => z ^ n * f z)
      ((continuous_pow n).continuousOn.mul hf) (hzero n)
    simpa only [← mul_assoc, ← pow_succ', ih] using he

theorem contourEval_polynomial_mul_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : ∀ n : ℕ, (∫ t in (0 : ℝ)..1,
      deriv Γ.path t * (Γ.path t ^ n * f (Γ.path t))) = 0) (p : Polynomial ℂ) :
    contourEval A Γ.toSmoothContour (fun z => p.eval z * f z) =
      Polynomial.aeval A p * contourEval A Γ.toSmoothContour f := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Polynomial.aeval_eq_sum_range]
  rw [contourEval_sum A Γ (Finset.range (p.natDegree + 1))
    (fun k z => (p.coeff k * z ^ k) * f z)
    (fun k _ => (continuousOn_const.mul (continuous_pow k).continuousOn).mul hf)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [mul_assoc]
  rw [contourEval_const_mul, contourEval_pow_mul_of_integral_eq_zero A Γ hf hzero,
    smul_mul_assoc]

theorem CalculusContour.inside_subset {K U : Set ℂ} (Γ : CalculusContour K U) : K ⊆ U := by
  intro z hz
  by_contra he
  exact one_ne_zero ((Γ.index_inside z hz).symm.trans (Γ.index_outside z he))

theorem contourEval_quotient [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    (p q : Polynomial ℂ) (hq : q.Monic) (hqu : ∀ z ∈ U, q.eval z ≠ 0) :
    contourEval A Γ.toSmoothContour (fun z => p.eval z / q.eval z) =
      Polynomial.aeval A p * Ring.inverse (Polynomial.aeval A q) := by
  have hqt (z : ℂ) (hz : z ∈ Γ.toSmoothContour.trace) : q.eval z ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := hz
    exact hqu _ (Γ.avoids t ht).1
  have hind (a : ℂ) (ha : a ∈ q.roots) : Γ.toSmoothContour.index a = 0 := by
    apply Γ.index_outside
    intro hau
    exact hqu a hau ((Polynomial.mem_roots hq.ne_zero).mp ha)
  have hzero (n : ℕ) : (∫ t in (0 : ℝ)..1,
      deriv Γ.path t * (Γ.path t ^ n * (p.eval (Γ.path t) / q.eval (Γ.path t)))) = 0 := by
    have hi := Γ.toSmoothContour.integral_deriv_mul_quotient
      (Polynomial.X ^ n * p) q hq hqt hind
    simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, mul_div_assoc] using hi
  have hf : ContinuousOn (fun z => p.eval z / q.eval z) Γ.toSmoothContour.trace :=
    p.continuous.continuousOn.div q.continuous.continuousOn hqt
  have he := contourEval_polynomial_mul_of_integral_eq_zero A Γ hf hzero q
  have heq : contourEval A Γ.toSmoothContour (fun z => q.eval z * (p.eval z / q.eval z)) =
      Polynomial.aeval A p := by
    calc
      _ = contourEval A Γ.toSmoothContour p.eval := by
        apply contourEval_congr
        intro z hz
        exact mul_div_cancel₀ _ (hqt z hz)
      _ = _ := contourEval_polynomial A Γ p
  have hu : IsUnit (Polynomial.aeval A q) :=
    isUnit_polynomial_aeval A q (fun z hz => hqu z (Γ.inside_subset hz))
  apply hu.mul_left_cancel
  calc
    _ = Polynomial.aeval A p := he.symm.trans heq
    _ = Polynomial.aeval A q * (Polynomial.aeval A p * Ring.inverse (Polynomial.aeval A q)) := by
      rw [← mul_assoc, ((Commute.all q p).map (Polynomial.aeval A)).eq,
        mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

theorem contourEval_rational [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (r : RatFunc ℂ)
    (hr : ∀ z ∈ U, r.denom.eval z ≠ 0) :
    contourEval A Γ.toSmoothContour (fun z => RatFunc.eval (RingHom.id ℂ) z r) =
      rationalEval A r := by
  simpa only [rationalEval, RatFunc.eval, Polynomial.eval₂_id] using
    contourEval_quotient A Γ r.num r.denom (RatFunc.monic_denom r) hr

theorem matrixContourEval_matrixRationalFunction [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m : ℕ} (R : RationalMatrix m) (hR : PolesOutside U R) :
    matrixContourEval A Γ.toSmoothContour (matrixRationalFunction R) = matrixRationalEval A R := by
  unfold matrixContourEval matrixRationalEval matrixRationalFunction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [contourEval_rational A Γ (R i j) (hR i j)]

theorem holomorphicEval_rational [CompleteSpace H] [Nontrivial H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (r : RatFunc ℂ)
    (hr : ∀ z ∈ U, r.denom.eval z ≠ 0) :
    holomorphicEval A U (fun z => RatFunc.eval (RingHom.id ℂ) z r) = rationalEval A r := by
  unfold holomorphicEval
  rw [dite_eq_left (show Nonempty (CalculusContour (numericalClosure A) U) from ⟨Γ⟩)]
  exact contourEval_rational A _ r hr

theorem matrixHolomorphicEval_matrixRationalFunction [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m : ℕ} (R : RationalMatrix m) (hR : PolesOutside U R) :
    matrixHolomorphicEval A U (matrixRationalFunction R) = matrixRationalEval A R := by
  unfold matrixHolomorphicEval matrixRationalEval matrixRationalFunction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [holomorphicEval_rational A Γ (R i j) (hR i j)]

theorem rational_poleFree_neighborhood {m : ℕ} {K : Set ℂ}
    (R : RationalMatrix m) (hR : PolesOutside K R) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ PolesOutside U R ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) := by
  let U : Set ℂ := ⋂ i, ⋂ j, {z : ℂ | (R i j).denom.eval z ≠ 0}
  have hne : PolesOutside U R := by
    intro i j z hz
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) j
  refine ⟨U, ?_, ?_, hne, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (R i j).denom.continuous
  · intro z hz
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j => hR i j z hz))
  · intro i j
    simp only [matrixRationalFunction, RatFunc.eval, Polynomial.eval₂_id]
    exact DifferentiableOn.div (𝕜 := ℂ) (𝕜' := ℂ)
      (R i j).num.differentiableOn (R i j).denom.differentiableOn (hne i j)

theorem rational_conclusion_of_holomorphic_bound [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {m : ℕ}
    (hhol : ∀ (U : Set ℂ) (F : ℂ → Coeff m), IsOpen U →
      numericalClosure A ⊆ U → EntrywiseHolomorphic U F →
      Nonempty (CalculusContour (numericalClosure A) U) ∧
      ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F)
    (R : RationalMatrix m) (hR : PolesOutside (numericalClosure A) R) :
    (∀ i j, IsUnit (Polynomial.aeval A (R i j).denom)) ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalClosure A) (matrixRationalFunction R) ∧
    (∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixRationalFunction R) =
        ‖matrixRationalFunction R z‖) ∧
    ∃ U : Set ℂ, IsOpen U ∧ numericalClosure A ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      matrixRationalEval A R = matrixHolomorphicEval A U (matrixRationalFunction R) := by
  obtain ⟨U, hU, hKU, hpoles, hF⟩ := rational_poleFree_neighborhood R hR
  obtain ⟨⟨Γ⟩, hb⟩ := hhol U (matrixRationalFunction R) hU hKU hF
  have he := matrixHolomorphicEval_matrixRationalFunction A Γ R hpoles
  refine ⟨rational_denominators_isUnit A R hR, ?_,
    rational_sup_attained A R hR, U, hU, hKU, hF, he.symm⟩
  rwa [he] at hb

end CrouzeixHilbert

end

end OAI
