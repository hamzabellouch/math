import OAI.AlgebraicGeometry.PlaneCurves.GaussianBounds
import OAI.AlgebraicGeometry.PlaneCurves.NormalizedExponents
import OAI.AlgebraicGeometry.PlaneCurves.QuotientSections
import OAI.AlgebraicGeometry.PlaneCurves.ThetaProducts

namespace OAI

/-!
# Normalized and marked theta sections of cubic divisors
-/

section

/-! Three nonzero complex marks with prescribed product and distinct period
orbits. Countable avoidance is applied to genuine univariate polynomials. -/
noncomputable section
namespace Nagata.W08

theorem exists_complex_nonroot {ι : Type*} [Countable ι]
    (p : ι → Polynomial ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ b : ℂ, ∀ i, (p i).eval b ≠ 0 := by
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.cantor Cardinal.aleph0)
  let B : Set ℂ := ⋃ i, {b | (p i).IsRoot b}
  have hB : B.Countable := Set.countable_iUnion fun i =>
    (Polynomial.finite_setOfPred_isRoot (hp i)).countable
  have hex : ∃ b : ℂ, b ∉ B := by
    by_contra h
    have hu : B = Set.univ := Set.eq_univ_of_forall fun b =>
      Classical.not_not.mp (fun hb => h ⟨b, hb⟩)
    exact Set.not_countable_univ (hu ▸ hB)
  obtain ⟨b, hb⟩ := hex
  exact ⟨b, fun i hi => hb (Set.mem_iUnion.mpr ⟨i, hi⟩)⟩

open Polynomial in
theorem exists_cubic_second_mark {τ a γ : ℂ} (hτ : τ ≠ 0) (ha : a ≠ 0) :
    ∃ b : ℂ, b ≠ 0 ∧
      (∀ k : ℤ, b ≠ a * τ ^ k) ∧
      (∀ k : ℤ, a ^ 2 * b * τ ^ k + γ ≠ 0) ∧
      (∀ k : ℤ, a * b ^ 2 * τ ^ k + γ ≠ 0) := by
  let p : Fin 4 × ℤ → Polynomial ℂ := fun i =>
    if i.1 = 0 then X else if i.1 = 1 then X - C (a * τ ^ i.2)
    else if i.1 = 2 then C (a ^ 2 * τ ^ i.2) * X + C γ
    else C (a * τ ^ i.2) * X ^ 2 + C γ
  have hp : ∀ i, p i ≠ 0 := by
    rintro ⟨j, k⟩ he
    fin_cases j
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      norm_num [p] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      norm_num [p] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      change (C (a ^ 2 * τ ^ k) * X + C γ).coeff 1 = (0 : Polynomial ℂ).coeff 1 at hc
      simp only [coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at hc
      norm_num [ha, zpow_ne_zero k hτ] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 2) he
      change (C (a * τ ^ k) * X ^ 2 + C γ).coeff 2 = (0 : Polynomial ℂ).coeff 2 at hc
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C, coeff_zero] at hc
      norm_num [ha, zpow_ne_zero k hτ] at hc
  obtain ⟨b, hb⟩ := exists_complex_nonroot p hp
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simpa [p] using hb (0, 0)
  · intro k
    simpa [p, sub_ne_zero] using hb (1, k)
  · intro k
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using hb (2, k)
  · intro k
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using hb (3, k)

end Nagata.W08

end
end

section

/-!
Packaging of the actual source theta product as a genuine holomorphic
multiplier section. This claims no divisor, degree, dimension, or plane embedding.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W21

/-- A translate of the source theta product defines a section with multiplier `-a`. -/
def thetaProductSection {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    automorphicSections τ 1 (-a) :=
  sectionOfFunction hτ0 (fun z ↦ thetaProduct τ (z / a))
    (fun z hz ↦ by
      have hd := thetaProduct_differentiableAt hτ (div_ne_zero hz ha)
      have hc : DifferentiableAt ℂ (fun z : ℂ ↦ z / a) z := by
        simp only [div_eq_mul_inv]
        exact differentiableAt_id.mul_const _
      exact hd.comp z hc)
    (fun z hz ↦ by
      simpa only [zpow_neg_one] using thetaProduct_scaled_automorphy hτ hτ0 ha hz)

/-- The packaged section has exactly the source covering-frame scalar values on `ℂ*`. -/
@[simp] theorem thetaProductSection_apply {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    (thetaProductSection hτ hτ0 ha).val z = thetaProduct τ (z / a) := by
  change normalizeAtZero (fun w ↦ thetaProduct τ (w / a)) z = thetaProduct τ (z / a)
  exact normalizeAtZero_of_ne _ hz

end Nagata.W08

end
end

section

/-! A prescribed nonzero mark extends to three distinct multiplicative-torus
orbits with the exact degree-three section multiplier. -/
noncomputable section
namespace Nagata.W08

theorem orbit_avoidance_symm {τ x y : ℂ} (hτ : τ ≠ 0)
    (h : ∀ k : ℤ, x ≠ y * τ ^ k) : ∀ k : ℤ, y ≠ x * τ ^ k := by
  intro k he
  apply h (-k)
  rw [he, mul_assoc, ← zpow_add₀ hτ]
  simp

theorem exists_three_distinct_orbit_marks {τ a γ : ℂ}
    (hτ : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) :
    ∃ m : Fin 3 → ℂ, m 0 = a ∧ (∀ i, m i ≠ 0) ∧
      Pairwise (fun i j => ∀ k : ℤ, m i ≠ m j * τ ^ k) ∧
      (∏ i, -m i) = γ := by
  obtain ⟨b, hb, hba, hlinear, hquadratic⟩ := exists_cubic_second_mark (γ := γ) hτ ha
  let c : ℂ := -γ / (a * b)
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hγ) (mul_ne_zero ha hb)
  have hca : ∀ k : ℤ, c ≠ a * τ ^ k := by
    intro k he
    have heq : -γ = (a * τ ^ k) * (a * b) :=
      (div_eq_iff (mul_ne_zero ha hb)).mp he
    apply hlinear k
    calc a ^ 2 * b * τ ^ k + γ = (a * τ ^ k) * (a * b) + γ := by ring
      _ = 0 := by rw [← heq]; ring
  have hcb : ∀ k : ℤ, c ≠ b * τ ^ k := by
    intro k he
    have heq : -γ = (b * τ ^ k) * (a * b) :=
      (div_eq_iff (mul_ne_zero ha hb)).mp he
    apply hquadratic k
    calc a * b ^ 2 * τ ^ k + γ = (b * τ ^ k) * (a * b) + γ := by ring
      _ = 0 := by rw [← heq]; ring
  have hab := orbit_avoidance_symm hτ hba
  have hac := orbit_avoidance_symm hτ hca
  have hbc := orbit_avoidance_symm hτ hcb
  refine ⟨![a, b, c], rfl, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
    dsimp [c]
    field_simp [ha, hb]

end Nagata.W08

end
end

section

/-! Actual finite marked theta products as genuine holomorphic multiplier sections. -/
noncomputable section
namespace Nagata.W08

open Nagata.W21
open scoped BigOperators

/-- The marked product has the exact tensor-product multiplier. -/
theorem markedThetaProduct_automorphy {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    markedThetaProduct τ a (τ * z) =
      (∏ i, -a i) * z ^ (-(Fintype.card ι : ℤ)) * markedThetaProduct τ a z := by
  classical
  unfold markedThetaProduct
  simp_rw [thetaProduct_scaled_automorphy hτ hτ0 (ha _) hz]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, zpow_neg, zpow_natCast, inv_pow]

/-- The actual marked divisor product as a genuine section of degree `card ι`. -/
def markedThetaSection {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    automorphicSections τ (Fintype.card ι : ℤ) (∏ i, -a i) :=
  sectionOfFunction hτ0 (markedThetaProduct τ a)
    (fun _ hz ↦ markedThetaProduct_differentiableAt hτ ha hz)
    (fun _ hz ↦ markedThetaProduct_automorphy hτ hτ0 a ha hz)

@[simp] theorem markedThetaSection_apply {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    (markedThetaSection hτ hτ0 a ha).val z = markedThetaProduct τ a z := by
  change normalizeAtZero (markedThetaProduct τ a) z = markedThetaProduct τ a z
  exact normalizeAtZero_of_ne _ hz

/-- The nine-mark multiplier retains the source's negative sign. -/
theorem markedThetaMultiplier_nine (a : Fin 9 → ℂ) :
    (∏ i, -a i) = -(∏ i, a i) := by
  rw [Finset.prod_neg]
  norm_num

end Nagata.W08

end
end

section

/-! Global convergence and entire holomorphy of the literal normalized source
series, obtained from explicit summable Gaussian bounds at every allowed period. -/
noncomputable section
namespace Nagata.W08
open Nagata.W07

theorem normalizedThetaTerm_summable {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτone : τ < 1) (a K : ℝ) {ε : ℂ} (hε : ε ≠ 0) (x : ℂ) :
    Summable (fun p : ℤ ↦ normalizedThetaTerm n a K ε τ p x) := by
  have hs := Nagata.W02.summable_normalizedThetaDerivativeTerm_allTau
    (a := a) (K := K) hn hτ hτone hε 0 x
  simpa only [normalizedThetaDerivativeTerm, pow_zero, one_mul] using hs.of_norm

theorem normalizedThetaSeries_differentiable {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτone : τ < 1) (a K : ℝ) {ε : ℂ} (hε : ε ≠ 0) :
    Differentiable ℂ (fun x : ℂ ↦ ∑' p : ℤ, normalizedThetaTerm n a K ε τ p x) :=
  Nagata.W02.differentiable_normalizedThetaSeries_allTau hn hτ hτone hε

end Nagata.W08

end
end

section

/-! Exact divisor-support and simple-zero facts for the actual degree-one theta section. -/
namespace Nagata.W08

open Nagata.W21 Filter Topology

/-- The actual section has exactly the prescribed marked period orbit as its zero set on `ℂ*`. -/
theorem thetaProductSection_zero_iff {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    (thetaProductSection hτ hτ0 ha).val z = 0 ↔ ∃ k : ℤ, z = a * τ ^ k := by
  rw [thetaProductSection_apply hτ hτ0 ha hz]
  exact thetaProduct_scaled_eq_zero_iff hτ hτ0 ha hz

@[simp] theorem thetaProductSection_at_mark {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    (thetaProductSection hτ hτ0 ha).val a = 0 := by
  rw [thetaProductSection_apply hτ hτ0 ha ha, div_self ha]
  exact thetaProduct_one hτ

/-- The zero extension changes no derivative at a genuine point. -/
theorem thetaProductSection_deriv {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    deriv (thetaProductSection hτ hτ0 ha).val z =
      deriv (fun w ↦ thetaProduct τ (w / a)) z := by
  apply Filter.EventuallyEq.deriv_eq
  exact normalizeAtZero_eventuallyEq (fun w ↦ thetaProduct τ (w / a)) hz

/-- Every actual section zero has nonzero derivative in the covering coordinate. -/
theorem thetaProductSection_zero_has_nonzero_deriv {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0)
    (hf : (thetaProductSection hτ hτ0 ha).val z = 0) :
    deriv (thetaProductSection hτ hτ0 ha).val z ≠ 0 := by
  rw [thetaProductSection_deriv hτ hτ0 ha hz]
  apply thetaProduct_scaled_zero_has_nonzero_deriv hτ hτ0 ha hz
  simpa only [thetaProductSection_apply hτ hτ0 ha hz] using hf

/-- The constructed genuine theta section is nonzero. -/
theorem thetaProductSection_ne_zero {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    thetaProductSection hτ hτ0 ha ≠ 0 := by
  intro hzero
  have hd := thetaProductSection_zero_has_nonzero_deriv hτ hτ0 ha ha
    (thetaProductSection_at_mark hτ hτ0 ha)
  have hfun : (thetaProductSection hτ hτ0 ha).val = (fun _ : ℂ ↦ 0) :=
    congrArg Subtype.val hzero
  apply hd
  rw [hfun, deriv_const]

end Nagata.W08

end

section

/-! Exact zero-set and derivative bridges for the actual marked theta section. -/
namespace Nagata.W08

open Nagata.W21 Filter Topology

/-- The marked section has precisely the marked period orbits as zeros on `ℂ*`. -/
theorem markedThetaSection_zero_iff {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    (markedThetaSection hτ hτ0 a ha).val z = 0 ↔ ∃ i, ∃ k : ℤ, z = a i * τ ^ k := by
  rw [markedThetaSection_apply hτ hτ0 a ha hz]
  exact markedThetaProduct_eq_zero_iff hτ hτ0 ha hz

@[simp] theorem markedThetaSection_at_mark {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (i : ι) : (markedThetaSection hτ hτ0 a ha).val (a i) = 0 :=
  (markedThetaSection_zero_iff hτ hτ0 a ha (ha i)).mpr ⟨i, 0, by simp⟩

/-- The forced zero value outside the genuine domain changes no derivative on `ℂ*`. -/
theorem markedThetaSection_deriv {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    deriv (markedThetaSection hτ hτ0 a ha).val z = deriv (markedThetaProduct τ a) z := by
  apply Filter.EventuallyEq.deriv_eq
  exact normalizeAtZero_eventuallyEq (markedThetaProduct τ a) hz

/-- Distinct marked orbits give simple zeros of the actual section. -/
theorem markedThetaSection_zero_has_nonzero_deriv {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k))
    {z : ℂ} (hz : z ≠ 0) (hzero : (markedThetaSection hτ hτ0 a ha).val z = 0) :
    deriv (markedThetaSection hτ hτ0 a ha).val z ≠ 0 := by
  rw [markedThetaSection_deriv hτ hτ0 a ha hz]
  apply markedThetaProduct_zero_has_nonzero_deriv hτ hτ0 ha hdisjoint hz
  simpa only [markedThetaSection_apply hτ hτ0 a ha hz] using hzero

/-- A nonempty disjoint marked family gives a nonzero genuine section. -/
theorem markedThetaSection_ne_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k)) :
    markedThetaSection hτ hτ0 a ha ≠ 0 := by
  classical
  intro hzero
  let i : ι := Classical.arbitrary ι
  have hd := markedThetaSection_zero_has_nonzero_deriv hτ hτ0 a ha hdisjoint (ha i)
    (markedThetaSection_at_mark hτ hτ0 a ha i)
  have hfun : (markedThetaSection hτ hτ0 a ha).val = (fun _ : ℂ ↦ 0) :=
    congrArg Subtype.val hzero
  apply hd
  rw [hfun, deriv_const]

end Nagata.W08

end

section

/-!
An actual global holomorphic section constructed from the normalized Laurent
series. The global logarithm-branch gluing and multiplier law are proved;
linear independence, dimension, divisors and the projective embedding are not
asserted by this construction.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W07

/-- The normalized integer-frequency theta series as a genuine global multiplier section. -/
def normalizedThetaSection (n K : ℤ) (hn : 0 < n) (a : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    automorphicSections (τ : ℂ) n (ε * ((τ ^ ((K : ℝ) - a) : ℝ) : ℂ)) :=
  automorphicSectionOfPeriodicFunction
    (fun x ↦ ∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x)
    (normalizedThetaSeries_differentiable (by exact_mod_cast hn) hτ hτone a (K : ℝ) hε)
    (fun x k ↦ normalizedThetaSeries_integerPeriod n K k a ε τ x)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun x ↦ by
      rw [← Complex.ofReal_log hτ.le]
      simpa using normalizedThetaSeries_realShift (n : ℝ) a (K : ℝ) hε hτ x)

/-- Exact agreement with the normalized source series in every exponential coordinate. -/
theorem normalizedThetaSection_exp (n K : ℤ) (hn : 0 < n) (a : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    (normalizedThetaSection n K hn a hε hτ hτone).val (Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x := by
  apply automorphicSectionOfPeriodicFunction_exp

end Nagata.W08

end
end

section

/-!
The actual global section, evaluated at the moving center `τ^x₀ * exp x`,
recovers exactly the normalized source series after the source scalar scaling.
-/
noncomputable section
namespace Nagata.W08

open Nagata.W07

/-- Centering the genuine section agrees with centering each actual source summand. -/
theorem normalizedThetaSection_centered (n K : ℤ) (hn : 0 < n) (a x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) *
      (normalizedThetaSection n K hn a hε hτ hτone).val
        (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) (a + x₀ * (n : ℝ)) (K : ℝ) ε τ p x := by
  have he : Complex.exp (((x₀ * Real.log τ : ℝ) : ℂ)) = ((τ ^ x₀ : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
    congr 1
    rw [mul_comm x₀ (Real.log τ)]
  have hcenter : Complex.exp (((x₀ * Real.log τ : ℝ) : ℂ) + x) =
      ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x := by
    rw [Complex.exp_add, he]
  rw [← hcenter, normalizedThetaSection_exp, ← tsum_mul_left]
  exact tsum_congr fun p ↦ normalizedThetaTerm_shift hτ (n : ℝ) a (K : ℝ) x₀ ε x p

end Nagata.W08

end
end

section

noncomputable section
namespace Nagata.W08

theorem exists_cubic_three_simple_zeros {τ γ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (ha : a ≠ 0) :
    ∃ (m : Fin 3 → ℂ) (s : automorphicSections τ 3 γ),
      m 0 = a ∧ (∀ i, m i ≠ 0) ∧
      Pairwise (fun i j => ∀ k : ℤ, m i ≠ m j * τ ^ k) ∧
      (∏ i, -m i) = γ ∧ s ≠ 0 ∧ s.val a = 0 ∧
      (∀ z : ℂ, z ≠ 0 → (s.val z = 0 ↔ ∃ i, ∃ k : ℤ, z = m i * τ ^ k)) ∧
      (∀ z : ℂ, z ≠ 0 → s.val z = 0 → deriv s.val z ≠ 0) := by
  obtain ⟨m, hm0, hm, hdisjoint, hprod⟩ := exists_three_distinct_orbit_marks hτ0 ha hγ
  let f := markedThetaSection hτ hτ0 m hm
  have hf : f.val ∈ automorphicSections τ 3 γ := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, hprod] using f.property
  let s : automorphicSections τ 3 γ := ⟨f.val, hf⟩
  have hs : s ≠ 0 := by
    intro he
    apply markedThetaSection_ne_zero hτ hτ0 m hm hdisjoint
    apply Subtype.ext
    exact congrArg (fun v : automorphicSections τ 3 γ => v.val) he
  refine ⟨m, s, hm0, hm, hdisjoint, hprod, hs, ?_, ?_, ?_⟩
  · rw [← hm0]
    exact markedThetaSection_at_mark hτ hτ0 m hm 0
  · intro z hz
    exact markedThetaSection_zero_iff hτ hτ0 m hm hz
  · intro z hz hzero
    exact markedThetaSection_zero_has_nonzero_deriv hτ hτ0 m hm hdisjoint hz hzero

theorem exists_cubic_three_simple_zeros_pos_real {τ : ℝ} {γ a : ℂ}
    (hτ : 0 < τ) (hτone : τ < 1) (hγ : γ ≠ 0) (ha : a ≠ 0) :
    ∃ (m : Fin 3 → ℂ) (s : automorphicSections (τ : ℂ) 3 γ),
      m 0 = a ∧ (∀ i, m i ≠ 0) ∧
      Pairwise (fun i j => ∀ k : ℤ, m i ≠ m j * (τ : ℂ) ^ k) ∧
      (∏ i, -m i) = γ ∧ s ≠ 0 ∧ s.val a = 0 ∧
      (∀ z : ℂ, z ≠ 0 → (s.val z = 0 ↔ ∃ i, ∃ k : ℤ, z = m i * (τ : ℂ) ^ k)) ∧
      (∀ z : ℂ, z ≠ 0 → s.val z = 0 → deriv s.val z ≠ 0) :=
  exists_cubic_three_simple_zeros (positivePeriod_norm_lt_one hτ hτone)
    (Complex.ofReal_ne_zero.mpr hτ.ne') hγ ha

end Nagata.W08

end
end

end OAI
