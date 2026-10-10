import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.Moments

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
def triangleDoubleArea (p₀ p₁ p₂ : ℝ × ℝ) : ℝ :=
  |(p₁.1 - p₀.1) * (p₂.2 - p₀.2) - (p₂.1 - p₀.1) * (p₁.2 - p₀.2)|

theorem triangle_subset_balanced (p₀ p₁ p₂ : ℝ × ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (_h01 : p₀.2 ≤ p₁.2) (_h12 : p₁.2 ≤ p₂.2)
    (hrange : p₂.2 - p₀.2 = ρ)
    (harea : triangleDoubleArea p₀ p₁ p₂ = ρ ^ 2) :
    ∃ shear sign : ℝ, sign ^ 2 = 1 ∧
      convexHull ℝ {p₀, p₁, p₂} ⊆
        balancedStrip ρ (p₁.2 - p₀.2) p₀.1 p₀.2 shear sign := by
  let shear := (p₂.1 - p₀.1) / ρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hs : shear * ρ = p₂.1 - p₀.1 := div_mul_cancel₀ _ hρne
  obtain ⟨sign, hsign, hm⟩ : ∃ sign : ℝ, sign ^ 2 = 1 ∧
      sign * (p₁.1 - p₀.1 - shear * (p₁.2 - p₀.2)) = ρ := by
    change |(p₁.1 - p₀.1) * (p₂.2 - p₀.2) -
      (p₂.1 - p₀.1) * (p₁.2 - p₀.2)| = ρ ^ 2 at harea
    rw [hrange] at harea
    rcases (abs_eq (sq_nonneg ρ)).mp harea with h | h
    · refine ⟨1, by norm_num, ?_⟩
      apply (mul_left_inj' hρne).mp
      dsimp [shear]
      field_simp
      nlinarith [h]
    · refine ⟨-1, by norm_num, ?_⟩
      apply (mul_left_inj' hρne).mp
      dsimp [shear]
      field_simp
      nlinarith [h]
  refine ⟨shear, sign, hsign, ?_⟩
  apply convexHull_min _ (convex_balancedStrip _ _ _ _ _ _)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp <;> subst p
  · have ht : transverse p₀.1 p₀.2 shear sign p₀ = 0 := by simp [transverse]
    change 0 ≤ transverse p₀.1 p₀.2 shear sign p₀ ∧ _
    rw [ht]
    simp only [mul_zero, sub_self, mul_zero, le_refl, true_and]
    have : p₀.2 + ρ - p₀.2 = ρ := by ring
    rw [this]
    positivity
  · change 0 ≤ sign * (p₁.1 - p₀.1 - shear * (p₁.2 - p₀.2)) ∧ _
    change 0 ≤ transverse p₀.1 p₀.2 shear sign p₁ ∧
      (p₁.2 - p₀.2) * transverse p₀.1 p₀.2 shear sign p₁ ≤ _ ∧ _
    have ht : transverse p₀.1 p₀.2 shear sign p₁ = ρ := hm
    rw [ht]
    refine ⟨hρ.le, ?_, ?_⟩ <;> nlinarith
  · have ht : transverse p₀.1 p₀.2 shear sign p₂ = 0 := by
      dsimp [transverse]
      rw [hrange, hs]
      ring
    change 0 ≤ transverse p₀.1 p₀.2 shear sign p₂ ∧ _
    rw [ht]
    refine ⟨le_refl _, ?_, ?_⟩
    · rw [hrange]
      nlinarith
    · have : p₀.2 + ρ - p₂.2 = 0 := by linarith
      rw [this]
      simp

theorem triangle_euler_test (p₀ p₁ p₂ : ℝ × ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (h01 : p₀.2 ≤ p₁.2) (h12 : p₁.2 ≤ p₂.2)
    (hrange : p₂.2 - p₀.2 = ρ)
    (harea : triangleDoubleArea p₀ p₁ p₂ = ρ ^ 2)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ convexHull ℝ {p₀, p₁, p₂})
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : ρ < (m : ℝ)) : ¬ EulerJetZero s c m := by
  obtain ⟨shear, sign, hsign, hsub⟩ :=
    triangle_subset_balanced p₀ p₁ p₂ ρ hρ h01 h12 hrange harea
  exact balanced_triangle_euler_test ρ (p₁.2 - p₀.2) p₀.1 p₀.2 shear sign
    hρ (sub_nonneg.mpr h01) (by linarith) hsign s hs
    (fun p hp => hsub (hsupp p hp)) c hc m hm

noncomputable def fallingSequence : Polynomial.Sequence ℂ where
  elems' := descPochhammer ℂ
  degree_eq' n := by
    rw [Polynomial.degree_eq_natDegree (monic_descPochhammer ℂ n).ne_zero,
      descPochhammer_natDegree]

theorem linearMap_zero_power_of_falling (L : Polynomial ℂ →ₗ[ℂ] ℂ) (n : ℕ)
    (h : ∀ i ≤ n, L (descPochhammer ℂ i) = 0) : L (Polynomial.X ^ n) = 0 := by
  have hspan : Submodule.span ℂ (fallingSequence '' Set.Iic n) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro p ⟨i, hi, rfl⟩
    exact h i hi
  have hunit (i : ℕ) (_ : i ≤ n) : IsUnit (fallingSequence i).leadingCoeff := by
    change IsUnit (descPochhammer ℂ i).leadingCoeff
    rw [(monic_descPochhammer ℂ i).leadingCoeff]
    exact isUnit_one
  rw [fallingSequence.span_degreeLE hunit] at hspan
  apply hspan
  simp only [Polynomial.mem_degreeLE, Polynomial.degree_X_pow, le_refl]

noncomputable def polynomialMoment (xs : Finset ℤ) (d : ℤ → ℂ) :
    Polynomial ℂ →ₗ[ℂ] ℂ :=
  ∑ x ∈ xs, d x • Polynomial.leval (x : ℂ)

@[simp] theorem polynomialMoment_apply (xs : Finset ℤ) (d : ℤ → ℂ) (p : Polynomial ℂ) :
    polynomialMoment xs d p = ∑ x ∈ xs, d x * p.eval (x : ℂ) := by
  simp [polynomialMoment]

def FallingJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    ∑ y ∈ rows s, (∑ x ∈ row s y,
      c (x, y) * (descPochhammer ℂ a).eval (x : ℂ)) *
        (descPochhammer ℂ b).eval (y : ℂ) = 0

theorem fallingJetZero_eulerJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (m : ℕ) (hj : FallingJetZero s c m) : EulerJetZero s c m := by
  intro a b hab
  let L : Polynomial ℂ →ₗ[ℂ] ℂ :=
    ∑ y ∈ rows s, (y : ℂ) ^ b • polynomialMoment (row s y) (fun x => c (x, y))
  have hL (i : ℕ) (hi : i ≤ a) : L (descPochhammer ℂ i) = 0 := by
    let d : ℤ → ℂ := fun y => ∑ x ∈ row s y,
      c (x, y) * (descPochhammer ℂ i).eval (x : ℂ)
    have hM (j : ℕ) (hj' : j ≤ b) :
        polynomialMoment (rows s) d (descPochhammer ℂ j) = 0 := by
      simpa only [polynomialMoment_apply] using hj i j (by omega)
    have hpow := linearMap_zero_power_of_falling (polynomialMoment (rows s) d) b hM
    simpa [L, d, mul_comm] using hpow
  have hpow := linearMap_zero_power_of_falling L a hL
  simpa [L, rowMoment, mul_comm] using hpow

theorem triangle_falling_test (p₀ p₁ p₂ : ℝ × ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (h01 : p₀.2 ≤ p₁.2) (h12 : p₁.2 ≤ p₂.2)
    (hrange : p₂.2 - p₀.2 = ρ)
    (harea : triangleDoubleArea p₀ p₁ p₂ = ρ ^ 2)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ convexHull ℝ {p₀, p₁, p₂})
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : ρ < (m : ℝ)) : ¬ FallingJetZero s c m := by
  intro hj
  exact triangle_euler_test p₀ p₁ p₂ ρ hρ h01 h12 hrange harea s hs hsupp c hc m hm
    (fallingJetZero_eulerJetZero s c m hj)

noncomputable def laurentEval (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (u z : ℂ) : ℂ :=
  ∑ y ∈ rows s, (∑ x ∈ row s y, c (x, y) * u ^ x) * z ^ y

theorem contDiffAt_zpow_one (q : ℤ) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (fun u : ℂ => u ^ q) 1 :=
  (analyticAt_id.zpow (by norm_num : (1 : ℂ) ≠ 0)).contDiffAt

theorem laurentRow_deriv_one (xs : Finset ℤ) (d : ℤ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun u : ℂ => ∑ x ∈ xs, d x * u ^ x) 1 =
      ∑ x ∈ xs, d x * (descPochhammer ℂ n).eval (x : ℂ) := by
  rw [iteratedDeriv_fun_sum (fun x _ =>
    contDiffAt_const.mul (contDiffAt_zpow_one x n))]
  apply Finset.sum_congr rfl
  intro x _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow,
    one_zpow, mul_one, descPochhammer_eval_eq_prod_range]

theorem laurentEval_mixed_deriv_one (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (a b : ℕ) :
    iteratedDeriv b (fun z : ℂ => iteratedDeriv a (fun u : ℂ => laurentEval s c u z) 1) 1 =
      ∑ y ∈ rows s, (∑ x ∈ row s y,
        c (x, y) * (descPochhammer ℂ a).eval (x : ℂ)) *
          (descPochhammer ℂ b).eval (y : ℂ) := by
  have hrow (y : ℤ) :
      ContDiffAt ℂ (a : WithTop ℕ∞) (fun u : ℂ =>
        ∑ x ∈ row s y, c (x, y) * u ^ x) 1 :=
    ContDiffAt.sum (fun x _ => contDiffAt_const.mul (contDiffAt_zpow_one x a))
  have hi (z : ℂ) :
      iteratedDeriv a (fun u : ℂ => laurentEval s c u z) 1 =
        ∑ y ∈ rows s, (∑ x ∈ row s y,
          c (x, y) * (descPochhammer ℂ a).eval (x : ℂ)) * z ^ y := by
    unfold laurentEval
    rw [iteratedDeriv_fun_sum (fun y _ => (hrow y).mul contDiffAt_const)]
    apply Finset.sum_congr rfl
    intro y _
    rw [iteratedDeriv_mul_const_field, laurentRow_deriv_one]
  simp_rw [hi]
  exact laurentRow_deriv_one _ _ b

def MixedJetZero (f : ℂ → ℂ → ℂ) (u z : ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    iteratedDeriv b (fun v : ℂ => iteratedDeriv a (fun w : ℂ => f w v) u) z = 0

theorem mixedJetZero_iff_fallingJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) :
    MixedJetZero (laurentEval s c) 1 1 m ↔ FallingJetZero s c m := by
  simp only [MixedJetZero, FallingJetZero, laurentEval_mixed_deriv_one]

theorem triangle_mixed_jet_test (p₀ p₁ p₂ : ℝ × ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (h01 : p₀.2 ≤ p₁.2) (h12 : p₁.2 ≤ p₂.2)
    (hrange : p₂.2 - p₀.2 = ρ)
    (harea : triangleDoubleArea p₀ p₁ p₂ = ρ ^ 2)
    (s : Finset (ℤ × ℤ)) (hs : s.Nonempty)
    (hsupp : ∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ convexHull ℝ {p₀, p₁, p₂})
    (c : ℤ × ℤ → ℂ) (hc : ∀ p ∈ s, c p ≠ 0)
    (m : ℕ) (hm : ρ < (m : ℝ)) : ¬ MixedJetZero (laurentEval s c) 1 1 m := by
  rw [mixedJetZero_iff_fallingJetZero]
  exact triangle_falling_test p₀ p₁ p₂ ρ hρ h01 h12 hrange harea s hs hsupp c hc m hm


end MaximalSeshadri.Interpolation
end

end OAI
