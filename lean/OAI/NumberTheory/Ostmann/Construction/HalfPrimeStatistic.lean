import OAI.NumberTheory.Ostmann.Construction.RegularInitialAmplitude
import OAI.NumberTheory.Ostmann.Construction.BoundedWordStatistic
import OAI.NumberTheory.Ostmann.Construction.WordCopyCoordinates

namespace OAI

/-! # The two independent half-lists in the positive physical statistic -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem physicalTupleTerm_summable {I : Type*} [Fintype I]
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (p : I → P)
    (F : I → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun a : ℤ => (∏ i, F i (p i) (a : ZMod (p i : ℕ))) * ψ ((a : ℝ) / X)) := by
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hs.mul_left (∏ i, ∑ b, ‖F i (p i) b‖))
  intro a
  rw [norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
    Finset.single_le_sum (fun b _ => norm_nonneg (F i (p i) b)) (Finset.mem_univ _))

noncomputable def halfPrimeMean {n : ℕ}
    (P : Finset ℕ) (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (a : ℤ) : ℂ :=
  ∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * ∏ i, F i (x i) (a : ZMod (x i : ℕ))

noncomputable def doubledHalfWeight {n : ℕ} {A : Type*}
    (w : (Fin n → A) → ℂ) (x : Fin (n + n) → A) : ℂ :=
  w (fun i => x (i.castAdd n)) * w (fun i => x (i.natAdd n))

/-- All positions, including the two giants and the outside spectators,
are sampled twice independently in the initial square. -/
theorem halfPrimeMean_square {n : ℕ} (P : Finset ℕ) (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (a : ℤ) :
    halfPrimeMean P μ F w a ^ 2 =
      ∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        ∏ i, Fin.append F F i (x i) (a : ZMod (x i : ℕ)) := by
  let e : ((Fin n → P) × (Fin n → P)) ≃ (Fin (n + n) → P) := Fin.appendEquiv n n
  rw [← e.sum_comp, Fintype.sum_prod_type]
  unfold halfPrimeMean
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change _ = (productPrior (Fin.append μ μ) (Fin.append x y) : ℂ) *
    doubledHalfWeight w (Fin.append x y) *
      ∏ i, Fin.append F F i (Fin.append x y i)
        (a : ZMod ((Fin.append x y : Fin (n + n) → P) i : ℕ))
  simp only [productPrior_append, doubledHalfWeight, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Complex.ofReal_mul]
  have hxF : (∏ i : Fin n, F i (Fin.append x y (i.castAdd n))
      (a : ZMod ((Fin.append x y : Fin (n + n) → P) (i.castAdd n) : ℕ))) =
      ∏ i, F i (x i) (a : ZMod (x i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun q : P => F i q (a : ZMod (q : ℕ))) (Fin.append_left x y i)
  have hyF : (∏ i : Fin n, F i (Fin.append x y (i.natAdd n))
      (a : ZMod ((Fin.append x y : Fin (n + n) → P) (i.natAdd n) : ℕ))) =
      ∏ i, F i (y i) (a : ZMod (y i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun q : P => F i q (a : ZMod (q : ℕ))) (Fin.append_right x y i)
  rw [hxF, hyF]
  ring

/-- Exchanging only finite original sample sums with the Schwartz sum gives
the exact physical statistic used by the initial Fourier lower bound. -/
theorem halfPrimeMean_statistic {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' a : ℤ, halfPrimeMean P μ F w a ^ 2 * ψ ((a : ℝ) / X)) =
      ∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        physicalTupleSum P x (Fin.append F F) ψ X := by
  simp_rw [halfPrimeMean_square, Finset.sum_mul]
  have hs (x : Fin (n + n) → P) : Summable (fun a : ℤ =>
      ((productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        ∏ i, Fin.append F F i (x i) (a : ZMod (x i : ℕ))) * ψ ((a : ℝ) / X)) := by
    simpa only [mul_assoc] using
      (physicalTupleTerm_summable P x (Fin.append F F) ψ X hX).mul_left
        ((productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x)
  rw [Summable.tsum_finsetSum (fun x _ => hs x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [physicalTupleSum, ← tsum_mul_left]
  apply tsum_congr
  intro a
  ring

noncomputable def halfPrimeBound {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ) (w : (Fin n → P) → ℂ) : ℝ :=
  ∑ x : Fin n → P, |productPrior μ x| * ‖w x‖ * ∏ i, ∑ b, ‖F i (x i) b‖

theorem halfPrimeMean_bound {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (a : ℤ) :
    ‖halfPrimeMean P μ F w a‖ ≤ halfPrimeBound P μ F w := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
    Finset.single_le_sum (fun b _ => norm_nonneg (F i (x i) b)) (Finset.mem_univ _))

theorem halfPrimeMean_real {n : ℕ} (P : Finset ℕ) (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ) (w : (Fin n → P) → ℂ)
    (hF : ∀ i q x, (F i q x).im = 0) (hw : ∀ x, (w x).im = 0) (a : ℤ) :
    (halfPrimeMean P μ F w a).im = 0 := by
  have hFc : ∀ i q x, conj (F i q x) = F i q x := by
    intro i q x
    apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, hF, neg_zero]
  have hwc : ∀ x, conj (w x) = w x := by
    intro x
    apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, hw, neg_zero]
  have h : conj (halfPrimeMean P μ F w a) = halfPrimeMean P μ F w a := by
    simp only [halfPrimeMean, map_sum, map_mul, map_prod, Complex.conj_ofReal, hFc, hwc]
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem halfPrimeMean_statistic_re {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hreal : ∀ a, (halfPrimeMean P μ F w a).im = 0) :
    (∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
      physicalTupleSum P x (Fin.append F F) ψ X).re =
      ∑' a : ℤ, (ψ ((a : ℝ) / X)).re * ‖halfPrimeMean P μ F w a‖ ^ 2 := by
  let T := halfPrimeMean P μ F w
  have hs : Summable (fun a : ℤ => ‖ψ ((a : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  have hc : Summable (fun a : ℤ => T a ^ 2 * ψ ((a : ℝ) / X)) := by
    apply Summable.of_norm_bounded (hs.mul_left (halfPrimeBound P μ F w ^ 2))
    intro a
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (halfPrimeMean_bound P μ F w a) 2) (norm_nonneg _)
  rw [← halfPrimeMean_statistic P μ F w ψ X hX]
  change (∑' a : ℤ, T a ^ 2 * ψ ((a : ℝ) / X)).re = _
  rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hc]
  apply tsum_congr
  intro a
  have hi : (T a).im = 0 := hreal a
  have hn : ‖T a‖ ^ 2 = (T a).re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hi]
    ring
  change (T a ^ 2 * ψ ((a : ℝ) / X)).re = (ψ ((a : ℝ) / X)).re * ‖T a‖ ^ 2
  rw [hn]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, hi,
    mul_zero, zero_mul, add_zero, sub_zero]
  ring

/-- The selected mean over endpoints gives a lower bound for the full
original doubled-list physical statistic. -/
theorem halfPrimeMean_endpoint_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hreal : ∀ a, (halfPrimeMean P μ F w a).im = 0)
    (E : Finset ℤ) (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E, (halfPrimeMean P μ F w a).re) :
    (E.card : ℝ) * (c * δ ^ 2) ≤
      ‖∑ x : Fin (n + n) → P, (productPrior (Fin.append μ μ) x : ℂ) * doubledHalfWeight w x *
        physicalTupleSum P x (Fin.append F F) ψ X‖ := by
  have hb := wordStatistic_lower_of_endpoint_mean (m := 0) ψ X hX (halfPrimeMean P μ F w)
    (fun i => Fin.elim0 i) E (halfPrimeBound P μ F w) (fun i => Fin.elim0 i)
    hψ (halfPrimeMean_bound P μ F w) (fun i => Fin.elim0 i)
    c δ 1 hc hδ zero_le_one hcE hmean (fun _ _ i => Fin.elim0 i)
  have hb' : (E.card : ℝ) * (c * δ ^ 2) ≤
      ∑' a : ℤ, (ψ ((a : ℝ) / X)).re * ‖halfPrimeMean P μ F w a‖ ^ 2 := by
    simpa only [wordStatisticTerm, Nat.mul_zero, pow_zero, mul_one, Finset.univ_eq_empty,
      Finset.prod_empty] using hb
  rw [← halfPrimeMean_statistic_re P μ F w ψ X hX hreal] at hb'
  exact hb'.trans (Complex.re_le_norm _)

end Ostmann

end OAI
