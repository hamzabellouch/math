import OAI.Algebra.Determinantal.BorderClosure
import OAI.Algebra.Determinantal.BorderPolars

namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

namespace InitialHomogeneous
variable {σ : Type*} [Fintype σ]

noncomputable def dilation (t : ℂ) : Poly σ →ₐ[ℂ] Poly σ := by
  classical
  exact affineSubstitution (fun _ => 0) (fun i j => if i = j then t else 0)

lemma dilation_eq_aeval (t : ℂ) :
    dilation (σ := σ) t = aeval (fun i => C t * X i) := by
  classical
  unfold dilation affineSubstitution
  congr 1
  funext i
  simp [apply_ite]

lemma dilation_monomial (t : ℂ) (e : σ →₀ ℕ) (c : ℂ) :
    dilation t (monomial e c) = t ^ e.degree • monomial e c := by
  rw [dilation_eq_aeval]
  have h := SliceParameters.homogeneous_aeval_scale
    (isHomogeneous_monomial c (n := e.degree) rfl) (C t) (fun i : σ => X i)
  simpa only [aeval_X_left_apply, ← map_pow, smul_eq_C_mul] using h

lemma coeff_dilation (t : ℂ) (q : Poly σ) (e : σ →₀ ℕ) :
    (dilation t q).coeff e = t ^ e.degree * q.coeff e := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [dilation_monomial, coeff_smul]
      by_cases h : s = e
      · subst s; rfl
      · simp [coeff_monomial, h]
  | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

noncomputable def normalizedDilation (r : ℕ) (q : Poly σ) (t : ℂ) : Poly σ :=
  (t ^ r)⁻¹ • dilation t q

omit [Fintype σ] in
lemma coeff_eq_zero_of_lower_components {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    (e : σ →₀ ℕ) (he : e.degree < r) : q.coeff e = 0 := by
  have h := congrArg (fun p : Poly σ => p.coeff e) (hlow e.degree he)
  simpa [coeff_homogeneousComponent] using h

lemma coeff_normalizedDilation {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    {t : ℂ} (ht : t ≠ 0) (e : σ →₀ ℕ) :
    (normalizedDilation r q t).coeff e =
      if e.degree < r then 0 else t ^ (e.degree - r) * q.coeff e := by
  simp only [normalizedDilation, coeff_smul, smul_eq_mul, coeff_dilation]
  by_cases he : e.degree < r
  · simp [he, coeff_eq_zero_of_lower_components hlow e he]
  · rw [ite_eq_right he]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt he)
    rw [hk, Nat.add_sub_cancel_left, pow_add]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero r ht), one_mul]

/-- Cancellation of the pole gives coefficientwise convergence along any filter
approaching zero through nonzero complex values. -/
theorem normalizedDilation_tendsto {α : Type*} {l : Filter α}
    {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0)
    {t : α → ℂ} (ht : Tendsto t l (𝓝 0))
    (hne : ∀ᶠ j in l, t j ≠ 0) (e : σ →₀ ℕ) :
    Tendsto (fun j => (normalizedDilation r q (t j)).coeff e)
      l (𝓝 ((homogeneousComponent r q).coeff e)) := by
  have heq : (fun j => (normalizedDilation r q (t j)).coeff e) =ᶠ[l]
      (fun j => if e.degree < r then 0 else t j ^ (e.degree-r) * q.coeff e) :=
    hne.mono fun j hj => coeff_normalizedDilation hlow hj e
  apply Tendsto.congr' heq.symm
  rw [coeff_homogeneousComponent]
  by_cases hlo : e.degree < r
  · simp only [hlo, ite_true, ite_eq_right (Nat.ne_of_lt hlo)]
    exact tendsto_const_nhds
  · simp only [hlo, ite_false]
    by_cases he : e.degree = r
    · simp only [he, Nat.sub_self, pow_zero, one_mul, ite_true]
      exact tendsto_const_nhds
    · have hk : e.degree-r ≠ 0 := by omega
      simpa only [ite_eq_right he, zero_pow hk, zero_mul] using
        (ht.pow (e.degree-r)).mul_const (q.coeff e)

/-- Normalized dilation converges coefficientwise as the positive real scale tends to zero. -/
theorem normalizedDilation_tendsto_positive {q : Poly σ} {r : ℕ}
    (hlow : ∀ j < r, homogeneousComponent j q = 0) (e : σ →₀ ℕ) :
    Tendsto (fun t : ℝ => (normalizedDilation r q (t : ℂ)).coeff e)
      (𝓝[Set.Ioi 0] 0) (𝓝 ((homogeneousComponent r q).coeff e)) := by
  apply normalizedDilation_tendsto hlow
  · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact_mod_cast (ne_of_gt ht : t ≠ (0 : ℝ))

end InitialHomogeneous

/-- The lowest homogeneous component inherits the fixed border determinant size
by degeneration along a geometric sequence of nonzero scales. -/
theorem HasBorderDeterminant.lowest_homogeneousComponent
    {σ : Type*} [Fintype σ] {n r : ℕ} {q : Poly σ}
    (hb : HasBorderDeterminant n q)
    (hlow : ∀ j < r, homogeneousComponent j q = 0) :
    HasBorderDeterminant n (homogeneousComponent r q) := by
  classical
  let t : ℕ → ℂ := fun j => (1 / 2 : ℂ) ^ j
  have ht : Tendsto t atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    norm_num
  have hne : ∀ j, t j ≠ 0 := fun j => pow_ne_zero j (by norm_num)
  apply HasBorderDeterminant.coefficientwise_limit
    (P := fun j => InitialHomogeneous.normalizedDilation r q (t j))
  · intro j
    exact hb.affineSubstitution_smul (fun _ => 0)
      (fun i k => if i = k then t j else 0) ((t j ^ r)⁻¹)
  · exact InitialHomogeneous.normalizedDilation_tendsto hlow ht
      (Filter.Eventually.of_forall hne)

/-- A smooth lowest homogeneous term after translation bounds both border and exact
determinant sizes by the product of its degree minus one and dimension minus one,
divided by `4 * Real.exp 1`. -/
theorem smooth_initial_form_lower_bound (d r : ℕ) (g : Poly (Fin d))
    (a : Fin d → ℂ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (_hG : homogeneousComponent r
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) ≠ 0)
    (hlow : ∀ j < r, homogeneousComponent j
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) = 0)
    (hs : ∀ y : Fin d → ℂ,
      eval y (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g)) = 0 →
      (∀ i, eval y (pderiv i (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g))) = 0) →
      y = 0) :
    ∀ n : ℕ,
      (HasBorderDeterminant n g →
        ((r-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ (n : ℝ)) ∧
      (HasExactDeterminant n g →
        ((r-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ (n : ℝ)) := by
  intro n
  have hb : HasBorderDeterminant n g →
      ((r-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ (n : ℝ) := by
    intro h
    have hq := h.affineSubstitution a
      (fun i j : Fin d => if i = j then (1 : ℂ) else 0)
    have hinit := hq.lowest_homogeneousComponent hlow
    simpa only [Fintype.card_fin] using Polar.HasBorderDeterminant.smooth_lower_bound hinit
      (by simpa only [Fintype.card_fin] using hd) hr
      (homogeneousComponent_isHomogeneous r _) hs
  exact ⟨hb, fun h => hb h.hasBorderDeterminant⟩

end PermanentBorder

end OAI
