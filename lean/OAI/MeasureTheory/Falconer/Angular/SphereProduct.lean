import OAI.MeasureTheory.Falconer.Angular.SphereStationary

namespace OAI

/-! # Actual products of two spherical oscillations

The leading expression keeps both signs at each stationary pole. Its
product therefore contains the four radial phases used in the comparable
far reduction. The error uses only norm bounds, never derivatives of a
stationary remainder.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationarySphereApprox (m J : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) : ℂ :=
  ((Λ^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
    (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e+
      star (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ (antipodalConjugate B) e))

theorem sphere_stationary_expansion_unscaled
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖sphereOscillation Λ e (fun w => B w)-stationarySphereApprox m J Λ B e‖ ≤
        A*Λ^(-(J : ℝ)-((m+2 : ℕ) : ℝ)/2)*C*D^(2*J+(m+2)+1) := by
  obtain ⟨A,hA,hAb⟩ := sphere_stationary_expansion hgnomonic hquadratic m J hJ
  refine ⟨A,hA,?_⟩
  intro e B hB C D hC hD hb Λ hΛ
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  let p : ℂ := ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)
  let q : ℂ := ((Λ^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)
  let S := Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e+
    star (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ (antipodalConjugate B) e)
  have hqp : q*p = 1 := by
    dsimp only [p,q]
    rw [← Complex.ofReal_mul,← Real.rpow_add hΛp,neg_add_cancel,Real.rpow_zero,Complex.ofReal_one]
  have he : sphereOscillation Λ e (fun w => B w)-stationarySphereApprox m J Λ B e =
      q*(p*sphereOscillation Λ e (fun w => B w)-S) := by
    rw [mul_sub,← mul_assoc,hqp,one_mul]
    rfl
  rw [he,norm_mul]
  have hq : ‖q‖ = Λ^(-(((m+2 : ℕ) : ℝ)/2)) := by
    dsimp only [q]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛp _)]
  rw [hq]
  apply (mul_le_mul_of_nonneg_left (hAb e B hB C D hC hD hb Λ hΛ)
    (Real.rpow_pos_of_pos hΛp _).le).trans_eq
  calc
    _ = A*(Λ^(-(((m+2 : ℕ) : ℝ)/2))*Λ^(-(J : ℝ)))*C*D^(2*J+(m+2)+1) := by ring
    _ = _ := by
      rw [← Real.rpow_add hΛp,
        show -(((m+2 : ℕ) : ℝ)/2) + -(J : ℝ) = -(J : ℝ)-((m+2 : ℕ) : ℝ)/2 by ring]

theorem sphereOscillation_norm_le_of_bound {d : ℕ} (Λ : ℝ) (e : Sphere d)
    (B : Sphere d → ℂ) {C : ℝ} (hB : ∀ w, ‖B w‖ ≤ C) :
    ‖sphereOscillation Λ e B‖ ≤ C*(sphereMeasure d).real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  simpa only [norm_mul,sphere_phase_norm,one_mul] using hB w

theorem norm_complex_pair_approx (X Y P Q : ℂ) {Cx Cy εx εy : ℝ}
    (hCx : 0 ≤ Cx) (_hCy : 0 ≤ Cy) (hεx : 0 ≤ εx) (_hεy : 0 ≤ εy)
    (hX : ‖X‖ ≤ Cx) (hY : ‖Y‖ ≤ Cy) (heX : ‖X-P‖ ≤ εx) (heY : ‖Y-Q‖ ≤ εy) :
    ‖X*star Y-P*star Q‖ ≤ εx*Cy+Cx*εy+εx*εy := by
  have hP : ‖P‖ ≤ Cx+εx := by
    calc
      _ = ‖X-(X-P)‖ := by congr 1; ring
      _ ≤ ‖X‖+‖X-P‖ := norm_sub_le _ _
      _ ≤ Cx+εx := add_le_add hX heX
  have he : X*star Y-P*star Q = (X-P)*star Y+P*star (Y-Q) := by
    rw [star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖(X-P)*star Y‖+‖P*star (Y-Q)‖ := norm_add_le _ _
    _ = ‖X-P‖*‖Y‖+‖P‖*‖Y-Q‖ := by simp only [norm_mul,norm_star]
    _ ≤ εx*Cy+(Cx+εx)*εy := add_le_add
      (mul_le_mul heX hY (norm_nonneg _) hεx)
      (mul_le_mul hP heY (norm_nonneg _) (add_nonneg hCx hεx))
    _ = _ := by ring

theorem sphere_product_stationary_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Fin 2 → Sphere (m+3)) (B : Fin 2 → Space (m+3) → ℂ),
      (∀ i, ContDiff ℝ ∞ (B i)) → ∀ C D Λ : Fin 2 → ℝ,
      (∀ i, 0 ≤ C i) → (∀ i, 1 ≤ D i) → (∀ i, 1 ≤ Λ i) →
      (∀ i j, j ≤ 2*J+(m+2)+1 → ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j (B i) w‖ ≤ C i*D i^j) →
      let ε := fun i => A*Λ i^(-(J : ℝ)-((m+2 : ℕ) : ℝ)/2)*C i*D i^(2*J+(m+2)+1)
      let M := (sphereMeasure (m+3)).real univ
      ‖sphereOscillation (Λ 0) (e 0) (fun w => B 0 w)*
          star (sphereOscillation (Λ 1) (e 1) (fun w => B 1 w))-
        stationarySphereApprox m J (Λ 0) (B 0) (e 0)*
          star (stationarySphereApprox m J (Λ 1) (B 1) (e 1))‖ ≤
        ε 0*(C 1*M)+(C 0*M)*ε 1+ε 0*ε 1 := by
  obtain ⟨A,hA,hAb⟩ := sphere_stationary_expansion_unscaled hgnomonic hquadratic m J hJ
  refine ⟨A,hA,?_⟩
  intro e B hB C D Λ hC hD hΛ hb
  dsimp only
  apply norm_complex_pair_approx
  · exact mul_nonneg (hC 0) ENNReal.toReal_nonneg
  · exact mul_nonneg (hC 1) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos
      (zero_lt_one.trans_le (hΛ 0)) _).le) (hC 0)) (pow_nonneg (zero_le_one.trans (hD 0)) _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos
      (zero_lt_one.trans_le (hΛ 1)) _).le) (hC 1)) (pow_nonneg (zero_le_one.trans (hD 1)) _)
  · exact sphereOscillation_norm_le_of_bound _ _ _ (fun w => by
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb 0 0 (by omega) w)
  · exact sphereOscillation_norm_le_of_bound _ _ _ (fun w => by
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb 1 0 (by omega) w)
  · exact hAb (e 0) (B 0) (hB 0) (C 0) (D 0) (hC 0) (hD 0) (hb 0) (Λ 0) (hΛ 0)
  · exact hAb (e 1) (B 1) (hB 1) (C 1) (D 1) (hC 1) (hD 1) (hb 1) (Λ 1) (hΛ 1)

end Falconer

end OAI
