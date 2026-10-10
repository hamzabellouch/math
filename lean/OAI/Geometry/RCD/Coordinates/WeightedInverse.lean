import OAI.Geometry.RCD.Coordinates.FrozenNorms

namespace OAI

/-!
# Inverse increments without commutation assumptions

The arguments use positive quadratic forms and exact inverse identities.
Operators from different scales are never assumed to commute.
-/

open scoped InnerProductSpace BigOperators

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positivity is preserved by the inverse of a linear equivalence. -/
theorem positive_equiv_symm (Q : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) : (Q.symm : E →L[ℝ] E).IsPositive :=
  LinearMap.IsPositive.toLinearMap_symm (T := Q.toLinearEquiv) hQ

/-- Exact resolvent identity evaluated on a vector. -/
theorem inverse_increment_apply (P Q : E ≃L[ℝ] E) (xi : E) :
    ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)) xi =
      Q.symm (((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)) (P.symm xi)) := by
  simp only [sub_apply, ContinuousLinearEquiv.coe_coe, map_sub,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The inverse increment equals the leading conjugated decrement plus a
nonnegative remainder. -/
theorem inverse_increment_quadratic_identity (P Q : E ≃L[ℝ] E)
    (hP : (P : E →L[ℝ] E).IsPositive)
    (hD : ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)).IsPositive) (xi : E) :
    let D := (P : E →L[ℝ] E) - (Q : E →L[ℝ] E)
    let a := P.symm xi
    let e := Q.symm (D a)
    ⟪xi, ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)) xi⟫_ℝ =
      ⟪a, D a⟫_ℝ + ⟪e, Q e⟫_ℝ := by
  dsimp only
  let D := (P : E →L[ℝ] E) - (Q : E →L[ℝ] E)
  let a := P.symm xi
  let e := Q.symm (D a)
  have he : Q e = D a := Q.apply_symm_apply (D a)
  have hcross : ⟪a, D e⟫_ℝ = ⟪e, Q e⟫_ℝ := by
    calc
      _ = ⟪D a, e⟫_ℝ := (hD.inner_left_eq_inner_right a e).symm
      _ = ⟪Q e, e⟫_ℝ := by rw [he]
      _ = _ := real_inner_comm _ _
  change ⟪xi, ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)) xi⟫_ℝ =
    ⟪a, D a⟫_ℝ + ⟪e, Q e⟫_ℝ
  rw [inverse_increment_apply]
  change ⟪xi, e⟫_ℝ = _
  calc
    _ = ⟪P a, e⟫_ℝ := by simp [a]
    _ = ⟪a, P e⟫_ℝ := hP.inner_left_eq_inner_right a e
    _ = ⟪a, Q e + D e⟫_ℝ := by congr 1; simp [D]
    _ = _ := by simp only [inner_add_right, he, hcross]

/-- The sharp two-sided inverse-increment order for a relatively small
positive decrement.  This replaces the one-matrix spectral calculation. -/
theorem inverse_increment_order (P Q : E ≃L[ℝ] E)
    (hP : (P : E →L[ℝ] E).IsPositive) (hQ : (Q : E →L[ℝ] E).IsPositive)
    (hD : ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)).IsPositive)
    {eta : ℝ} (heta : 0 ≤ eta) (heta1 : eta < 1)
    (hsmall : ∀ v, ⟪v, ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)) v⟫_ℝ ≤
      eta * ⟪v, P v⟫_ℝ) (xi : E) :
    let D := (P : E →L[ℝ] E) - (Q : E →L[ℝ] E)
    ⟪P.symm xi, D (P.symm xi)⟫_ℝ ≤
      ⟪xi, ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)) xi⟫_ℝ ∧
    ⟪xi, ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)) xi⟫_ℝ ≤
      ⟪P.symm xi, D (P.symm xi)⟫_ℝ / (1 - eta) := by
  dsimp only
  let D := (P : E →L[ℝ] E) - (Q : E →L[ℝ] E)
  let a := P.symm xi
  let e := Q.symm (D a)
  have he : Q e = D a := Q.apply_symm_apply (D a)
  have hc : 0 ≤ ⟪e, Q e⟫_ℝ := hQ.inner_nonneg_right e
  have hb : 0 ≤ ⟪a, D a⟫_ℝ := hD.inner_nonneg_right a
  have hcross : ⟪a, D e⟫_ℝ = ⟪e, Q e⟫_ℝ := by
    rw [← hD.inner_left_eq_inner_right, ← he, real_inner_comm]
  have hcs := positive_form_cauchy_schwarz hD a e
  change ⟪a, D e⟫_ℝ ^ 2 ≤ ⟪a, D a⟫_ℝ * ⟪e, D e⟫_ℝ at hcs
  rw [hcross] at hcs
  have hde : (1 - eta) * ⟪e, D e⟫_ℝ ≤ eta * ⟪e, Q e⟫_ℝ := by
    have hs := hsmall e
    change ⟪e, D e⟫_ℝ ≤ eta * ⟪e, P e⟫_ℝ at hs
    have hid : ⟪e, P e⟫_ℝ = ⟪e, Q e⟫_ℝ + ⟪e, D e⟫_ℝ := by
      simp [D, inner_sub_right]
    rw [hid] at hs
    nlinarith
  have hrem : (1 - eta) * ⟪e, Q e⟫_ℝ ≤ eta * ⟪a, D a⟫_ℝ := by
    by_cases hz : ⟪e, Q e⟫_ℝ = 0
    · rw [hz, mul_zero]
      exact mul_nonneg heta hb
    have hcpos : 0 < ⟪e, Q e⟫_ℝ := lt_of_le_of_ne hc (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hcpos).mp
    have h₁ := mul_le_mul_of_nonneg_left hcs (by linarith : 0 ≤ 1 - eta)
    have h₂ := mul_le_mul_of_nonneg_left hde hb
    nlinarith only [h₁, h₂]
  have hid := inverse_increment_quadratic_identity P Q hP hD xi
  change ⟪xi, ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)) xi⟫_ℝ =
    ⟪a, D a⟫_ℝ + ⟪e, Q e⟫_ℝ at hid
  change ⟪a, D a⟫_ℝ ≤ _ ∧ _ ≤ ⟪a, D a⟫_ℝ / (1 - eta)
  rw [hid]
  constructor
  · linarith
  · apply (le_div_iff₀ (by linarith : 0 < 1 - eta)).mpr
    nlinarith only [hrem]

/-- A positive form bounded by `eta Q` satisfies the weighted square bound
`D Q⁻¹ D ≤ eta D`. -/
theorem positive_inverse_sandwich_bound (Q : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) {D : E →L[ℝ] E} (hD : D.IsPositive)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hsmall : ∀ v, ⟪v, D v⟫_ℝ ≤ eta * ⟪v, Q v⟫_ℝ) (w : E) :
    ⟪D w, Q.symm (D w)⟫_ℝ ≤ eta * ⟪w, D w⟫_ℝ := by
  let v := Q.symm (D w)
  have hQv : Q v = D w := Q.apply_symm_apply (D w)
  have heq : ⟪w, D v⟫_ℝ = ⟪v, Q v⟫_ℝ := by
    rw [← hD.inner_left_eq_inner_right, ← hQv, real_inner_comm]
  have hc : 0 ≤ ⟪v, Q v⟫_ℝ := hQ.inner_nonneg_right v
  have hb := hD.inner_nonneg_right w
  have hcs := positive_form_cauchy_schwarz hD w v
  rw [heq] at hcs
  have hm := mul_le_mul_of_nonneg_left (hsmall v) hb
  have htarget : ⟪v, Q v⟫_ℝ ≤ eta * ⟪w, D w⟫_ℝ := by
    by_cases hz : ⟪v, Q v⟫_ℝ = 0
    · rw [hz]; exact mul_nonneg heta hb
    have hp : 0 < ⟪v, Q v⟫_ℝ := lt_of_le_of_ne hc (Ne.symm hz)
    nlinarith
  change ⟪D w, v⟫_ℝ ≤ _
  calc
    _ = ⟪v, D w⟫_ℝ := real_inner_comm _ _
    _ = ⟪v, Q v⟫_ℝ := by rw [hQv]
    _ ≤ _ := htarget

/-- A monotone positive metric sequence has positive inverse increments. -/
theorem inverse_increment_isPositive (P Q : E ≃L[ℝ] E)
    (hP : (P : E →L[ℝ] E).IsPositive) (hQ : (Q : E →L[ℝ] E).IsPositive)
    (hD : ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)).IsPositive) :
    ((Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨(positive_equiv_symm Q hQ).isSymmetric.sub
    (positive_equiv_symm P hP).isSymmetric, ?_⟩
  intro xi
  have hid := inverse_increment_quadratic_identity P Q hP hD xi
  have h₁ := hD.inner_nonneg_right (P.symm xi)
  have h₂ := hQ.inner_nonneg_right
    (Q.symm (((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)) (P.symm xi)))
  rw [real_inner_comm]
  exact hid.symm ▸ add_nonneg h₁ h₂

/-- For a half-small decrement the inverse increment satisfies the weighted
square bound used in the convolution argument. -/
theorem inverse_increment_weighted_square_le (P Q : E ≃L[ℝ] E)
    (hP : (P : E →L[ℝ] E).IsPositive) (hQ : (Q : E →L[ℝ] E).IsPositive)
    (hD : ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)).IsPositive)
    (hsmall : ∀ v, ⟪v, ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)) v⟫_ℝ ≤
      (1 / 2 : ℝ) * ⟪v, P v⟫_ℝ) (xi : E) :
    let B := (Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)
    ⟪B xi, P (B xi)⟫_ℝ ≤ ⟪xi, B xi⟫_ℝ := by
  let B := (Q.symm : E →L[ℝ] E) - (P.symm : E →L[ℝ] E)
  have hB := inverse_increment_isPositive P Q hP hQ hD
  have hb : ∀ v, ⟪v, B v⟫_ℝ ≤ ⟪v, P.symm v⟫_ℝ := by
    intro v
    have ho := (inverse_increment_order P Q hP hQ hD (by norm_num) (by norm_num) hsmall v).2
    have ho' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 2)).mp ho
    have hs := hsmall (P.symm v)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hs
    have hi : ⟪P.symm v, v⟫_ℝ = ⟪v, P.symm v⟫_ℝ := real_inner_comm _ _
    rw [hi] at hs
    change ⟪v, B v⟫_ℝ * (1 - 1 / 2) ≤
      ⟪P.symm v, ((P : E →L[ℝ] E) - (Q : E →L[ℝ] E)) (P.symm v)⟫_ℝ at ho'
    linarith
  have h := positive_inverse_sandwich_bound P.symm (positive_equiv_symm P hP) hB
    (by norm_num : (0 : ℝ) ≤ 1) (fun v => by simpa only [B, sub_apply, one_mul] using hb v) xi
  simpa only [ContinuousLinearEquiv.symm_symm, one_mul] using h

/-- The inverse-energy form of a bilinear comparison, obtained by testing
at the actual inverse image rather than assuming a duality formula. -/
theorem inverse_energy_of_bilinear_bound (Q : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) (z : E) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ v, ⟪v, z⟫_ℝ ^ 2 ≤ K * ⟪v, Q v⟫_ℝ) :
    ⟪z, Q.symm z⟫_ℝ ≤ K := by
  let v := Q.symm z
  have hv : Q v = z := Q.apply_symm_apply z
  have hc : 0 ≤ ⟪v, z⟫_ℝ := by
    simpa only [ContinuousLinearEquiv.coe_coe, hv] using hQ.inner_nonneg_right v
  have hb := hbound v
  rw [hv] at hb
  have ht : ⟪v, z⟫_ℝ ≤ K := by
    by_cases hz : ⟪v, z⟫_ℝ = 0
    · simpa only [hz] using hK
    · have hp : 0 < ⟪v, z⟫_ℝ := lt_of_le_of_ne hc (Ne.symm hz)
      nlinarith
  simpa only [real_inner_comm] using ht

/-- Relative comparison of positive metrics gives both inverse order and
the weighted inverse-square estimate needed for normalization errors. -/
theorem relative_inverse_bounds (Q R : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) (hR : (R : E →L[ℝ] E).IsPositive)
    {c : ℝ} (hc : 0 < c)
    (hcompare : ∀ v, c * ⟪v, Q v⟫_ℝ ≤ ⟪v, R v⟫_ℝ) (z : E) :
    ⟪z, R.symm z⟫_ℝ ≤ ⟪z, Q.symm z⟫_ℝ / c ∧
      ⟪R.symm z, Q (R.symm z)⟫_ℝ ≤ ⟪z, Q.symm z⟫_ℝ / c ^ 2 := by
  let u := Q.symm z
  let v := R.symm z
  have hu : Q u = z := Q.apply_symm_apply z
  have hv : R v = z := R.apply_symm_apply z
  have ha : 0 ≤ ⟪z, u⟫_ℝ := by
    simpa only [ContinuousLinearEquiv.coe_coe, hu, real_inner_comm] using hQ.inner_nonneg_right u
  have hb : 0 ≤ ⟪z, v⟫_ℝ := by
    simpa only [ContinuousLinearEquiv.coe_coe, hv, real_inner_comm] using hR.inner_nonneg_right v
  have hq : 0 ≤ ⟪v, Q v⟫_ℝ := hQ.inner_nonneg_right v
  have hcs := positive_form_cauchy_schwarz hQ u v
  change ⟪u, Q v⟫_ℝ ^ 2 ≤ ⟪u, Q u⟫_ℝ * ⟪v, Q v⟫_ℝ at hcs
  have hid : ⟪u, Q v⟫_ℝ = ⟪z, v⟫_ℝ := by
    have hh := hQ.inner_left_eq_inner_right u v
    change ⟪Q u, v⟫_ℝ = ⟪u, Q v⟫_ℝ at hh
    rw [hu] at hh
    exact hh.symm
  rw [hid, hu] at hcs
  have hinner : ⟪u, z⟫_ℝ = ⟪z, u⟫_ℝ := real_inner_comm _ _
  rw [hinner] at hcs
  have hcomp : c * ⟪v, Q v⟫_ℝ ≤ ⟪z, v⟫_ℝ := by
    simpa only [hv, real_inner_comm] using hcompare v
  change ⟪z, v⟫_ℝ ≤ ⟪z, u⟫_ℝ / c ∧ ⟪v, Q v⟫_ℝ ≤ ⟪z, u⟫_ℝ / c ^ 2
  constructor
  · apply (le_div_iff₀ hc).mpr
    by_cases hz : ⟪z, v⟫_ℝ = 0
    · rw [hz, zero_mul]; exact ha
    have hp : 0 < ⟪z, v⟫_ℝ := lt_of_le_of_ne hb (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    have h₁ := mul_le_mul_of_nonneg_left hcs hc.le
    have h₂ := mul_le_mul_of_nonneg_left hcomp ha
    nlinarith only [h₁, h₂]
  · apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    by_cases hz : ⟪v, Q v⟫_ℝ = 0
    · rw [hz, zero_mul]; exact ha
    have hp : 0 < ⟪v, Q v⟫_ℝ := lt_of_le_of_ne hq (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    have hsq := (sq_le_sq₀ (mul_nonneg hc.le hq) hb).mpr hcomp
    nlinarith only [hsq, hcs]

/-- Exact change of inverse normalization. -/
theorem inverse_normalization_error_identity (Q R : E ≃L[ℝ] E) (xi : E) :
    R.symm xi - Q.symm xi =
      -(R.symm (((R : E →L[ℝ] E) - (Q : E →L[ℝ] E)) (Q.symm xi))) := by
  simp only [sub_apply, ContinuousLinearEquiv.coe_coe, map_sub,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  abel

/-- Bilinear heat comparison and relative metric comparison imply the
normalization-error bound. Neither inverse order nor the error is assumed. -/
theorem inverse_normalization_error_le (Q R : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) (hR : (R : E →L[ℝ] E).IsPositive)
    (F : E →L[ℝ] E) (hF : F.IsPositive) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hcompare : ∀ v, c * ⟪v, Q v⟫_ℝ ≤ ⟪v, R v⟫_ℝ)
    (hbilinear : ∀ u v,
      ⟪v, ((R : E →L[ℝ] E) - (Q : E →L[ℝ] E)) u⟫_ℝ ^ 2 ≤
        (C * ⟪u, F u⟫_ℝ) * ⟪v, Q v⟫_ℝ) (xi : E) :
    ⟪R.symm xi - Q.symm xi, Q (R.symm xi - Q.symm xi)⟫_ℝ ≤
      C / c ^ 2 * ⟪Q.symm xi, F (Q.symm xi)⟫_ℝ := by
  let z := ((R : E →L[ℝ] E) - (Q : E →L[ℝ] E)) (Q.symm xi)
  have henergy : ⟪z, Q.symm z⟫_ℝ ≤ C * ⟪Q.symm xi, F (Q.symm xi)⟫_ℝ :=
    inverse_energy_of_bilinear_bound Q hQ z
      (mul_nonneg hC (hF.inner_nonneg_right _)) (hbilinear (Q.symm xi))
  rw [inverse_normalization_error_identity]
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg]
  calc
    _ ≤ ⟪z, Q.symm z⟫_ℝ / c ^ 2 := (relative_inverse_bounds Q R hQ hR hc hcompare z).2
    _ ≤ (C * ⟪Q.symm xi, F (Q.symm xi)⟫_ℝ) / c ^ 2 :=
      div_le_div_of_nonneg_right henergy (sq_nonneg c)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
