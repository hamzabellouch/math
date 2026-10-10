import Mathlib

namespace OAI

/-!
Pointwise algebra for spherical starting immersions and positive boundary
crossing invariants, as in Section 8.1, equations `spherical-radial-form` and
`initial-crossing-positivity` of paper 094-01.
-/

noncomputable section

open scoped Matrix

namespace ClosedSurfaceR4.RadialMetricAlgebra

abbrev Vec := Fin 4 → ℝ

/-- Euclidean normalization, expressed using the finite-coordinate dot product. -/
def unitDirection (v : Vec) : Vec := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v

lemma dot_self_pos {v : Vec} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hnonneg : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  exact hnonneg.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hv)

lemma positive_dot_ne_zero {v n : Vec} (hv : 0 < v ⬝ᵥ n) : v ≠ 0 := by
  intro h
  simp [h] at hv

lemma unitDirection_ne_neg_of_dot_pos {v n : Vec}
    (hn : n ⬝ᵥ n = 1) (hv : 0 < v ⬝ᵥ n) : unitDirection v ≠ -n := by
  have hsq : 0 < v ⬝ᵥ v := dot_self_pos (positive_dot_ne_zero hv)
  have hpos : 0 < unitDirection v ⬝ᵥ n := by
    simpa only [unitDirection, smul_dotProduct, smul_eq_mul] using
      mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hsq)) hv
  intro h
  rw [h, neg_dotProduct, hn] at hpos
  norm_num at hpos

lemma unitDirection_pos_smul {n : Vec} (hn : n ⬝ᵥ n = 1)
    {c : ℝ} (hc : 0 < c) : unitDirection (c • n) = n := by
  have hs : (c • n) ⬝ᵥ (c • n) = c ^ 2 := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hn]
    ring
  rw [unitDirection, hs, Real.sqrt_sq hc.le, smul_smul, inv_mul_cancel₀ hc.ne']
  exact one_smul ℝ n

/-- A radial component with positive coefficient prevents the second form
from vanishing, independently of its component tangent to the sphere. -/
theorem spherical_radial_boundary {n b : Vec} {a r : ℝ}
    (hn : n ⬝ᵥ n = 1) (hb : b ⬝ᵥ n = 0) (ha : 0 < a) (hr : 0 < r) :
    let B := r • b + (r⁻¹ * a) • n
    0 < B ⬝ᵥ n ∧ B ≠ 0 ∧ unitDirection B ≠ -n := by
  dsimp only
  have hp : 0 < (r • b + (r⁻¹ * a) • n) ⬝ᵥ n := by
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hb, hn,
      mul_zero, mul_one, zero_add]
    exact mul_pos (inv_pos.mpr hr) ha
  exact ⟨hp, positive_dot_ne_zero hp, unitDirection_ne_neg_of_dot_pos hn hp⟩

/-- At a prepared crossing the spherical component vanishes.  This is the
Gauss expression for the remaining radial second fundamental form. -/
theorem radial_gauss_identity (n : Vec) (hn : n ⬝ᵥ n = 1) (a b c r : ℝ) :
    ((r⁻¹ * a) • n) ⬝ᵥ ((r⁻¹ * b) • n) -
        ((r⁻¹ * c) • n) ⬝ᵥ ((r⁻¹ * c) • n) =
      r⁻¹ ^ 2 * (a * b - c ^ 2) := by
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hn]
  ring

/-- The ordered crossing invariant from equation `crossing-invariant`.
Here `a`, `b`, and `c` are the values of the metric on `(v,v)`, `(w,w)`,
and `(v,w)` respectively, and `K` is the Gauss curvature. -/
def radialCrossing (n : Vec) (a b c r K : ℝ) : ℝ :=
  (((r⁻¹ * c) • n) ⬝ᵥ unitDirection ((r⁻¹ * a) • n)) ^ 2 +
    K * (a * b - c ^ 2)

theorem radial_crossing_eq {n : Vec} (hn : n ⬝ᵥ n = 1)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (b c : ℝ) :
    radialCrossing n a b c r (r⁻¹ ^ 2) = r⁻¹ ^ 2 * a * b := by
  unfold radialCrossing
  rw [unitDirection_pos_smul hn (mul_pos (inv_pos.mpr hr) ha)]
  simp only [smul_dotProduct, smul_eq_mul, hn, mul_one]
  ring

/-- Both ordered inequalities hold even if the two tangent vectors are
proportional; no positive lower bound for their Gram determinant is needed. -/
theorem radial_crossings_pos {n : Vec} (hn : n ⬝ᵥ n = 1)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (c : ℝ) :
    0 < radialCrossing n a b c r (r⁻¹ ^ 2) ∧
    0 < radialCrossing n b a c r (r⁻¹ ^ 2) := by
  rw [radial_crossing_eq hn ha hr, radial_crossing_eq hn hb hr]
  have hsq : 0 < r⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hr)
  exact ⟨mul_pos (mul_pos hsq ha) hb, mul_pos (mul_pos hsq hb) ha⟩

section GeneralCrossing

/-- Coordinates in an orthonormal frame of the two-dimensional normal plane.
The complex plane is used only as a real inner product space. -/
def pureNormal (S D N L k t : ℝ) : ℂ :=
  ⟨(N ^ 2 + k + (D + S * t) ^ 2) / S, L + 2 * N * t⟩

def mixedNormal (S D N L k t u : ℝ) : ℂ :=
  ⟨(N ^ 2 + k + (D + S * t) * (D + S * u)) / S,
    L + N * (t + u)⟩

theorem mixed_sub_pure {S : ℝ} (hS : S ≠ 0) (D N L k t u : ℝ) :
    mixedNormal S D N L k t u - pureNormal S D N L k t =
      ⟨(u - t) * (D + S * t), (u - t) * N⟩ := by
  apply Complex.ext <;> simp only [mixedNormal, pureNormal, Complex.sub_re, Complex.sub_im]
  · field_simp [hS]
    ring
  · ring

theorem mixedNormal_comm (S D N L k t u : ℝ) :
    mixedNormal S D N L k t u = mixedNormal S D N L k u t := by
  apply Complex.ext <;> simp only [mixedNormal] <;> ring

/-- The estimate used at crossings before inserting uniform geometric bounds. -/
theorem normalized_projection_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P : E} (hP : P ≠ 0) (Z : E) :
    ‖P‖ - ‖Z - P‖ ≤ inner ℝ Z (‖P‖⁻¹ • P) := by
  have hn : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hP
  have hu : ‖‖P‖⁻¹ • P‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have he : inner ℝ P (‖P‖⁻¹ • P) = ‖P‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
    field_simp [hn]
  have hz := neg_le_of_abs_le (abs_real_inner_le_norm (Z - P) (‖P‖⁻¹ • P))
  rw [hu, mul_one, inner_sub_left, he] at hz
  linarith

theorem mixed_projection_lower {S D N L k t u : ℝ} (hS : S ≠ 0)
    (hP : pureNormal S D N L k t ≠ 0) :
    (N ^ 2 + k + (D + S * t) ^ 2) / S -
        |u - t| * (|D + S * t| + |N|) ≤
      inner ℝ (mixedNormal S D N L k t u)
        (‖pureNormal S D N L k t‖⁻¹ • pureNormal S D N L k t) := by
  have hp : (N ^ 2 + k + (D + S * t) ^ 2) / S ≤
      ‖pureNormal S D N L k t‖ := by
    simpa only [pureNormal] using Complex.re_le_norm (pureNormal S D N L k t)
  have hd : ‖mixedNormal S D N L k t u - pureNormal S D N L k t‖ ≤
      |u - t| * (|D + S * t| + |N|) := by
    rw [mixed_sub_pure hS]
    calc
      _ ≤ |(u - t) * (D + S * t)| + |(u - t) * N| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = _ := by rw [abs_mul, abs_mul]; ring
  have hn := normalized_projection_lower hP (mixedNormal S D N L k t u)
  linarith

theorem pureNormal_ne_zero {S D N L k t : ℝ} (hS : 0 < S)
    (hNk : 0 < N ^ 2 + k) : pureNormal S D N L k t ≠ 0 := by
  have hp : 0 < (pureNormal S D N L k t).re := by
    exact div_pos (add_pos_of_pos_of_nonneg hNk (sq_nonneg _)) hS
  intro h
  simp [h] at hp

/-- The first normal component admits a lower bound which is independent of
the large `xx` component `L`. -/
theorem pureNormal_re_lower {S D N L k t smin smax K : ℝ}
    (hmin : 0 < smin) (hlo : smin ≤ S) (hhi : S ≤ smax)
    (hK : 0 ≤ K) (hk : -K ≤ k) :
    N ^ 2 / smax - K / smin ≤ (pureNormal S D N L k t).re := by
  have hS : 0 < S := lt_of_lt_of_le hmin hlo
  have ha : N ^ 2 / smax ≤ N ^ 2 / S :=
    div_le_div_of_nonneg_left (sq_nonneg N) hS hhi
  have hb : K / S ≤ K / smin := div_le_div_of_nonneg_left hK hmin hlo
  have hc : -K / S ≤ (k + (D + S * t) ^ 2) / S := by
    apply div_le_div_of_nonneg_right _ hS.le
    linarith [sq_nonneg (D + S * t)]
  simp only [neg_div] at hc
  change N ^ 2 / smax - K / smin ≤
    (N ^ 2 + k + (D + S * t) ^ 2) / S
  rw [add_assoc, add_div]
  linarith

/-- A fully uniform crossing estimate. Its right-hand side contains no `L`;
therefore the turn threshold is chosen before the fast `xx` derivative. -/
theorem uniform_mixed_projection_lower
    {S D N L k t u smin smax K dmax T : ℝ}
    (hmin : 0 < smin) (hlo : smin ≤ S) (hhi : S ≤ smax)
    (hK : 0 ≤ K) (hk : -K ≤ k) (hD : |D| ≤ dmax)
    (ht : |t| ≤ T) (hu : |u| ≤ T)
    (hP : pureNormal S D N L k t ≠ 0) :
    N ^ 2 / smax - K / smin - 2 * T * (dmax + smax * T + |N|) ≤
      inner ℝ (mixedNormal S D N L k t u)
        (‖pureNormal S D N L k t‖⁻¹ • pureNormal S D N L k t) := by
  have hS : 0 < S := lt_of_lt_of_le hmin hlo
  have hsmax : 0 ≤ smax := hS.le.trans hhi
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hdmax : 0 ≤ dmax := (abs_nonneg D).trans hD
  have hdiff : |u - t| ≤ 2 * T := by
    calc
      _ ≤ |u| + |t| := abs_sub u t
      _ ≤ 2 * T := by linarith
  have hcoef : |D + S * t| ≤ dmax + smax * T := by
    calc
      _ ≤ |D| + |S * t| := abs_add_le D (S * t)
      _ = |D| + S * |t| := by rw [abs_mul, abs_of_pos hS]
      _ ≤ dmax + smax * T := by gcongr
  have hprod : |u - t| * (|D + S * t| + |N|) ≤
      2 * T * (dmax + smax * T + |N|) := by gcongr
  have hfirst := pureNormal_re_lower (D := D) (N := N) (L := L) (t := t)
    hmin hlo hhi hK hk
  have hprojection := mixed_projection_lower (u := u) hS.ne' hP
  change N ^ 2 / smax - K / smin ≤
    (N ^ 2 + k + (D + S * t) ^ 2) / S at hfirst
  linarith

/-- Once the mixed projection exceeds the possible negative curvature term,
the ordered crossing invariant is strictly positive. -/
theorem crossing_positive_of_projection_bound {projection k delta : ℝ}
    (hp : Real.sqrt (max 0 (-k * delta ^ 2)) < projection) :
    0 < projection ^ 2 + k * delta ^ 2 := by
  have hs : 0 ≤ Real.sqrt (max 0 (-k * delta ^ 2)) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (max 0 (-k * delta ^ 2))) ^ 2 =
      max 0 (-k * delta ^ 2) := Real.sq_sqrt (le_max_left _ _)
  have hk : -k * delta ^ 2 ≤ max 0 (-k * delta ^ 2) := le_max_right _ _
  nlinarith

lemma quadratic_dominates_affine {s a c x : ℝ} (hs : 0 < s)
    (hx : max 1 (s * (a + |c| + 1)) < x) :
    c < x ^ 2 / s - a * x := by
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hx
  have hx0 : 0 < x := by linarith
  have hlinear : s * (a + |c| + 1) < x := (le_max_right _ _).trans_lt hx
  have hprod := mul_lt_mul_of_pos_right hlinear hx0
  have hquad : (a + |c| + 1) * x < x ^ 2 / s := by
    apply (lt_div_iff₀ hs).mpr
    nlinarith only [hprod]
  have habs : c ≤ |c| := le_abs_self c
  have hmul : 0 ≤ |c| * (x - 1) := mul_nonneg (abs_nonneg c) (by linarith)
  nlinarith

lemma curvature_sqrt_le {K k delta A : ℝ} (hK : 0 ≤ K) (hk : -K ≤ k)
    (hdelta : |delta| ≤ A) :
    Real.sqrt (max 0 (-k * delta ^ 2)) ≤ A * Real.sqrt K := by
  have hA : 0 ≤ A := (abs_nonneg delta).trans hdelta
  have hdsq : delta ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg delta) hA).mpr hdelta
  have hksq : -k * delta ^ 2 ≤ K * A ^ 2 := by
    calc
      _ ≤ K * delta ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ K * A ^ 2 := mul_le_mul_of_nonneg_left hdsq hK
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hA (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, Real.sq_sqrt hK]
  apply max_le
  · positivity
  · nlinarith only [hksq]

/-- There is a single threshold for the large mixed normal coefficient `N`.
It works for every `L`, every crossing with the displayed geometric bounds,
and both ordered invariants (by exchanging `t` and `u`). -/
theorem exists_uniform_crossing_threshold {smin smax K dmax T : ℝ}
    (hmin : 0 < smin) (hmax : 0 < smax) (hK : 0 ≤ K) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ (S D N L k t u : ℝ), smin ≤ S → S ≤ smax → -K ≤ k →
        |D| ≤ dmax → |t| ≤ T → |u| ≤ T → threshold < |N| →
        let P := pureNormal S D N L k t
        let Z := mixedNormal S D N L k t u
        P ≠ 0 ∧ 0 < (inner ℝ Z (‖P‖⁻¹ • P)) ^ 2 + k * (u - t) ^ 2 := by
  let C := K / smin + 2 * T * (dmax + smax * T) + 2 * T * Real.sqrt K
  let threshold := max (K + 1) (max 1 (smax * (2 * T + |C| + 1)))
  refine ⟨threshold, ?_, ?_⟩
  · have : K + 1 ≤ threshold := le_max_left _ _
    linarith
  · intro S D N L k t u hlo hhi hk hD ht hu hN
    dsimp only
    have hx1 : 1 < |N| :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hN
    have hxK : K + 1 < |N| := (le_max_left _ _).trans_lt hN
    have hNsq : K < N ^ 2 := by
      have hprod : 0 < |N| * (|N| - 1) :=
        mul_pos (lt_trans zero_lt_one hx1) (sub_pos.mpr hx1)
      nlinarith [sq_abs N]
    have hNk : 0 < N ^ 2 + k := by linarith
    have hS : 0 < S := hmin.trans_le hlo
    have hP := pureNormal_ne_zero (D := D) (L := L) (t := t) hS hNk
    refine ⟨hP, ?_⟩
    apply crossing_positive_of_projection_bound
    have hdelta : |u - t| ≤ 2 * T := (abs_sub u t).trans (by linarith)
    have hroot := curvature_sqrt_le hK hk hdelta
    have hdom := quadratic_dominates_affine (a := 2 * T) (c := C) hmax
      ((le_max_right _ _).trans_lt hN)
    rw [sq_abs] at hdom
    have hlower := uniform_mixed_projection_lower hmin hlo hhi hK hk hD ht hu hP
    dsimp only [C] at hdom
    linarith

end GeneralCrossing

end ClosedSurfaceR4.RadialMetricAlgebra

end

end OAI
