import OAI.Analysis.KadisonSimilarity.Derivation.DicksonRow
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional

namespace OAI

/-! The norm-attaining case of the little Grothendieck inequality.
The unitary paths and their quadratic estimates are constructed explicitly. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- At a norm-attaining unit, the supporting vector functional is a state. -/
theorem exists_normAttainingState (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ ∀ a, f a = inner ℂ (T 1) (T a) := by
  let φ : A →L[ℂ] ℂ := (innerSL ℂ (T 1)).comp T
  have hφ1 : φ 1 = 1 := by
    change inner ℂ (T 1) (T 1) = 1
    rw [inner_self_eq_norm_sq_to_K, h1]
    norm_num
  have hnle : ‖φ‖ ≤ 1 := by
    calc
      _ ≤ ‖innerSL ℂ (T 1)‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖T‖ := by rw [innerSL_apply_norm, h1, one_mul]
      _ ≤ 1 := hT
  have hn : ‖φ‖ = 1 := by
    apply le_antisymm hnle
    simpa only [hφ1, norm_one, mul_one] using φ.le_opNorm (1 : A)
  have hm : Monotone φ := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr (by
    rw [hn, hφ1]
    norm_num)
  let f : A →P[ℂ] ℂ := { φ with monotone' := hm }
  exact ⟨f.toPositiveLinearMap, hφ1, fun _ => rfl⟩

/-- The two conjugate unitary paths give a quadratic contraction estimate. -/
theorem contraction_sqrt_complement (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (a : A) (ha : IsSelfAdjoint a) (hna : ‖a‖ ≤ 1) :
    ‖T a‖ ^ 2 + ‖T (CFC.sqrt (1 - a ^ 2))‖ ^ 2 ≤ 1 := by
  let r := CFC.sqrt (1 - a ^ 2)
  have hu : a + Complex.I • r ∈ unitary A :=
    ha.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary a hna
  have hv : a - Complex.I • r ∈ unitary A := by
    have hstar := Unitary.star_mem hu
    have hr : star r = r := (CFC.sqrt_nonneg (1 - a ^ 2)).star_eq
    simpa only [star_add, star_smul, ha.star_eq, Complex.star_def, map_add,
      Complex.conj_I, hr, neg_smul,
      ← sub_eq_add_neg] using hstar
  have hplus : ‖T (a + Complex.I • r)‖ ≤ 1 := by
    exact (T.le_opNorm _).trans (by rw [CStarRing.norm_of_mem_unitary hu, mul_one]; exact hT)
  have hminus : ‖T (a - Complex.I • r)‖ ≤ 1 := by
    exact (T.le_opNorm _).trans (by rw [CStarRing.norm_of_mem_unitary hv, mul_one]; exact hT)
  have hpar := parallelogram_law_with_norm ℂ (T a) (Complex.I • T r)
  have hi : ‖Complex.I • T r‖ = ‖T r‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hi] at hpar
  have hp : ‖T a + Complex.I • T r‖ ≤ 1 := by simpa only [map_add, map_smul] using hplus
  have hm : ‖T a - Complex.I • T r‖ ≤ 1 := by simpa only [map_sub, map_smul] using hminus
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  change ‖T a‖ ^ 2 + ‖T r‖ ^ 2 ≤ 1
  nlinarith

/-- A scalar square-root expansion with a uniform quadratic remainder. -/
theorem sqrt_complement_remainder (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    |1 - Real.sqrt (1 - s) - s / 2| ≤ s ^ 2 := by
  have hr : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (1 - s) ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have hr1 : Real.sqrt (1 - s) ≤ 1 := by nlinarith
  have hd : 0 ≤ 1 - Real.sqrt (1 - s) := by linarith
  have hdle : 1 - Real.sqrt (1 - s) ≤ s := by
    nlinarith
  have he : 1 - Real.sqrt (1 - s) - s / 2 = (1 - Real.sqrt (1 - s)) ^ 2 / 2 := by
    nlinarith
  rw [he, abs_of_nonneg (by positivity)]
  have hsq := pow_le_pow_left₀ hd hdle 2
  nlinarith [sq_nonneg s]

/-- The fourth-order remainder for the unitary path, still expressed in
one continuous functional calculus. -/
def cfcSqrtRemainder (a : A) (t : ℝ) : A :=
  cfc (fun x : ℝ => 1 - Real.sqrt (1 - (t * x) ^ 2) - (t * x) ^ 2 / 2) a

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_cfcSqrtRemainder_le (a : A) (hna : ‖a‖ ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) : ‖cfcSqrtRemainder a t‖ ≤ t ^ 4 := by
  apply norm_cfc_le (by positivity)
  intro x hx
  have hxabs : |x| ≤ 1 := (spectrum.norm_le_norm_of_mem hx).trans hna
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr hxabs
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have hprod : (t * x) ^ 2 ≤ t ^ 2 := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg t)]
  have hsmall : (t * x) ^ 2 ≤ 1 / 2 := by linarith
  have he := sqrt_complement_remainder ((t * x) ^ 2) (sq_nonneg _) hsmall
  rw [Real.norm_eq_abs]
  exact he.trans (by nlinarith [sq_nonneg ((t * x) ^ 2), sq_nonneg (t ^ 2)])

omit [Nontrivial A] in
/-- Interpret the scalar remainder as the actual square-root error. -/
theorem cfcSqrtRemainder_eq (a : A) (ha : IsSelfAdjoint a) (t : ℝ)
    (hpos : 0 ≤ 1 - (t • a) ^ 2) :
    cfcSqrtRemainder a t =
      1 - CFC.sqrt (1 - (t • a) ^ 2) - (t ^ 2 / 2) • a ^ 2 := by
  have hpoly : cfc (fun x : ℝ => 1 - (t * x) ^ 2) a = 1 - (t • a) ^ 2 := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => (t * x) ^ 2) a,
      cfc_const_one ℝ a ha,
      cfc_pow (fun x : ℝ => t * x) 2 a (by fun_prop) ha, cfc_const_mul_id t a ha]
  have hroot : cfc (fun x : ℝ => Real.sqrt (1 - (t * x) ^ 2)) a =
      CFC.sqrt (1 - (t • a) ^ 2) := by
    rw [cfc_comp' Real.sqrt (fun x : ℝ => 1 - (t * x) ^ 2) a,
      hpoly, CFC.sqrt_eq_real_sqrt _ hpos, cfcₙ_eq_cfc]
  have hquad : cfc (fun x : ℝ => (t * x) ^ 2 / 2) a = (t ^ 2 / 2) • a ^ 2 := by
    have he : (fun x : ℝ => (t * x) ^ 2 / 2) = (fun x : ℝ => (t ^ 2 / 2) * x ^ 2) := by
      funext x
      ring
    rw [he, cfc_const_mul (t ^ 2 / 2) (fun x : ℝ => x ^ 2) a (by fun_prop),
      cfc_pow_id a 2 ha]
  unfold cfcSqrtRemainder
  rw [cfc_sub (fun x : ℝ => 1 - Real.sqrt (1 - (t * x) ^ 2))
    (fun x : ℝ => (t * x) ^ 2 / 2) a,
    cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => Real.sqrt (1 - (t * x) ^ 2)) a,
    cfc_const_one ℝ a ha, hroot, hquad]

/-- A fourth-order error disappears after dividing the quadratic term. -/
theorem le_of_scaled_quadratic_approximations {x y : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → t ^ 2 * x ≤ t ^ 2 * y + 2 * t ^ 4) :
    x ≤ y := by
  by_contra hxy
  have hgap : 0 < x - y := by linarith
  let t := min (1 / 2 : ℝ) (Real.sqrt (x - y) / 2)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have hthalf : t ≤ 1 / 2 := min_le_left _ _
  have htsqrt : t ≤ Real.sqrt (x - y) / 2 := min_le_right _ _
  have hsqrt := Real.sq_sqrt hgap.le
  have hsmall : 2 * t ^ 2 < x - y := by
    have hsq := pow_le_pow_left₀ ht.le htsqrt 2
    nlinarith
  have hprod : 0 < t ^ 2 * (x - y - 2 * t ^ 2) :=
    mul_pos (sq_pos_of_pos ht) (by linarith)
  have hbound := h t ht hthalf
  nlinarith

/-- The unitary-path estimate recovers the square bound on self-adjoint contractions. -/
theorem normAttaining_selfAdjoint_contraction (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) (a : A) (ha : IsSelfAdjoint a) (hna : ‖a‖ ≤ 1) :
    ‖T a‖ ^ 2 ≤ (inner ℂ (T 1) (T (a ^ 2))).re := by
  apply le_of_scaled_quadratic_approximations
  intro t ht ht1
  have hta : ‖t • a‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg a]
  have hsa : IsSelfAdjoint (t • a) := (IsSelfAdjoint.all t).smul ha
  have hpos : 0 ≤ 1 - (t • a) ^ 2 := by
    rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg ((t • a) ^ 2),
      sq, hsa.norm_mul_self, sq_le_one_iff₀ (norm_nonneg _)]
    exact hta
  have hpath := contraction_sqrt_complement T hT (t • a) hsa hta
  have hrem : ‖T (cfcSqrtRemainder a t)‖ ≤ t ^ 4 :=
    (T.le_opNorm _).trans <| (mul_le_of_le_one_left (norm_nonneg _) hT).trans
      (norm_cfcSqrtRemainder_le a hna ht.le ht1)
  have hinner : (inner ℂ (T 1) (T (cfcSqrtRemainder a t))).re ≤ t ^ 4 := by
    exact (re_inner_le_norm (𝕜 := ℂ) (T 1) (T (cfcSqrtRemainder a t))).trans (by simpa only [h1, one_mul] using hrem)
  have hpair := norm_sub_sq (𝕜 := ℂ) (T 1) (T (CFC.sqrt (1 - (t • a) ^ 2)))
  have hnonneg := sq_nonneg ‖T 1 - T (CFC.sqrt (1 - (t • a) ^ 2))‖
  have hsmul (c : ℝ) (v : H) :
      inner ℂ (T 1) (c • v) = (c : ℂ) * inner ℂ (T 1) v := by
    rw [← Complex.coe_smul c v, inner_smul_right]
  rw [cfcSqrtRemainder_eq a ha t hpos, map_sub, map_sub,
    ContinuousLinearMap.map_smul_of_tower, inner_sub_right, inner_sub_right, hsmul,
    inner_self_eq_norm_sq_to_K] at hinner
  simp only [ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    mul_pow] at hpath
  simp only [Complex.sub_re, Complex.ofReal_re, h1,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hinner
  norm_num at hinner
  rw [h1] at hpair
  change ‖T 1 - T (CFC.sqrt (1 - (t • a) ^ 2))‖ ^ 2 =
    1 ^ 2 - 2 * (inner ℂ (T 1) (T (CFC.sqrt (1 - (t • a) ^ 2)))).re +
    ‖T (CFC.sqrt (1 - (t • a) ^ 2))‖ ^ 2 at hpair
  nlinarith only [hpath, hinner, hpair, hnonneg]

/-- Homogeneity removes the contraction restriction. -/
theorem normAttaining_selfAdjoint (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) (a : A) (ha : IsSelfAdjoint a) :
    ‖T a‖ ^ 2 ≤ (inner ℂ (T 1) (T (a ^ 2))).re := by
  by_cases hz : a = 0
  · simp [hz]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hna : ‖‖a‖⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have h := normAttaining_selfAdjoint_contraction T hT h1 (‖a‖⁻¹ • a)
    ((IsSelfAdjoint.all _).smul ha) hna
  have hsmul (c : ℝ) (v : H) :
      inner ℂ (T 1) (c • v) = (c : ℂ) * inner ℂ (T 1) v := by
    rw [← Complex.coe_smul c v, inner_smul_right]
  simp only [ContinuousLinearMap.map_smul_of_tower, smul_pow, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hn.le), mul_pow, hsmul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp h

/-- Haagerup's norm-attaining inequality, obtained from the real and imaginary parts. -/
theorem normAttaining_grothendieck (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (h1 : ‖T 1‖ = 1) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧
      ∀ a, ‖T a‖ ^ 2 ≤ (f (star a * a)).re + (f (a * star a)).re := by
  obtain ⟨f, hf1, hf⟩ := exists_normAttainingState T hT h1
  refine ⟨f, hf1, fun a => ?_⟩
  let b : A := realPart a
  let c : A := imaginaryPart a
  have hb := normAttaining_selfAdjoint T hT h1 b selfAdjoint.isSelfAdjoint
  have hc := normAttaining_selfAdjoint T hT h1 c selfAdjoint.isSelfAdjoint
  rw [← hf (b ^ 2)] at hb
  rw [← hf (c ^ 2)] at hc
  have hdec : b + Complex.I • c = a := realPart_add_I_smul_imaginaryPart a
  have htdec : T b + Complex.I • T c = T a := by rw [← map_smul, ← map_add, hdec]
  have hpar := parallelogram_law_with_norm ℂ (T b) (Complex.I • T c)
  rw [norm_smul, Complex.norm_I, one_mul, htdec] at hpar
  have hsum : (f (star a * a)).re + (f (a * star a)).re =
      2 * ((f (b ^ 2)).re + (f (c ^ 2)).re) := by
    rw [← Complex.add_re, ← map_add, star_mul_self_add_self_mul_star]
    simp only [two_smul, two_mul, map_add, Complex.add_re, b, c, pow_two]
  rw [hsum]
  nlinarith [sq_nonneg ‖T b - Complex.I • T c‖]

/-- Transport the norm-attaining inequality from the identity to a unitary. -/
theorem unitaryNormAttaining_grothendieck (T : A →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (u : unitary A) (hu : ‖T (u : A)‖ = 1) :
    ∃ f g : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ g 1 = 1 ∧
      ∀ a, ‖T a‖ ^ 2 ≤ (f (star a * a)).re + (g (a * star a)).re := by
  let S := T.comp (ContinuousLinearMap.mul ℂ A (u : A))
  have hS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    calc
      ‖S a‖ ≤ ‖T‖ * ‖(u : A) * a‖ := T.le_opNorm _
      _ ≤ ‖(u : A) * a‖ := mul_le_of_le_one_left (norm_nonneg _) hT
      _ ≤ ‖(u : A)‖ * ‖a‖ := norm_mul_le _ _
      _ = 1 * ‖a‖ := by rw [CStarRing.norm_coe_unitary]
  have hS1 : ‖S 1‖ = 1 := by simpa [S] using hu
  obtain ⟨f, hf1, hf⟩ := normAttaining_grothendieck S hS hS1
  let gL : A →ₗ[ℂ] ℂ := f.toLinearMap.comp
    ((LinearMap.mulRight ℂ (u : A)).comp (LinearMap.mulLeft ℂ (star (u : A))))
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ gL
    (fun a ha => f.map_nonneg (star_left_conjugate_nonneg ha (u : A)))
  have hg (a : A) : g a = f (star (u : A) * a * (u : A)) := rfl
  refine ⟨f, g, hf1, ?_, fun a => ?_⟩
  · rw [hg, mul_one, Unitary.star_mul_self_of_mem u.prop, hf1]
  · have h := hf (star (u : A) * a)
    have hval : S (star (u : A) * a) = T a := by
      change T ((u : A) * (star (u : A) * a)) = T a
      rw [← mul_assoc, Unitary.mul_star_self_of_mem u.prop, one_mul]
    have hs : star (star (u : A) * a) * (star (u : A) * a) = star a * a := by
      rw [star_mul, star_star, mul_assoc, ← mul_assoc (u : A),
        Unitary.mul_star_self_of_mem u.prop, one_mul]
    have ht : (star (u : A) * a) * star (star (u : A) * a) =
        star (u : A) * (a * star a) * (u : A) := by
      rw [star_mul, star_star]
      simp only [mul_assoc]
    simpa only [hval, hs, ht, hg] using h

end KadisonSimilarity

end

end OAI
