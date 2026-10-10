import OAI.Dynamics.StandardMap.PlaneGeometry

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma norm_smul_add_smul_sq (z w : ℂ) (s t : ℝ) :
    ‖s • z+t • w‖^2 = s^2*‖z‖^2+2*s*t*dot z w+t^2*‖w‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, dot]
  ring
lemma dot_quarterTurn_right (a z : ℂ) : dot a (quarterTurn z) = -wedge a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma wedge_quarterTurn_left (a z : ℂ) : wedge (quarterTurn a) z = -dot a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma dot_comm (a z : ℂ) : dot a z = dot z a := by dsimp [dot]; ring
lemma PlaneAreaPreserving.norm_map_sq {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖^2 = dot a z ^ 2 * ‖A‖^2 + wedge a z ^ 2 * ‖A‖⁻¹^2 := by
  have hd := orthogonal_image_of_max A a ha hA
  have hw : wedge (A a) (A (quarterTurn a))=1 := by rw [h,wedge_quarterTurn,ha]; norm_num
  have hs := dot_wedge_sq (A a) (A (quarterTurn a))
  rw [hd,hw,hA] at hs
  have hprod : ‖A‖*‖A (quarterTurn a)‖=1 := by
    have hp := mul_nonneg (norm_nonneg (A : ℂ →L[ℝ] ℂ)) (norm_nonneg (A (quarterTurn a)))
    exact (sq_eq_sq₀ hp (by norm_num)).mp (by nlinarith [hs])
  have hn : ‖A‖≠0 := by intro hz; simp [hz] at hprod
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    rw [← one_div]; apply (eq_div_iff hn).mpr; simpa [mul_comm] using hprod
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul,norm_smul_add_smul_sq,hA,hd,hb]
  ring
lemma PlaneAreaPreserving.norm_lower {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A) (z : ℂ) :
    ‖z‖ ≤ ‖A‖*‖A z‖ := by
  obtain ⟨a,ha,hA,hd,hb,hD⟩ := h.singular_pair
  have hsq := h.norm_map_sq a ha hA z
  have hdw := dot_wedge_sq a z
  rw [ha] at hdw
  have hn : ‖A‖≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hD)
  have hid : ‖A‖^2*(‖A‖⁻¹)^2=1 := by field_simp
  have hm : ‖A‖^2*‖A z‖^2=(‖A‖^2)^2*dot a z^2+wedge a z^2 := by
    calc
      _ = ‖A‖^2 * (dot a z^2*‖A‖^2+wedge a z^2*‖A‖⁻¹^2) := by rw [hsq]
      _ = (‖A‖^2)^2*dot a z^2+(‖A‖^2*‖A‖⁻¹^2)*wedge a z^2 := by ring
      _ = _ := by rw [hid]; ring
  have h4 : 1≤(‖A‖^2)^2 := by nlinarith [sq_nonneg (‖A‖^2-1)]
  have hsqle : ‖z‖^2≤(‖A‖*‖A z‖)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) (sq_nonneg (dot a z))]
  exact (sq_le_sq₀ (norm_nonneg z) (mul_nonneg (norm_nonneg A) (norm_nonneg _))).mp hsqle
lemma PlaneAreaPreserving.norm_inverse {A B : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B)
    (hAB : ∀ z, A (B z)=z) (hBA : ∀ z, B (A z)=z) : ‖A‖=‖B‖ := by
  apply le_antisymm
  · apply A.opNorm_le_bound (norm_nonneg _)
    intro z
    simpa [hBA] using hB.norm_lower (A z)
  · apply B.opNorm_le_bound (norm_nonneg _)
    intro z
    simpa [hAB] using hA.norm_lower (B z)
lemma PlaneAreaPreserving.comp {A B : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B) : PlaneAreaPreserving (A.comp B) := by
  intro z w
  exact (hA (B z) (B w)).trans (hB z w)
lemma PlaneAreaPreserving.norm_le_product {A B C : ℂ →L[ℝ] ℂ}
    (_hB : PlaneAreaPreserving B) (hBC : ∀ z, C (B z)=A z) : ‖A‖≤‖C‖*‖B‖ := by
  have he : A=C.comp B := by ext z; exact (hBC z).symm
  rw [he]
  exact C.opNorm_comp_le B
lemma expanded_projection_bound {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A‖*|dot a z| ≤ ‖A z‖ := by
  have hs := h.norm_map_sq a ha hA z
  have hnon := mul_nonneg (sq_nonneg (wedge a z)) (sq_nonneg (‖A‖⁻¹))
  have hsq : (‖A‖*|dot a z|)^2≤‖A z‖^2 := by nlinarith [sq_abs (dot a z)]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (abs_nonneg _)) (norm_nonneg _)).mp hsq
lemma two_singular_upper {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖ ≤ ‖A‖*|dot a z| + ‖A‖⁻¹*|wedge a z| := by
  have hd := orthogonal_image_of_max A a ha hA
  have hs := h.norm_map_sq a ha hA (quarterTurn a)
  rw [dot_quarterTurn,wedge_quarterTurn,ha] at hs
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(dot a z : ℝ) • A a‖+‖(wedge a z : ℝ) • A (quarterTurn a)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hA,hb]; ring
lemma PlaneAreaPreserving.small_two_endpoints {A B C : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hBC : ∀ z, C (A z)=B z) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖A z‖=‖A‖⁻¹ ∧ ‖B z‖≤‖C‖*‖A‖⁻¹ := by
  obtain ⟨a,ha,hAa,hd,hb,hD⟩ := hA.singular_pair
  refine ⟨quarterTurn a, (norm_quarterTurn a).trans ha, hb, ?_⟩
  rw [← hBC]
  simpa [hb] using C.le_opNorm (A (quarterTurn a))
end StandardMapEntropy

end OAI
