import OAI.Dynamics.StandardMap.LocalScarcity

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
noncomputable def wedge (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re
noncomputable def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im
noncomputable def quarterTurn (z : ℂ) : ℂ := Complex.I * z
lemma norm_quarterTurn (z : ℂ) : ‖quarterTurn z‖ = ‖z‖ := by simp [quarterTurn]
lemma dot_self (z : ℂ) : dot z z = ‖z‖^2 := by
  simp [dot, Complex.sq_norm, Complex.normSq_apply]
lemma wedge_quarterTurn (z : ℂ) : wedge z (quarterTurn z) = ‖z‖^2 := by
  simp [wedge, quarterTurn, Complex.sq_norm, Complex.normSq_apply]
lemma dot_quarterTurn (z : ℂ) : dot z (quarterTurn z) = 0 := by
  simp [dot, quarterTurn]
  ring
lemma dot_wedge_sq (z w : ℂ) : dot z w ^ 2 + wedge z w ^ 2 = ‖z‖^2 * ‖w‖^2 := by
  simp only [dot, wedge, Complex.sq_norm, Complex.normSq_apply]
  ring
lemma norm_add_smul_sq (z w : ℂ) (t : ℝ) :
    ‖z+t • w‖^2 = ‖z‖^2 + 2*t*dot z w+t^2*‖w‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, dot]
  ring
lemma unit_expansion (a z : ℂ) (ha : ‖a‖=1) :
    z = dot a z • a + wedge a z • quarterTurn a := by
  have hsq : a.re*a.re+a.im*a.im=1 := by
    calc
      _ = ‖a‖^2 := Complex.normSq_eq_norm_sq a
      _ = 1 := by rw [ha]; norm_num
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, dot, wedge, quarterTurn, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im] <;> nlinarith [congrArg (fun x : ℝ => x*z.re) hsq, congrArg (fun x : ℝ => x*z.im) hsq]
lemma abs_dot_le_norm_mul (z w : ℂ) : |dot z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have h0 := sq_nonneg (wedge z w)
  have hs : (dot z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma abs_wedge_le_norm_mul (z w : ℂ) : |wedge z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have hs : (wedge z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith [sq_nonneg (dot z w)]
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma wedge_add_left (z w a : ℂ) : wedge (z+w) a = wedge z a + wedge w a := by
  simp [wedge]; ring
lemma wedge_smul_left (t : ℝ) (z w : ℂ) : wedge (t • z) w = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_add_right (z w a : ℂ) : wedge z (w+a) = wedge z w + wedge z a := by
  simp [wedge]; ring
lemma wedge_smul_right (t : ℝ) (z w : ℂ) : wedge z (t • w) = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_refl (z : ℂ) : wedge z z = 0 := by dsimp [wedge]; ring
lemma wedge_swap (z w : ℂ) : wedge z w = -wedge w z := by dsimp [wedge]; ring
lemma wedge_sine_triangle (a b c : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |wedge a c| ≤ |wedge a b|+|wedge b c| := by
  have he : wedge a c = dot b a * wedge b c + wedge b a * wedge (quarterTurn b) c := by
    conv_lhs => rw [unit_expansion b a hb]
    rw [wedge_add_left, wedge_smul_left, wedge_smul_left]
  rw [he]
  calc
    _ ≤ |dot b a| * |wedge b c|+|wedge b a| * |wedge (quarterTurn b) c| := by
      simpa only [abs_mul] using abs_add_le (dot b a * wedge b c) (wedge b a * wedge (quarterTurn b) c)
    _ ≤ |wedge b c|+|wedge b a| := by
      have h1 : |dot b a|≤1 := by simpa [ha,hb] using abs_dot_le_norm_mul b a
      have h2 : |wedge (quarterTurn b) c|≤1 := by simpa [norm_quarterTurn,hb,hc] using abs_wedge_le_norm_mul (quarterTurn b) c
      nlinarith [abs_nonneg (wedge b c), abs_nonneg (wedge b a)]
    _ = _ := by rw [wedge_swap b a, abs_neg]; ring
lemma exists_unit_opNorm (A : ℂ →L[ℝ] ℂ) : ∃ a : ℂ, ‖a‖=1 ∧ ‖A a‖=‖A‖ := by
  obtain ⟨a,ha,hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    (show (sphere (0 : ℂ) 1).Nonempty by exact ⟨1,by simp⟩) A.continuous.norm.continuousOn
  have ha : ‖a‖=1 := by simpa [mem_sphere,dist_zero_right] using ha
  refine ⟨a,ha,le_antisymm (by simpa [ha] using A.le_opNorm a) ?_⟩
  apply A.opNorm_le_bound (norm_nonneg _)
  intro z
  by_cases hz : z=0
  · simp [hz]
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  have hm := hmax (show (‖z‖⁻¹ : ℝ) • z ∈ sphere (0 : ℂ) 1 by
    simp [ne_of_gt hn])
  change ‖A ((‖z‖⁻¹ : ℝ) • z)‖ ≤ ‖A a‖ at hm
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hm
  exact (div_le_iff₀ hn).mp (by simpa [div_eq_mul_inv,mul_comm] using hm)
lemma linear_term_of_quadratic_nonpos (d c : ℝ) (h : ∀ t : ℝ, 2*d*t-c*t^2≤0) : d=0 := by
  have hm : IsLocalMax (fun t : ℝ => 2*d*t-c*t^2) 0 := by
    exact Eventually.of_forall (fun t => by simpa using h t)
  have hd : HasDerivAt (fun t : ℝ => 2*d*t-c*t^2) (2*d) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul (2*d)).sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul c) using 1 ; norm_num
  linarith [hm.hasDerivAt_eq_zero hd]
lemma orthogonal_image_of_max (A : ℂ →L[ℝ] ℂ) (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) :
    dot (A a) (A (quarterTurn a))=0 := by
  apply linear_term_of_quadratic_nonpos _ (‖A‖^2-‖A (quarterTurn a)‖^2)
  intro t
  have h0 := A.le_opNorm (a+t • quarterTurn a)
  have hs : ‖A (a+t • quarterTurn a)‖^2 ≤ ‖A‖^2*‖a+t • quarterTurn a‖^2 := by
    nlinarith [norm_nonneg (A (a+t • quarterTurn a)), norm_nonneg A,
      norm_nonneg (a+t • quarterTurn a)]
  rw [map_add,map_smul,norm_add_smul_sq,norm_add_smul_sq,hA,ha,norm_quarterTurn,ha,dot_quarterTurn] at hs
  nlinarith

def PlaneAreaPreserving (A : ℂ →L[ℝ] ℂ) : Prop := ∀ z w, wedge (A z) (A w)=wedge z w
lemma PlaneAreaPreserving.singular_pair {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A) :
    ∃ a : ℂ, ‖a‖=1 ∧ ‖A a‖=‖A‖ ∧ dot (A a) (A (quarterTurn a))=0 ∧
      ‖A (quarterTurn a)‖=‖A‖⁻¹ ∧ 1≤‖A‖ := by
  obtain ⟨a,ha,hA⟩ := exists_unit_opNorm A
  have hd := orthogonal_image_of_max A a ha hA
  have hw : wedge (A a) (A (quarterTurn a))=1 := by rw [h, wedge_quarterTurn, ha]; norm_num
  have hs := dot_wedge_sq (A a) (A (quarterTurn a))
  rw [hd,hw,hA] at hs
  have hp : ‖A‖*‖A (quarterTurn a)‖=1 := by
    have hpos := mul_nonneg (norm_nonneg (A : ℂ →L[ℝ] ℂ)) (norm_nonneg (A (quarterTurn a)))
    have he : (‖A‖*‖A (quarterTurn a)‖)^2=1^2 := by nlinarith
    exact (sq_eq_sq₀ hpos (by norm_num)).mp he
  have hn : 0<‖A‖ := by
    have hh:= norm_nonneg (A : ℂ →L[ℝ] ℂ)
    by_contra hh'; have hz : ‖A‖=0 := le_antisymm (not_lt.mp hh') hh
    simp [hz] at hp
  have hi : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff (ne_of_gt hn)).mpr
    simpa [mul_comm] using hp
  refine ⟨a,ha,hA,hd,hi,?_⟩
  have hb : ‖A (quarterTurn a)‖≤‖A‖ := by simpa [norm_quarterTurn,ha] using A.le_opNorm (quarterTurn a)
  nlinarith [hp]
end StandardMapEntropy

end OAI
