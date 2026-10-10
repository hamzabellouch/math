import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.EuclideanEllipse
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseExit
import OAI.Probability.CriticalPercolation.GraphGeometry.MovingStrips

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.EuclideanEllipse

lemma rotated_re (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=(c : ℂ).re*z.re+(c : ℂ).im*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_re]
lemma rotated_im (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).im= -(c : ℂ).im*z.re+(c : ℂ).re*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_im,add_comm]
lemma norm_rotated (c : Circle) (z : ℂ) : ‖(c : ℂ)⁻¹*z‖=‖z‖ := by
  rw [norm_mul,norm_inv,Circle.norm_coe,inv_one,one_mul]

lemma original_components (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=R*((c : ℂ)⁻¹*normalize R W c z).re ∧
    ((c : ℂ)⁻¹*z).im=W*((c : ℂ)⁻¹*normalize R W c z).im := by
  obtain ⟨hre,him⟩ := normalize_components R W c z
  rw [hre,him]
  constructor <;> field_simp

lemma normalize_transverse_le (R W zeta : ℝ) (hR : R≠0) (hW : 0<W)
    (c : Circle) (z : ℂ) (hz : ‖normalize R W c z‖≤1+zeta) :
    |((c : ℂ)⁻¹*z).im|≤W*(1+zeta) := by
  rw [(original_components R W hR hW.ne' c z).2,abs_mul,abs_of_pos hW]
  apply mul_le_mul_of_nonneg_left _ hW.le
  exact ((Complex.abs_im_le_norm _).trans_eq (norm_rotated c _)).trans hz

lemma normalized_far_major (R W zeta : ℝ) (hR : 0<R) (hW : W≠0)
    (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|)
    (z : ℂ) (hz : ‖normalize R W c z-(d : ℂ)‖≤2*zeta) :
    R/10≤|((c : ℂ)⁻¹*z).re| := by
  have hdiff : |((c : ℂ)⁻¹*normalize R W c z).re-((c : ℂ)⁻¹*(d : ℂ)).re|≤2*zeta := by
    calc
      _ = |((c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))).re| := by rw [mul_sub,Complex.sub_re]
      _ ≤ ‖(c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))‖ := Complex.abs_re_le_norm _
      _ = ‖normalize R W c z-(d : ℂ)‖ := norm_rotated c _
      _ ≤ 2*zeta := hz
  have ha := abs_sub_abs_le_abs_sub (((c : ℂ)⁻¹*(d : ℂ)).re)
    (((c : ℂ)⁻¹*normalize R W c z).re)
  rw [abs_sub_comm] at ha
  have hmajor : (1 : ℝ)/10≤|((c : ℂ)⁻¹*normalize R W c z).re| := by linarith
  rw [(original_components R W hR.ne' hW c z).1,abs_mul,abs_of_pos hR]
  nlinarith

lemma doubled_angle_le_sine (theta : ℝ) :
    |((2*theta : ℝ) : Real.Angle).toReal|≤Real.pi*|Real.sin theta| := by
  let t : Real.Angle := ((2*theta : ℝ) : Real.Angle)
  have ht : |t.toReal/2|≤Real.pi/2 := by rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; exact div_le_div_of_nonneg_right (Real.Angle.abs_toReal_le_pi t) (by norm_num)
  have heq : 2•((t.toReal/2 : ℝ) : Real.Angle)=2•((theta : ℝ) : Real.Angle) := by
    rw [Real.Angle.two_nsmul_coe_div_two,Real.Angle.coe_toReal]
    dsimp [t]
    rw [←Real.Angle.coe_nsmul]
    congr 1
    simp only [two_smul]
    ring
  have hs := Real.Angle.abs_sin_eq_of_two_nsmul_eq heq
  simp only [Real.Angle.sin_coe] at hs
  have hj := Real.mul_abs_le_abs_sin ht
  rw [hs,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hj
  have hp := Real.pi_pos
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  field_simp at hm
  dsimp [t] at hm
  nlinarith

end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ellipseExit_subset_longStrip (pi : V → ℂ) (A : Set V) (R W zeta : ℝ)
    (hR : 0<R) (hW : 0<W) (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|) :
    G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d ⊆
      G.longStripExit (fun x => (pi x).re) (fun x => (pi x).im) A
        (W*(1+zeta)) (R/10) (c : ℂ).re (c : ℂ).im := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.ellipseExit_iff _ A zeta d ω).mp hω
  have hpath : ∀ y∈w.support, |normalCoordinate (fun x => (pi x).re)
      (fun x => (pi x).im) (c : ℂ).re (c : ℂ).im y|≤W*(1+zeta) := by
    intro y hy
    change |-(c : ℂ).im*(pi y).re+(c : ℂ).re*(pi y).im|≤_
    rw [←EuclideanEllipse.rotated_im]
    exact EuclideanEllipse.normalize_transverse_le R W zeta hR.ne' hW c (pi y) (hw y hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,G.walk_reachable_induced _ ω w hpath,hpath x w.end_mem_support,?_⟩
  change R/10≤|(c : ℂ).re*(pi x).re+(c : ℂ).im*(pi x).im|
  rw [←EuclideanEllipse.rotated_re]
  exact EuclideanEllipse.normalized_far_major R W zeta hR hW.ne' hzeta c d hd (pi x) hx

theorem favored_boundary_major_small [Countable V] [Countable E]
    (hl : G.LocallyFinite) (mu : Measure (Set E)) [IsFiniteMeasure mu]
    (pi : V → ℂ) (A : Set V) (hA : A.Finite) (W zeta r : ℝ)
    (hW : 0<W) (hzeta : 0≤zeta) (hzeta' : zeta≤1/10000) (hr : 0<r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      mu (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) :
    ∃ N : ℕ, ∀ R : ℝ, 0<R → 10*(N : ℝ)≤R → ∀ c d : Circle,
      r ≤ mu.real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) →
      |((c : ℂ)⁻¹*(d : ℂ)).re|<1/8 := by
  obtain ⟨N,hN⟩ := G.uniform_long_strip_exits hl mu (fun x => (pi x).re)
    (fun x => (pi x).im) A hA (W*(1+zeta)) r (by positivity) hr
    (fun a b hab => hnull a b hab _)
  refine ⟨N,?_⟩
  intro R hR hRN c d hprob
  by_contra hn
  have hunit : (c : ℂ).re^2+(c : ℂ).im^2=1 := by
    have h := Circle.normSq_coe c
    simpa [Complex.normSq_apply,pow_two] using h
  have hsmall := hN (R/10) (by linarith) (c : ℂ).re (c : ℂ).im hunit
  have hmono := ENNReal.toReal_mono (measure_ne_top mu _)
    (measure_mono (G.ellipseExit_subset_longStrip pi A R W zeta hR hW hzeta' c d (le_of_not_gt hn)))
  exact (not_lt_of_ge (hprob.trans hmono) hsmall).elim

end CriticalPercolation.BondGraph
end
end
end

end OAI
