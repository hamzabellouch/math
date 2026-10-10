import OAI.Geometry.Kahler.BasePhaseAveraging

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_low_moment {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k n : ℕ} (hband : PhaseBandwidth W ℓ) (hgap : n+ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) (p ξ : Sphere) :
    (∫ z : Circle, phaseChar n z*(densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)):ℂ) ∂circleMeasure)=0 := by
  classical
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun m => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a m *
          ((f (densityHeight k p ξ) - (m:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun m => (k:ℤ)+m)) (fun m => A (m-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z,phaseSum_shift]
    simp_rw [hh]
    have hb : ∀ m ∈ s.image (fun m => (k:ℤ)+m), (n:ℤ) < m := by
      intro m hm
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hm
      have hl' := (abs_le.mp (hs l hl)).1
      omega
    rw [phase_real_sum_moment _ _ n (fun m hm => lt_of_le_of_lt (by exact_mod_cast Nat.zero_le n) (hb m hm))]
    exact Finset.sum_eq_zero (fun m hm => ite_eq_right (ne_of_gt (hb m hm)))
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,Complex.ofReal_zero,mul_zero,integral_zero]

lemma circle_real_product_zero {f : Circle → ℝ} (hf : Continuous f) (n : ℕ) (v : ℂ)
    (hz : (∫ z : Circle, phaseChar n z*(f z:ℂ) ∂circleMeasure)=0) :
    (∫ z : Circle, (phaseChar n z*v).re*f z ∂circleMeasure)=0 := by
  have hi : Integrable (fun z : Circle => v*(phaseChar n z*(f z:ℂ))) circleMeasure :=
    compact_continuous_integrable (continuous_const.mul ((phaseChar_continuous _).mul (Complex.continuous_ofReal.comp hf)))
  have he : ∀ z : Circle, (phaseChar n z*v).re*f z=(v*(phaseChar n z*(f z:ℂ))).re := by
    intro z
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero]
    ring
  simp_rw [he]
  have hh : (∫ z : Circle, (v*(phaseChar n z*(f z:ℂ))).re ∂circleMeasure)=
      (∫ z : Circle, v*(phaseChar n z*(f z:ℂ)) ∂circleMeasure).re := integral_re hi
  rw [hh,integral_const_mul,hz,mul_zero]
  rfl

lemma sphere_eigen_integral_zero {W : Sphere → ℝ} (hW : Continuous W) {n : ℕ}
    {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ)
    (hz : ∀ ξ : Sphere, (∫ z : Circle, phaseChar n z*(W (phaseAction z ξ):ℂ) ∂circleMeasure)=0) :
    (∫ ξ : Sphere, (V ξ).re*W ξ ∂sigma)=0 := by
  have hcont : Continuous (fun ξ : Sphere => (V ξ).re*W ξ) := (Complex.continuous_re.comp hV).mul hW
  rw [sigma_phase_average hcont]
  apply integral_eq_zero_of_ae
  refine Eventually.of_forall (fun ξ => ?_)
  simp only [hphase]
  exact circle_real_product_zero (hW.comp (phaseAction_continuous.comp (continuous_id.prodMk continuous_const))) n (V ξ) (hz ξ)

lemma correction_eigenfunction_integral {a : ℝ} (pr : RadialProfiles a) {W : Base → ℝ}
    (hW : ContDiff ℝ ∞ W) {ℓ k n : ℕ} (hband : PhaseBandwidth W ℓ) (hgap : n+ℓ < k)
    (p : Sphere) {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ) :
    (∫ ξ : Sphere, (V ξ).re*densityCorrection k pr.R pr.f pr.b W p ξ ∂sigma)=0 := by
  have hk : 0 < k := by omega
  have hco : Continuous (fun ξ : Sphere => densityCorrection k pr.R pr.f pr.b W p ξ) :=
    (densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b hW pr.tail p).continuous.comp continuous_subtype_val
  exact sphere_eigen_integral_zero hco hV hphase
    (fun ξ => densityCorrection_low_moment (hW.differentiable (by norm_num)) hband hgap pr.R pr.f pr.b p ξ)

lemma density_low_moment_step {a : ℝ} (pr : RadialProfiles a) {Q : ℕ} (hQ : 0 < Q)
    (P : ℕ → Finset Sphere) (j : ℕ) {n : ℕ} (hgap : n+densityBandwidth Q j < Q^(j+1))
    {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ) :
    (∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P (j+1) ξ ∂sigma)=
      ∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P j ξ ∂sigma := by
  have hW := density_smooth hQ pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j
  have hband := density_bandwidth hQ pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j
  have hc : ∀ p ∈ P (Q^(j+1)), Integrable (fun ξ : Sphere => (V ξ).re*
      densityCorrection (Q^(j+1)) pr.R pr.f pr.b (density Q pr.R pr.f pr.b P j) p ξ) sigma := by
    intro p hp
    exact compact_continuous_integrable ((Complex.continuous_re.comp hV).mul
      ((densityCorrection_smooth (pow_pos hQ _) pr.cutoff_lt pr.smooth_f pr.smooth_b hW pr.tail p).continuous.comp continuous_subtype_val))
  simp only [density,mul_add,Finset.mul_sum]
  have hi : Integrable (fun ξ : Sphere => (V ξ).re*density Q pr.R pr.f pr.b P j ξ) sigma :=
    compact_continuous_integrable ((Complex.continuous_re.comp hV).mul (hW.continuous.comp continuous_subtype_val))
  rw [integral_add hi
    (integrable_finsetSum _ hc),integral_finsetSum _ hc]
  simp_rw [correction_eigenfunction_integral pr hW hband hgap _ hV hphase]
  simp

end PinchedHartogs.BaseConstruction

end

end OAI
