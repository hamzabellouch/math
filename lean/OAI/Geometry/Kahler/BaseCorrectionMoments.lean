import OAI.Geometry.Kahler.BaseRadialCancellation

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def adaptedMonomial (p : Sphere) (n m : ℕ) (ξ : Base) : ℂ :=
  (adaptedIsometry p ξ 0)^n*(adaptedIsometry p ξ 1)^m

lemma adaptedMonomial_continuous (p : Sphere) (n m : ℕ) : Continuous (adaptedMonomial p n m) := by
  unfold adaptedMonomial
  fun_prop

lemma adaptedMonomial_hopf (p : Sphere) (n m : ℕ) (t : unitInterval) (z : Circle × Circle) :
    adaptedMonomial p n m (adaptedHopf p t z) =
      (Real.sqrt (t:ℝ):ℂ)^n*phaseChar n z.1*(Real.sqrt (1-(t:ℝ)):ℂ)^m*phaseChar m z.2 := by
  simp only [adaptedMonomial,adaptedHopf,sphereAction_coe,LinearIsometryEquiv.apply_symm_apply,
    hopf,torusAction_zero,torusAction_one,radialSphere_zero,radialSphere_one,phaseChar,zpow_natCast,Circle.coe_pow,mul_pow]
  ring

lemma patch_cutoff_squared (k : ℕ) (R : ℝ) (t : unitInterval) :
    Real.exp (-R/k)<Real.sqrt (t:ℝ) ↔ Real.exp (-2*R/k)<(t:ℝ) := by
  have he : Real.exp (-R/k)^2=Real.exp (-2*R/k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hh := (sq_lt_sq₀ (Real.exp_pos (-R/k)).le (Real.sqrt_nonneg (t:ℝ))).symm
  rwa [he,Real.sq_sqrt t.property.1] at hh

lemma correction_torus_moment {W : Base → ℝ} (hW : Differentiable ℝ W)
    (k : ℕ) (hk : 0 < k) (R : ℝ) (f b : ℝ → ℝ) (p : Sphere)
    (s : Finset ℤ) (a : ℤ → ℂ) (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ)=phaseSum s a z)
    (hs : ∀ n ∈ s, 0 < (k:ℤ)+n) (N M : ℕ) (t : unitInterval) :
    (∫ z : Circle × Circle, adaptedMonomial p N M (adaptedHopf p t z)*
      (densityCorrection k R f b W p (adaptedHopf p t z):ℂ) ∂torusMeasure) =
    if M=0 ∧ (N:ℤ)-(k:ℤ) ∈ s then (star (a ((N:ℤ)-(k:ℤ)))/2)*
      (if Real.exp (-2*R/k)<(t:ℝ) then
        (((t:ℝ)⁻¹*(Real.sqrt (t:ℝ))^N*(f (-(k:ℝ)/2*Real.log (t:ℝ))+(1-(N:ℝ)/k)*b (-(k:ℝ)/2*Real.log (t:ℝ))) : ℝ) : ℂ) else 0)
    else 0 := by
  classical
  by_cases ht : Real.exp (-2*R/k)<(t:ℝ)
  · have ht0 : 0 < (t:ℝ) := lt_trans (Real.exp_pos _) ht
    have hcut : Real.exp (-R/k)<Real.sqrt (t:ℝ) := (patch_cutoff_squared k R t).mpr ht
    let y := -(k:ℝ)/2*Real.log (t:ℝ)
    let A : ℤ → ℂ := fun n => (((t:ℝ)⁻¹:ℝ):ℂ)*a n*((f y-(n:ℝ)/k*b y:ℝ):ℂ)
    let S : Circle → ℂ := fun z => ∑ n ∈ s, A n*phaseChar ((k:ℤ)+n) z
    have hcorr : ∀ z : Circle × Circle, densityCorrection k R f b W p (adaptedHopf p t z)=(S z.1).re := by
      intro z
      rw [densityCorrection,adaptedHopf_bracket_norm,ite_eq_left hcut]
      simpa only [S,A,y,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_natCast] using adaptedHopf_correction_expansion hW k f b p t ht0 s a he z
    have hprod : ∀ z : Circle × Circle,
        adaptedMonomial p N M (adaptedHopf p t z)*(densityCorrection k R f b W p (adaptedHopf p t z):ℂ) =
        ((Real.sqrt (t:ℝ):ℂ)^N*(Real.sqrt (1-(t:ℝ)):ℂ)^M*(phaseChar N z.1*((S z.1).re:ℂ)))*phaseChar M z.2 := by
      intro z
      rw [adaptedMonomial_hopf,hcorr]
      ring
    simp_rw [hprod]
    rw [show torusMeasure=circleMeasure.prod circleMeasure from rfl,
      integral_prod_mul (fun z : Circle => (Real.sqrt (t:ℝ):ℂ)^N*(Real.sqrt (1-(t:ℝ)):ℂ)^M*(phaseChar N z*((S z).re:ℂ))) (phaseChar M),integral_const_mul,
      phase_shifted_real_moment s A k N hs,circle_char_mean]
    rw [ite_eq_left ht]
    by_cases hM : M=0
    · subst M
      simp only [Nat.cast_zero,ite_true,pow_zero,mul_one,true_and]
      by_cases hN : (N:ℤ)-(k:ℤ) ∈ s
      · rw [ite_eq_left hN,ite_eq_left hN]
        unfold A y
        simp only [Complex.star_def,map_mul,Complex.conj_ofReal]
        push_cast
        have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
        field_simp
        ring
      · simp only [ite_eq_right hN,mul_zero]
    · have hM' : (M:ℤ) ≠ 0 := by exact_mod_cast hM
      simp only [ite_eq_right hM',mul_zero,hM,false_and,ite_false]
  · have hcut : ¬ Real.exp (-R/k)<Real.sqrt (t:ℝ) := fun h => ht ((patch_cutoff_squared k R t).mp h)
    have hz : ∀ z : Circle × Circle, densityCorrection k R f b W p (adaptedHopf p t z)=0 := by
      intro z
      simp only [densityCorrection,adaptedHopf_bracket_norm,ite_eq_right hcut]
    simp only [hz,Complex.ofReal_zero,mul_zero,integral_zero,ite_eq_right ht,ite_self]

lemma unitInterval_integral_complex (f : ℝ → ℂ) :
    (∫ t : unitInterval, f t) = ∫ t in (0:ℝ)..1, f t := by
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc f,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

lemma densityCorrection_monomial_moment {k : ℕ} (hk : 0 < k) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (hW : ContDiff ℝ ∞ W)
    {ℓ : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ<k) (p : Sphere) (N M : ℕ) :
    (∫ ξ : Sphere, adaptedMonomial p N M ξ*(densityCorrection k R f b W p ξ:ℂ) ∂sigma)=0 := by
  have hcont : Continuous (fun ξ : Sphere => adaptedMonomial p N M ξ*(densityCorrection k R f b W p ξ:ℂ)) :=
    ((adaptedMonomial_continuous p N M).comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp ((densityCorrection_smooth hk hER hf hb hW htail p).continuous.comp continuous_subtype_val))
  rw [adaptedHopf_integral hcont p]
  obtain ⟨s,a,hs,he⟩ := hband p
  have hspos : ∀ n ∈ s, 0 < (k:ℤ)+n := by
    intro n hn
    have hn' := (abs_le.mp (hs n hn)).1
    omega
  simp_rw [correction_torus_moment (hW.differentiable (by simp)) k hk R f b p s a he hspos N M]
  split_ifs with hNM
  · rw [integral_const_mul]
    rw [unitInterval_integral_complex (fun t : ℝ => if Real.exp (-2*R/k)<t then ((t⁻¹*(Real.sqrt t)^N*(f (-(k:ℝ)/2*Real.log t)+(1-(N:ℝ)/k)*b (-(k:ℝ)/2*Real.log t)):ℝ):ℂ) else 0),
      radial_profile_moment hf.continuous hb.continuous hode (by exact_mod_cast hk) hR hzero (htail R hER.le).2 N,mul_zero]
  · simp

end PinchedHartogs.BaseConstruction

end

end OAI
