import Mathlib
import OAI.Probability.JammingConcavity.CloudCountingDecomposition

namespace OAI

/-! Stable Jump Integral. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma lintegral_comp_rpow_positive_halfline (g : ℝ → ℝ≥0∞) {p : ℝ} (hp : p ≠ 0) :
    (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (|p| *x^(p-1))*g (x^p)) =
      ∫⁻ y in Set.Ioi (0:ℝ), g y := by
  have he : (fun x : ℝ => x^p) '' Set.Ioi 0 = Set.Ioi (0:ℝ) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact Real.rpow_pos_of_pos hy _
    · intro hx
      refine ⟨x^(1/p), Real.rpow_pos_of_pos hx _, ?_⟩
      change (x^(1/p))^p = x
      rw [← Real.rpow_mul (mem_Ioi.mp hx).le, one_div_mul_cancel hp, Real.rpow_one]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt)
    ((Real.rpow_left_injOn hp).mono (by intro x hx; exact (mem_Ioi.mp hx).le)) g
  rw [he] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]

lemma unscaled_jump_gamma {m q t : ℝ} (hm : 0 < m) (hq : m < q) (ht : 0 < t) :
    (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal ((x^(-1/m))^q*Real.exp (-t*x^(-1/m)))) =
      ENNReal.ofReal (m*Real.Gamma (q-m)*t^(m-q)) := by
  rw [← lintegral_comp_rpow_positive_halfline _ (neg_ne_zero.mpr hm.ne')]
  have he : (fun x : ℝ => ENNReal.ofReal (|-m| *x^(-m-1)) *
      ENNReal.ofReal (((x^(-m))^(-1/m))^q*Real.exp (-t*(x^(-m))^(-1/m))))
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun x => ENNReal.ofReal (m*(x^(q-m-1)*Real.exp (-t*x)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [← Real.rpow_mul hx.le, show -m*(-1/m) = 1 by field_simp,
      Real.rpow_one, abs_neg, abs_of_pos hm,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ m*x^(-m-1))]
    congr 1
    rw [show q-m-1 = (-m-1)+q by ring, Real.rpow_add hx]
    ring
  rw [lintegral_congr_ae he]
  have hi : IntegrableOn (fun x : ℝ => x^(q-m-1)*Real.exp (-t*x)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < q-m-1) (by norm_num : (0:ℝ)<1) ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul m) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    exact mul_nonneg hm.le (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)),
    integral_const_mul]
  have hv : (∫ x in Set.Ioi (0:ℝ), x^(q-m-1)*Real.exp (-t*x)) =
      (1/t)^(q-m)*Real.Gamma (q-m) := by
    simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi (sub_pos.mpr hq) ht
  rw [hv]
  congr 1
  rw [one_div, Real.inv_rpow ht.le, show m-q = -(q-m) by ring, Real.rpow_neg ht.le]
  ring

lemma measurable_stableJump (m c : ℝ) : Measurable (stableJump m c) := by
  unfold stableJump; fun_prop

lemma stableJump_eq_div {m c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    c^(1/m)*x^(-1/m) = (x/c)^(-1/m) := by
  rw [Real.div_rpow hx hc.le, show -1/m = -(1/m) by ring, Real.rpow_neg hc.le]
  simp only [div_inv_eq_mul]
  ring

lemma selected_jump_gamma {m c t : ℝ} (hm : 0 < m) (hc : 0 < c) (ht : 0 < t)
    (n : ℕ) (hn : m < (n:ℝ)) :
    (∫⁻ z, stableJump m c z^n * ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c z))
      ∂(volume.restrict (Set.Ioi 0)).prod (Measure.dirac ())) =
      ENNReal.ofReal (c*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))) := by
  have hmj := measurable_stableJump m c
  have hF : Measurable (fun z => stableJump m c z^n *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c z))) :=
    (hmj.pow_const n).mul
      (continuous_expNeg.measurable.comp (measurable_const.mul hmj)).ennreal_ofReal
  rw [lintegral_prod _ hF.aemeasurable]
  simp only [lintegral_dirac]
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((x^(-1/m))^(n:ℝ)*Real.exp (-t*x^(-1/m)))
  have hf : Measurable f := by unfold f; fun_prop
  have he : (fun x : ℝ => stableJump m c (x,())^n *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c (x,())))) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun x => f (x/c)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    unfold stableJump f
    rw [stableJump_eq_div hc hx.le, ← ENNReal.ofReal_mul ht.le, expNeg_ofReal (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), Real.rpow_natCast]
    simp only [neg_mul]
  rw [lintegral_congr_ae he, lintegral_Ioi_div hf hc, unscaled_jump_gamma hm hn ht,
    ← ENNReal.ofReal_mul hc.le]
  congr 1; ring
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma stableJump_exp {m x r : ℝ} (hm : m ≠ 0) :
    stableJump m (Real.exp (m*x)) (r,()) =
      ENNReal.ofReal (r^(-1/m))*ENNReal.ofReal (Real.exp x) := by
  unfold stableJump
  rw [← Real.exp_mul, show m*x*(1/m) = x by field_simp]
  rw [mul_comm (Real.exp x), ENNReal.ofReal_mul' (Real.exp_pos _).le]

lemma selected_exp_jump {m t x : ℝ} (hm : 0 < m) (ht : 0 < t)
    (n : ℕ) (hn : m < (n:ℝ)) :
    (∫⁻ r in Set.Ioi (0:ℝ), (ENNReal.ofReal (r^(-1/m))*ENNReal.ofReal (Real.exp x))^n *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*(ENNReal.ofReal (r^(-1/m))*ENNReal.ofReal (Real.exp x))))) =
      ENNReal.ofReal (m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))) * ENNReal.ofReal (Real.exp (m*x)) := by
  have hf : Measurable (fun z : ℝ × Unit => stableJump m (Real.exp (m*x)) z^n *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m (Real.exp (m*x)) z))) :=
    ((measurable_stableJump m _).pow_const n).mul
      (continuous_expNeg.measurable.comp (measurable_const.mul (measurable_stableJump m _))).ennreal_ofReal
  have hv := selected_jump_gamma hm (Real.exp_pos (m*x)) ht n hn
  rw [lintegral_prod _ hf.aemeasurable] at hv
  simp only [lintegral_dirac, stableJump_exp hm.ne'] at hv
  rw [hv, ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
  congr 1; ring

lemma tiltedChildProbability_ne_top {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} {X : A → ℝ}
    (hi : Integrable (fun a => Real.exp (m*X a)) ν) (s : Set A) :
    tiltedChildProbability ν m X s ≠ ∞ := by
  have hD : (∫⁻ a in s, ENNReal.ofReal (Real.exp (m*X a)) ∂ν) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show (∫⁻ a, ENNReal.ofReal (Real.exp (m*X a)) ∂ν) ≠ ∞ from ?_)
      (setLIntegral_le_lintegral s _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top
  exact ENNReal.div_ne_top hD (ENNReal.ofReal_ne_zero_iff.mpr (integral_exp_pos hi))

lemma selected_exp_marked_block {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (ht : 0 < t)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (n : ℕ) (hn : m < (n:ℝ)) {s : Set A} (hs : MeasurableSet s) :
    (∫⁻ z, expMarkedBlock m X n s z *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))
      ∂(volume.restrict (Set.Ioi 0)).prod ν) =
      tiltedChildProbability ν m X s *
        ENNReal.ofReal ((∫ a, Real.exp (m*X a) ∂ν)*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))) := by
  classical
  let K : ℝ := m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))
  have hf : Measurable (fun z : ℝ × A => expMarkedBlock m X n s z *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))) :=
    (measurable_expMarkedBlock m hX n hs).mul
      (continuous_expNeg.measurable.comp (measurable_const.mul (measurable_expMarkedJump m hX))).ennreal_ofReal
  rw [lintegral_prod_symm _ hf.aemeasurable]
  have he (a : A) : (∫⁻ r in Set.Ioi (0:ℝ), expMarkedBlock m X n s (r,a) *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X (r,a)))) =
      s.indicator (fun a => ENNReal.ofReal K*ENNReal.ofReal (Real.exp (m*X a))) a := by
    by_cases ha : a ∈ s
    · simp only [expMarkedBlock, Set.indicator_of_mem ha, expMarkedJump]
      exact selected_exp_jump hm ht n hn
    · simp [expMarkedBlock, ha]
  simp_rw [he]
  rw [lintegral_indicator hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hc := integral_exp_pos hi
  have hmul : ENNReal.ofReal ((∫ a, Real.exp (m*X a) ∂ν)*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))) =
      ENNReal.ofReal (∫ a, Real.exp (m*X a) ∂ν)*ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_mul hc.le]; congr 1; dsimp [K]; ring
  rw [hmul, tiltedChildProbability, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top]
  exact mul_comm _ _
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma cloud_intensity_ae_not_in {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (xs : List (ℝ × A)) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)).prod ν, z ∉ xs := by
  classical
  rw [ae_iff]
  have he : (↑xs.toFinset : Set (ℝ × A)) = {z | z ∈ xs} := by ext z; simp
  simpa only [not_not, he] using
    (xs.toFinset.finite_toSet.measure_zero ((volume.restrict (Set.Ioi 0)).prod ν))

lemma factorial_cloud_exclusions {A : Type} [MeasurableSpace A] [MeasurableEq (ℝ × A)]
    (ν : Measure A) [IsProbabilityMeasure ν] {g : ℝ × A → ℝ≥0∞} (hg : Measurable g)
    (fs : List ((ℝ × A) → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) (xs : List (ℝ × A)) :
    (∫⁻ ω, cloudLaplaceFactor g (pointCloudMeasure ω) *
      distinctCloudIntegral fs (pointCloudMeasure ω) xs ∂pointCloudLaw ν) =
    (∫⁻ ω, cloudLaplaceFactor g (pointCloudMeasure ω) ∂pointCloudLaw ν) *
    (fs.map (fun f => ∫⁻ z, f z * ENNReal.ofReal (expNeg (g z))
      ∂(volume.restrict (Set.Ioi 0)).prod ν)).prod := by
  classical
  induction fs generalizing xs with
  | nil => simp [distinctCloudIntegral]
  | cons f fs ih =>
    have hf : Measurable f := hfs f (by simp)
    have htail : ∀ h ∈ fs, Measurable h := fun h hh => hfs h (by simp [hh])
    let F : (ℝ × A) × Measure (ℝ × A) → ℝ≥0∞ := fun z =>
      if z.1 ∈ xs then 0 else
        f z.1 * cloudLaplaceFactor g z.2 * distinctCloudIntegral fs (cloudHull z.2) (z.1::xs)
    have hF : Measurable F := by
      apply Measurable.ite
      · convert (xs.toFinset.finite_toSet.measurableSet).preimage
          (measurable_fst : Measurable (Prod.fst : (ℝ × A) × Measure (ℝ × A) → ℝ × A)) using 1
        ext z; simp
      · exact measurable_const
      · exact ((hf.comp measurable_fst).mul ((measurable_cloudLaplaceFactor hg).comp measurable_snd)).mul
          (measurable_distinct_cloud_hull_cons fs htail xs)
    have hc := pointCloudCampbell A inferInstance ν inferInstance F hF
    have heL : (∫⁻ ω, cloudLaplaceFactor g (pointCloudMeasure ω) *
        distinctCloudIntegral (f::fs) (pointCloudMeasure ω) xs ∂pointCloudLaw ν) =
        ∫⁻ ω, ∫⁻ z, F (z,pointCloudMeasure ω) ∂pointCloudMeasure ω ∂pointCloudLaw ν := by
      apply lintegral_congr_ae
      filter_upwards [cloud_weightedMass_ae_finite ν] with ω hω
      unfold distinctCloudIntegral
      rw [← lintegral_const_mul' _ _ (show cloudLaplaceFactor g (pointCloudMeasure ω) ≠ ∞ from ENNReal.ofReal_ne_top)]
      apply lintegral_congr
      intro z
      dsimp [F]
      rw [cloudHull_eq _ hω]
      split_ifs
      · simp only [mul_zero]
      · ac_rfl
    rw [heL, hc]
    have heR (z : ℝ × A) :
        (∫⁻ ω, F (z,Measure.dirac z + pointCloudMeasure ω) ∂pointCloudLaw ν) =
        if z ∈ xs then 0 else (f z * ENNReal.ofReal (expNeg (g z))) *
          (∫⁻ ω, cloudLaplaceFactor g (pointCloudMeasure ω) *
            distinctCloudIntegral fs (pointCloudMeasure ω) (z::xs) ∂pointCloudLaw ν) := by
      by_cases hz : z ∈ xs
      · simp [F, hz]
      · have he : (fun ω : PointCloud A => F (z,Measure.dirac z + pointCloudMeasure ω)) =ᵐ[pointCloudLaw ν]
            (fun ω => (f z * ENNReal.ofReal (expNeg (g z))) *
              (cloudLaplaceFactor g (pointCloudMeasure ω) *
                distinctCloudIntegral fs (pointCloudMeasure ω) (z::xs))) := by
          filter_upwards [cloud_weightedMass_ae_finite ν] with ω hω
          dsimp [F]
          rw [ite_eq_right hz, cloudHull_eq _ (cloud_weightedMass_add_dirac_finite _ hω z),
            distinctCloudIntegral_add_dirac fs _ (z::xs) (by simp),
            cloudLaplaceFactor_add_dirac hg]
          ac_rfl
        rw [lintegral_congr_ae he, ite_eq_right hz]
        apply lintegral_const_mul''
        exact (((measurable_cloudLaplaceFactor hg).comp measurable_pointCloudMeasure).aemeasurable.mul
          (aemeasurable_distinct_cloud ν fs htail (z::xs)))
    simp_rw [heR, ih htail]
    have hn := cloud_intensity_ae_not_in ν xs
    rw [lintegral_congr_ae (show (fun z : ℝ × A => if z ∈ xs then 0 else
          (f z * ENNReal.ofReal (expNeg (g z))) *
            ((∫⁻ ω, cloudLaplaceFactor g (pointCloudMeasure ω) ∂pointCloudLaw ν) *
              (fs.map (fun h => ∫⁻ y, h y * ENNReal.ofReal (expNeg (g y))
                ∂(volume.restrict (Set.Ioi 0)).prod ν)).prod)) =ᵐ[(volume.restrict (Set.Ioi 0)).prod ν]
        (fun z => (f z * ENNReal.ofReal (expNeg (g z))) *
            ((∫⁻ ω, cloudLaplaceFactor g (pointCloudMeasure ω) ∂pointCloudLaw ν) *
              (fs.map (fun h => ∫⁻ y, h y * ENNReal.ofReal (expNeg (g y))
                ∂(volume.restrict (Set.Ioi 0)).prod ν)).prod)) from
      hn.mono fun z hz => ite_eq_right hz)]
    have hm : Measurable (fun z => f z * ENNReal.ofReal (expNeg (g z))) :=
      hf.mul (continuous_expNeg.measurable.comp hg).ennreal_ofReal
    rw [lintegral_mul_const _ hm]
    simp only [List.map_cons, List.prod_cons]
    ac_rfl

theorem factorialCloud : FactorialCloudStatement := by
  intro g hg fs hfs
  exact factorial_cloud_exclusions (Measure.dirac ()) hg fs hfs []
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma stable_cloudLaplaceFactor {m c t : ℝ} (ht : 0 ≤ t) (ω : PointCloud Unit)
    (hω : stableTotal m c ω ≠ ∞) :
    cloudLaplaceFactor (fun z => ENNReal.ofReal t*stableJump m c z) (pointCloudMeasure ω) =
      ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal)) := by
  unfold cloudLaplaceFactor
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← stableTotal_is_integral,
    expNeg_eq_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
  simp only [neg_mul]

lemma stable_cloudLaplaceFactor_ae {m c t : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c)
    (ht : 0 ≤ t) :
    (fun ω => cloudLaplaceFactor (fun z => ENNReal.ofReal t*stableJump m c z) (pointCloudMeasure ω))
      =ᵐ[pointCloudLaw (Measure.dirac ())]
      (fun ω => ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal))) := by
  filter_upwards [(stableTotal_properties hm hm1 hc).1] with ω hω
  exact stable_cloudLaplaceFactor ht ω hω.2.ne

lemma stable_laplace_ennreal {m c t : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c)
    (ht : 0 ≤ t) :
    (∫⁻ ω, cloudLaplaceFactor (fun z => ENNReal.ofReal t*stableJump m c z) (pointCloudMeasure ω)
      ∂pointCloudLaw (Measure.dirac ())) = ENNReal.ofReal (Real.exp (-(c*Real.Gamma (1-m))*t^m)) := by
  rw [lintegral_congr_ae (stable_cloudLaplaceFactor_ae hm hm1 hc ht),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_neg_mul _ (measurable_stableTotal m c).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg) ht) (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
    (stableTotal_properties hm hm1 hc).2 t ht]

lemma stable_factorial_laplace {m c t : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c)
    (ht : 0 ≤ t) (fs : List ((ℝ × Unit) → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal)) *
      distinctCloudIntegral fs (pointCloudMeasure ω) [] ∂pointCloudLaw (Measure.dirac ())) =
    ENNReal.ofReal (Real.exp (-(c*Real.Gamma (1-m))*t^m)) *
      (fs.map (fun f => ∫⁻ z, f z * ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c z))
        ∂(volume.restrict (Set.Ioi 0)).prod (Measure.dirac ()))).prod := by
  have he : (fun ω => ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal)) *
      distinctCloudIntegral fs (pointCloudMeasure ω) []) =ᵐ[pointCloudLaw (Measure.dirac ())]
      (fun ω => cloudLaplaceFactor (fun z => ENNReal.ofReal t*stableJump m c z) (pointCloudMeasure ω) *
        distinctCloudIntegral fs (pointCloudMeasure ω) []) :=
    (stable_cloudLaplaceFactor_ae hm hm1 hc ht).symm.mul (Filter.EventuallyEq.refl _ _)
  rw [lintegral_congr_ae he, factorial_cloud_exclusions (Measure.dirac ()) (g := fun z => ENNReal.ofReal t*stableJump m c z)
    (measurable_const.mul (measurable_stableJump m c))
    fs hfs [], stable_laplace_ennreal hm hm1 hc ht]
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

instance measurableEq_product {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableEq A] [MeasurableEq B] : MeasurableEq (A × B) where
  measurableSet_diagonal := by
    have h₁ : MeasurableSet {z : (A × B) × (A × B) | z.1.1 = z.2.1} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)
    have h₂ : MeasurableSet {z : (A × B) × (A × B) | z.1.2 = z.2.2} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
    convert h₁.inter h₂ using 1
    ext z
    simp [Set.diagonal, Prod.ext_iff]

lemma expMarked_laplaceFactor_ae {A : Type} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (ht : 0 ≤ t) :
    (fun ω => cloudLaplaceFactor (fun z => ENNReal.ofReal t*expMarkedJump m X z) (pointCloudMeasure ω))
      =ᵐ[pointCloudLaw ν] (fun ω => ENNReal.ofReal (Real.exp (-t*(expMarkedTotal m X ω).toReal))) := by
  filter_upwards [(expMarkedTotal_properties ν hm hm1 hX hi).1] with ω hω
  unfold cloudLaplaceFactor
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← expMarkedTotal_integral m hX,
    expNeg_eq_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
  simp only [neg_mul]

lemma expMarked_laplace_ennreal {A : Type} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (ht : 0 ≤ t) :
    (∫⁻ ω, cloudLaplaceFactor (fun z => ENNReal.ofReal t*expMarkedJump m X z) (pointCloudMeasure ω)
      ∂pointCloudLaw ν) =
      ENNReal.ofReal (Real.exp (-((∫ a, Real.exp (m*X a) ∂ν)*Real.Gamma (1-m))*t^m)) := by
  rw [lintegral_congr_ae (expMarked_laplaceFactor_ae ν hm hm1 hX hi ht),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_neg_mul _ (measurable_expMarkedTotal m hX).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg) ht) (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    (expMarkedTotal_properties ν hm hm1 hX hi).2 t ht]

lemma expMarked_factorial_laplace {A : Type} [MeasurableSpace A] [MeasurableEq A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (ht : 0 ≤ t) (fs : List ((ℝ × A) → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(expMarkedTotal m X ω).toReal)) *
      distinctCloudIntegral fs (pointCloudMeasure ω) [] ∂pointCloudLaw ν) =
    ENNReal.ofReal (Real.exp (-((∫ a, Real.exp (m*X a) ∂ν)*Real.Gamma (1-m))*t^m)) *
      (fs.map (fun f => ∫⁻ z, f z * ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))
        ∂(volume.restrict (Set.Ioi 0)).prod ν)).prod := by
  have he : (fun ω => ENNReal.ofReal (Real.exp (-t*(expMarkedTotal m X ω).toReal)) *
      distinctCloudIntegral fs (pointCloudMeasure ω) []) =ᵐ[pointCloudLaw ν]
      (fun ω => cloudLaplaceFactor (fun z => ENNReal.ofReal t*expMarkedJump m X z) (pointCloudMeasure ω) *
        distinctCloudIntegral fs (pointCloudMeasure ω) []) :=
    (expMarked_laplaceFactor_ae ν hm hm1 hX hi ht).symm.mul (EventuallyEq.refl _ _)
  rw [lintegral_congr_ae he, factorial_cloud_exclusions ν
    (g := fun z => ENNReal.ofReal t*expMarkedJump m X z)
    (measurable_const.mul (measurable_expMarkedJump m hX)) fs hfs [],
    expMarked_laplace_ennreal ν hm hm1 hX hi ht]

lemma expMarked_factorial_comparison {A : Type} [MeasurableSpace A] [MeasurableEq A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (ht : 0 < t) (bs : List (ℕ × Set A)) (hbs : ∀ b ∈ bs, 0 < b.1 ∧ MeasurableSet b.2) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(expMarkedTotal m X ω).toReal)) *
      distinctCloudIntegral (bs.map (fun b => expMarkedBlock m X b.1 b.2)) (pointCloudMeasure ω) []
      ∂pointCloudLaw ν) =
    (bs.map (fun b => tiltedChildProbability ν m X b.2)).prod *
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(stableTotal m (∫ a, Real.exp (m*X a) ∂ν) ω).toReal)) *
      distinctCloudIntegral ((bs.map Prod.fst).map (fun n z => stableJump m (∫ a, Real.exp (m*X a) ∂ν) z^n))
        (pointCloudMeasure ω) [] ∂pointCloudLaw (Measure.dirac ())) := by
  let c := ∫ a, Real.exp (m*X a) ∂ν
  have hc : 0 < c := integral_exp_pos hi
  have hf : ∀ f ∈ bs.map (fun b => expMarkedBlock m X b.1 b.2), Measurable f := by
    intro f hf
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hf
    exact measurable_expMarkedBlock m hX b.1 (hbs b hb).2
  have hf' : ∀ f ∈ (bs.map Prod.fst).map (fun n z => stableJump m c z^n), Measurable f := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact (measurable_stableJump m c).pow_const n
  rw [expMarked_factorial_laplace ν hm hm1 hX hi ht.le _ hf,
    stable_factorial_laplace hm hm1 hc ht.le _ hf']
  have hprod : ((bs.map (fun b => expMarkedBlock m X b.1 b.2)).map
      (fun f => ∫⁻ z, f z*ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))
        ∂(volume.restrict (Set.Ioi 0)).prod ν)).prod =
      (bs.map (fun b => tiltedChildProbability ν m X b.2)).prod *
      (((bs.map Prod.fst).map (fun n z => stableJump m c z^n)).map
        (fun f => ∫⁻ z, f z*ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c z))
          ∂(volume.restrict (Set.Ioi 0)).prod (Measure.dirac ()))).prod := by
    clear hf hf'
    simp only [List.map_map, Function.comp_def]
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have hb := hbs b (by simp)
      have hb' : m < (b.1:ℝ) := by
        have : (1:ℝ) ≤ b.1 := by exact_mod_cast hb.1
        linarith
      have htail : ∀ b ∈ bs, 0 < b.1 ∧ MeasurableSet b.2 := fun b hb => hbs b (by simp [hb])
      simp only [List.map_cons, List.prod_cons]
      rw [selected_exp_marked_block ν hm ht hX hi b.1 hb' hb.2,
        selected_jump_gamma hm hc ht b.1 hb', ih htail]
      dsimp [c]
      ac_rfl
  rw [hprod]
  dsimp [c]
  ac_rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

instance measurableEq_countableFun {I A : Type*} [Countable I] [MeasurableSpace A]
    [MeasurableEq A] : MeasurableEq (I → A) where
  measurableSet_diagonal := by
    have h : MeasurableSet (⋂ i : I, {z : (I → A) × (I → A) | z.1 i = z.2 i}) :=
      MeasurableSet.iInter fun i => measurableSet_eq_fun
        ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd)
    convert h using 1
    ext z
    simp only [Set.mem_diagonal_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact funext_iff

instance cascadeTree_measurableEq : (k : ℕ) → MeasurableEq (CascadeTree k)
  | 0 => inferInstanceAs (MeasurableEq Unit)
  | k+1 => by
    let := cascadeTree_measurableEq k
    exact inferInstanceAs (MeasurableEq (PointCloud (CascadeTree k)))

lemma replicaPatternSize_pos : ∀ (k : ℕ) (b : ReplicaPattern k),
    ValidReplicaPattern k b → 0 < replicaPatternSize k b := by
  intro k
  induction k with
  | zero => intro b hb; exact hb
  | succ k ih =>
    intro bs hb
    change bs ≠ (List.nil : List (ReplicaPattern k)) ∧ ∀ b, List.Mem b bs → ValidReplicaPattern k b at hb
    change 0 < (bs.map (replicaPatternSize k)).sum
    obtain ⟨b,bs,rfl⟩ := List.exists_cons_of_ne_nil hb.1
    have hp : 0 < replicaPatternSize k b := ih b (hb.2 b List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons]
    omega

lemma measurable_rpcPatternWeight (ms : List ℝ) (b : ReplicaPattern ms.length) :
    Measurable (rpcPatternWeight ms b) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    change Measurable (fun ω : PointCloud (CascadeTree ms.length) =>
      ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal ^
        (-(replicaPatternSize (ms.length+1) b : ℝ))) *
      distinctCloudIntegral (b.map (fun b (z : ℝ × CascadeTree ms.length) =>
        (ENNReal.ofReal (z.1^(-1/m))*cascadeTotal ms z.2)^(replicaPatternSize ms.length b) *
          rpcPatternWeight ms b z.2)) (pointCloudMeasure ω) [])
    apply Measurable.mul
    · exact ((measurable_cascadeTotal (m::ms)).ennreal_toReal.pow_const _).ennreal_ofReal
    · apply measurable_distinct_actual_cloud
      intro f hf
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
      exact (((by fun_prop : Measurable (fun z : ℝ × CascadeTree ms.length =>
        ENNReal.ofReal (z.1^(-1/m)))).mul ((measurable_cascadeTotal ms).comp measurable_snd)).pow_const _).mul
          ((ih a).comp measurable_snd)
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

instance familyCascadeTree_measurableEq {E : Type} [MeasurableSpace E] [MeasurableEq E] :
    (k : ℕ) → MeasurableEq (FamilyCascadeTree E k)
  | 0 => inferInstanceAs (MeasurableEq Unit)
  | k+1 => by
    let := familyCascadeTree_measurableEq (E := E) k
    exact inferInstanceAs (MeasurableEq (PointCloud (E × FamilyCascadeTree E k)))

lemma pointCloudFunctional_mono {A : Type} {f g : ℝ × A → ℝ≥0∞}
    (h : ∀ z, f z ≤ g z) (ω : PointCloud A) : pointCloudFunctional f ω ≤ pointCloudFunctional g ω := by
  apply ENNReal.tsum_le_tsum
  intro n
  exact Finset.sum_le_sum fun j _ => h _

variable {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]

lemma measurable_familyPathGibbs (ms : List ℝ) {u : E → ℝ} (hu : Measurable u)
    {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familyPathGibbs ms u φ z.1 z.2) := by
  induction ms with
  | nil => exact hφ.comp measurable_fst
  | cons m ms ih =>
    have hF := measurable_familyLeafTotal ms hu
    have hp : Measurable (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
        (z.1+z.2.2.1,z.2.2.2)) := by fun_prop
    have hf : Measurable (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
        ENNReal.ofReal (z.2.1^(-1/m))*familyLeafTotal ms u (z.1+z.2.2.1) z.2.2.2 *
          familyPathGibbs ms u φ (z.1+z.2.2.1) z.2.2.2) :=
      (((by fun_prop : Measurable (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
        ENNReal.ofReal (z.2.1^(-1/m)))).mul (hF.comp hp))).mul (ih.comp hp)
    exact (measurable_pointCloudFunctional_param hf).div (measurable_familyLeafTotal (m::ms) hu)

omit [MeasurableAdd₂ E] in
lemma familyPathGibbs_le_one [MeasurableAdd₂ E] (ms : List ℝ) (u : E → ℝ) {φ : E → ℝ≥0∞}
    (hφ : ∀ x, φ x ≤ 1) (x : E) (ω : FamilyCascadeTree E ms.length) :
    familyPathGibbs ms u φ x ω ≤ 1 := by
  induction ms generalizing x with
  | nil => exact hφ x
  | cons m ms ih =>
    change _ / familyLeafTotal (m::ms) u x ω ≤ 1
    apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    apply pointCloudFunctional_mono
    intro z
    simpa only [mul_one] using mul_le_mul_right (ih (x+z.2.1) z.2.2) _

lemma measurable_familyPathMean (ms : List ℝ) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) {u : E → ℝ} (hu : Measurable u)
    {φ : E → ℝ≥0∞} (hφ : Measurable φ) : Measurable (familyPathMean ms ν u φ) := by
  induction ms generalizing ν with
  | nil => exact hφ
  | cons m ms ih =>
    let := hν 0
    have hm := ih (fun j => ν (j+1)) (fun j => hν (j+1))
    have hc := ((measurable_familyEdgeMultiplier m ms ν hν hu).pow_const m).ennreal_ofReal
    have he (x : E) : familyPathMean (m::ms) ν u φ x =
        ∫⁻ a, ENNReal.ofReal ((familyEdgeMultiplier m ms ν u x a)^m)*
          familyPathMean ms (fun j => ν (j+1)) u φ (x+a) ∂ν 0 := by
      exact lintegral_withDensity_eq_lintegral_mul (ν 0)
        (hc.comp (measurable_const.prodMk measurable_id))
        (hm.comp (measurable_const.add measurable_id))
    rw [funext he]
    exact (hc.mul (hm.comp measurable_add)).lintegral_prod_right'

omit [MeasurableAdd₂ E] in
lemma decoratedTransition_probability [MeasurableAdd₂ E] (m : ℝ) (hm : m ≠ 0) (ms : List ℝ)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    (u : E → ℝ) (hi : FamilyMomentsFinite (m::ms) ν u) (x : E) :
    IsProbabilityMeasure (decoratedTransition m ms ν u x) := by
  have h := familyEdgeMultiplier_moment hm ms ν hν u hi x
  exact pointCloudTilt_probability (ν 0) m (familyEdgeMultiplier m ms ν u x)
    (fun _ => Real.exp_pos _) h.1 h.2

lemma familyPathMean_le_one (ms : List ℝ) (h01 : ∀ m ∈ ms, 0 < m)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j)) (u : E → ℝ)
    (hi : FamilyMomentsFinite ms ν u) {φ : E → ℝ≥0∞} (hφ : ∀ x, φ x ≤ 1)
    (x : E) : familyPathMean ms ν u φ x ≤ 1 := by
  induction ms generalizing ν x with
  | nil => exact hφ x
  | cons m ms ih =>
    let := decoratedTransition_probability m (ne_of_gt (h01 m (by simp))) ms ν hν u hi x
    change (∫⁻ a, familyPathMean ms (fun j => ν (j+1)) u φ (x+a) ∂_) ≤ 1
    calc
      _ ≤ ∫⁻ _ : E, 1 ∂decoratedTransition m ms ν u x := lintegral_mono fun _ =>
        ih (fun z hz => h01 z (by simp [hz])) (fun j => ν (j+1)) (fun j => hν (j+1)) hi.2 _
      _ = 1 := by simp
end MicroscopicJamming

end

end OAI
