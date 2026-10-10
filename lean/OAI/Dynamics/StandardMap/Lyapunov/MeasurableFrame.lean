import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.BoundedTempering

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma measurable_complex_mk {X : Type*} [MeasurableSpace X] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => (⟨f x,g x⟩ : ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.measurable.comp (hf.prodMk hg)

lemma measurable_wedge {X : Type*} [MeasurableSpace X] {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => wedge (f x) (g x)) :=
  ((Complex.continuous_re.measurable.comp hf).mul (Complex.continuous_im.measurable.comp hg)).sub
    ((Complex.continuous_im.measurable.comp hf).mul (Complex.continuous_re.measurable.comp hg))

lemma measurable_rankOne {X : Type*} [MeasurableSpace X] (L : ℂ →L[ℝ] ℝ)
    {v : X → ℂ} (hv : Measurable v) : Measurable (fun x => L.smulRight (v x)) :=
  ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ) L).measurable.comp hv

lemma planeCoframe_columns (s u : ℂ) (a b : ℝ) :
    planeCoframe s u a b =
      Complex.reCLM.smulRight ⟨2*a*u.im/wedge s u, -2*b*s.im/wedge s u⟩ +
      Complex.imCLM.smulRight ⟨-2*a*u.re/wedge s u, 2*b*s.re/wedge s u⟩ := by
  apply ContinuousLinearMap.ext
  intro v
  rw [planeCoframe_apply]
  apply Complex.ext <;> simp [wedge] <;> ring

lemma measurable_lyapunovFrame (k χ : ℝ) : Measurable (lyapunovFrame k χ) := by
  apply Measurable.add
  · exact measurable_rankOne _ (((measurable_const.mul (measurable_stableScale k χ)).inv).smul
      (measurable_stableVector k))
  · exact measurable_rankOne _ (((measurable_const.mul (measurable_unstableScale k χ)).inv).smul
      (measurable_unstableVector k))

lemma measurable_lyapunovCoframe (k χ : ℝ) : Measurable (lyapunovCoframe k χ) := by
  have hs := measurable_stableVector k
  have hu := measurable_unstableVector k
  have ha := measurable_stableScale k χ
  have hb := measurable_unstableScale k χ
  have hw := measurable_wedge hs hu
  have hsr := Complex.continuous_re.measurable.comp hs
  have hsi := Complex.continuous_im.measurable.comp hs
  have hur := Complex.continuous_re.measurable.comp hu
  have hui := Complex.continuous_im.measurable.comp hu
  change Measurable (fun z => planeCoframe (stableVector k z) (unstableVector k z)
    (stableScale k χ z) (unstableScale k χ z))
  simp only [planeCoframe_columns]
  exact (measurable_rankOne _ (measurable_complex_mk
    (((measurable_const.mul ha).mul hui).div hw)
    (((measurable_const.mul hb).mul hsi).div hw))).add
    (measurable_rankOne _ (measurable_complex_mk
      (((measurable_const.mul ha).mul hur).div hw)
      (((measurable_const.mul hb).mul hsr).div hw)))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TemperedControl

variable {X : Type*} [MeasurableSpace X]

def orbit (e : X ≃ᵐ X) (n : ℤ) (x : X) : X := (e.toEquiv ^ n) x
@[simp] lemma orbit_zero (e : X ≃ᵐ X) (x : X) : orbit e 0 x=x := by simp [orbit]
@[simp] lemma orbit_one (e : X ≃ᵐ X) (x : X) : orbit e 1 x=e x := by simp [orbit]
@[simp] lemma orbit_neg_one (e : X ≃ᵐ X) (x : X) : orbit e (-1) x=e.symm x := by simp [orbit]
lemma orbit_add (e : X ≃ᵐ X) (n m : ℤ) (x : X) :
    orbit e (n+m) x=orbit e n (orbit e m x) := by simp only [orbit,zpow_add,Equiv.Perm.mul_apply]
lemma orbit_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : orbit e n x=e^[n] x := by
  rw [orbit,zpow_natCast,Equiv.Perm.coe_pow]; rfl
lemma orbit_neg_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : orbit e (-n) x=e.symm^[n] x := by
  rw [orbit,zpow_neg,zpow_natCast,← inv_pow,Equiv.Perm.coe_pow]; rfl
lemma measurable_orbit (e : X ≃ᵐ X) (n : ℤ) : Measurable (orbit e n) := by
  obtain ⟨n,rfl | rfl⟩ := Int.eq_nat_or_neg n
  · change Measurable (fun x => orbit e (n : ℤ) x)
    simpa only [orbit_nat] using e.measurable.iterate n
  · change Measurable (fun x => orbit e (-(n : ℤ)) x)
    simpa only [orbit_neg_nat] using e.symm.measurable.iterate n

lemma summable_damped_of_log_rate {c : ℕ → ℝ} (hc : ∀ n, 0<c n)
    (hrate : Tendsto (fun n : ℕ => Real.log (c n)/(n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) : Summable (fun n : ℕ => c n*Real.exp (-ε*(n : ℝ))) := by
  have hgeo := summable_geometric_of_lt_one (Real.exp_pos (-ε/2)).le
    (Real.exp_lt_one_iff.mpr (by linarith : -ε/2<0))
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_order.mp hrate).2 (ε/2) (by linarith), eventually_gt_atTop 0] with n hn hn0
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn0
  have hlt := (div_lt_iff₀ hnp).mp hn
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hc n) (Real.exp_pos _))]
  calc
    _ ≤ Real.exp (ε/2*(n : ℝ))*Real.exp (-ε*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (by
        calc c n = Real.exp (Real.log (c n)) := (Real.exp_log (hc n)).symm
             _ ≤ _ := Real.exp_le_exp.mpr hlt.le) (Real.exp_pos _).le
    _ = (Real.exp (-ε/2))^n := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring

noncomputable def weight (ε : ℝ) (n : ℤ) : ℝ := Real.exp (-ε*|(n : ℝ)|)
noncomputable def control (e : X ≃ᵐ X) (c : X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  ∑' n : ℤ, c (orbit e n x)*weight ε n
noncomputable def radius (e : X ≃ᵐ X) (c : X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  (1+control e c ε x)⁻¹

lemma summable_control (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0<c x) {ε : ℝ} (hε : 0<ε)
    {x : X}
    (hf : Tendsto (fun n : ℕ => Real.log (c (e^[n] x))/(n : ℝ)) atTop (𝓝 0))
    (hb : Tendsto (fun n : ℕ => Real.log (c (e.symm^[n] x))/(n : ℝ)) atTop (𝓝 0)) :
    Summable (fun n : ℤ => c (orbit e n x)*weight ε n) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [orbit_nat,weight,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      summable_damped_of_log_rate (fun n => hc _) hf hε
  · simpa only [orbit_neg_nat,weight,Int.cast_neg,Int.cast_natCast,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using summable_damped_of_log_rate (fun n => hc _) hb hε

lemma control_nonneg (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x) (ε : ℝ) (x : X) :
    0≤control e c ε x := tsum_nonneg fun _ => mul_nonneg (hc _) (Real.exp_pos _).le
lemma control_ge (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x) (ε : ℝ) (x : X)
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) : c x≤control e c ε x := by
  have hh := hs.le_tsum 0 (fun n _ => mul_nonneg (hc _) (Real.exp_pos _).le)
  simpa only [control,orbit_zero,weight,Int.cast_zero,abs_zero,mul_zero,Real.exp_zero,mul_one] using hh

lemma weight_shift_bound {ε : ℝ} (hε : 0≤ε) (n m : ℤ) :
    weight ε n≤Real.exp (ε*|(m : ℝ)|)*weight ε (n+m) := by
  unfold weight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (abs_add_le (n : ℝ) (m : ℝ)) hε
  rw [Int.cast_add]
  linarith

lemma summable_control_orbit (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x)
    {ε : ℝ} (hε : 0≤ε) {x : X}
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) (m : ℤ) :
    Summable (fun n : ℤ => c (orbit e n (orbit e m x))*weight ε n) := by
  have hshift : Summable (fun n : ℤ => c (orbit e (n+m) x)*weight ε (n+m)) :=
    (Equiv.addRight m).summable_iff.mpr hs
  apply (hshift.mul_left (Real.exp (ε*|(m : ℝ)|))).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc _)
    (show 0≤weight ε n from (Real.exp_pos _).le)), ← orbit_add]
  calc
    _ ≤ c (orbit e (n+m) x)*(Real.exp (ε*|(m : ℝ)|)*weight ε (n+m)) :=
      mul_le_mul_of_nonneg_left (weight_shift_bound hε n m) (hc _)
    _ = _ := by ring

lemma control_orbit_le (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x)
    {ε : ℝ} (hε : 0≤ε) {x : X}
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) (m : ℤ) :
    control e c ε (orbit e m x)≤Real.exp (ε*|(m : ℝ)|)*control e c ε x := by
  have hshift : Summable (fun n : ℤ => c (orbit e (n+m) x)*weight ε (n+m)) :=
    (Equiv.addRight m).summable_iff.mpr hs
  have hle := Summable.tsum_le_tsum (fun n : ℤ => show
      c (orbit e n (orbit e m x))*weight ε n≤
        Real.exp (ε*|(m : ℝ)|)*(c (orbit e (n+m) x)*weight ε (n+m)) from by
    rw [← orbit_add]
    calc
      _ ≤ c (orbit e (n+m) x)*(Real.exp (ε*|(m : ℝ)|)*weight ε (n+m)) :=
        mul_le_mul_of_nonneg_left (weight_shift_bound hε n m) (hc _)
      _ = _ := by ring)
    (summable_control_orbit e hc hε hs m) (hshift.mul_left _)
  have heq := (Equiv.addRight m).tsum_eq (fun n : ℤ => c (orbit e n x)*weight ε n)
  change (∑' n : ℤ, c (orbit e (n+m) x)*weight ε (n+m))=control e c ε x at heq
  rw [tsum_mul_left, heq] at hle
  exact hle

lemma radius_pos (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x) (ε : ℝ) (x : X) :
    0<radius e c ε x := by
  have := control_nonneg e hc ε x
  exact inv_pos.mpr (by linarith)
lemma radius_le_one (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x) (ε : ℝ) (x : X) :
    radius e c ε x≤1 := by
  have := control_nonneg e hc ε x
  exact (inv_le_one₀ (by linarith : 0<1+control e c ε x)).mpr (by linarith)
lemma radius_mul_control_le (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x)
    (ε : ℝ) (x : X) (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) :
    radius e c ε x*c x≤1 := by
  have hh := control_ge e hc ε x hs
  have h0 := control_nonneg e hc ε x
  unfold radius
  calc
    _ ≤ (1+control e c ε x)⁻¹*(1+control e c ε x) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (by linarith))
    _ = 1 := inv_mul_cancel₀ (by linarith)

lemma radius_orbit_lower (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0≤c x)
    {ε : ℝ} (hε : 0≤ε) {x : X}
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) (m : ℤ) :
    Real.exp (-ε*|(m : ℝ)|)*radius e c ε x≤radius e c ε (orbit e m x) := by
  have hle := control_orbit_le e hc hε hs m
  have hexp : 1≤Real.exp (ε*|(m : ℝ)|) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 1+control e c ε (orbit e m x)≤Real.exp (ε*|(m : ℝ)|)*(1+control e c ε x) := by nlinarith
  have hp : 0<1+control e c ε (orbit e m x) := by have := control_nonneg e hc ε (orbit e m x); linarith
  have hh := one_div_le_one_div_of_le hp hb
  simpa only [radius, one_div, mul_inv, ← Real.exp_neg, neg_mul] using hh

lemma measurable_control (e : X ≃ᵐ X) {c : X → ℝ} (hc : Measurable c) (ε : ℝ) :
    Measurable (control e c ε) := Measurable.tsum fun n => (hc.comp (measurable_orbit e n)).mul_const _
lemma measurable_radius (e : X ≃ᵐ X) {c : X → ℝ} (hc : Measurable c) (ε : ℝ) :
    Measurable (radius e c ε) := (measurable_const.add (measurable_control e hc ε)).inv

end TemperedControl
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def diagonalPlane (α β : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (α : ℂ) + Complex.imCLM.smulRight (β*Complex.I)
lemma diagonalPlane_apply (α β : ℝ) (v : ℂ) :
    diagonalPlane α β v = ⟨α*v.re, β*v.im⟩ := by
  apply Complex.ext <;> simp [diagonalPlane] <;> ring

lemma planeFrame_normal_form (D : ℂ →L[ℝ] ℂ) {s u t v : ℂ}
    (ht : ‖t‖=1) (hv : ‖v‖=1) (hw : wedge t v≠0)
    (hs : wedge t (D s)=0) (hu : wedge v (D u)=0)
    {a b c d : ℝ} (ha : a≠0) (hb : b≠0) :
    (planeCoframe t v c d).comp (D.comp (planeFrame s u a b)) =
      diagonalPlane (dot t (D s)*c/a) (dot v (D u)*d/b) := by
  apply ContinuousLinearMap.ext
  intro x
  have he1 := unit_collinear_eq_smul ht hs
  have he2 := unit_collinear_eq_smul hv hu
  simp only [ContinuousLinearMap.comp_apply, planeFrame_apply, map_add, map_smul]
  conv_lhs => rw [he1, he2]
  simp only [planeCoframe_apply, wedge_smul_left,
    wedge_smul_right, wedge_refl, diagonalPlane_apply]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  all_goals (field_simp [ha,hb,hw]; ring)

lemma collinear_image_norm (D : ℂ →L[ℝ] ℂ) {s t : ℂ} (ht : ‖t‖=1)
    (hcov : wedge t (D s)=0) : ‖D s‖=|dot t (D s)| := by
  have he := unit_collinear_eq_smul ht hcov
  conv_lhs => rw [he, norm_smul, Real.norm_eq_abs, ht, mul_one]

lemma energy_contraction {a b ρ χ : ℝ} (ha : 0<a) (hb : 0≤b) (hr : 0≤ρ)
    (he : a^2=1+Real.exp (2*χ)*ρ^2*b^2) :
    ρ*b/a≤Real.exp (-χ) := by
  have hexp : Real.exp (2*χ)=(Real.exp χ)^2 := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hs : (Real.exp χ*ρ*b)^2≤a^2 := by rw [hexp] at he; nlinarith
  have hle : Real.exp χ*ρ*b≤a := (sq_le_sq₀ (by positivity) ha.le).mp hs
  have hmain : ρ*b≤Real.exp (-χ)*a := by
    have hh := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-χ)).le
    have hid : Real.exp (-χ)*Real.exp χ=1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = Real.exp (-χ)*(Real.exp χ*ρ*b) := by rw [← mul_assoc, ← mul_assoc, hid, one_mul]
      _ ≤ _ := hh
  exact (div_le_iff₀ ha).mpr hmain

noncomputable def stableMultiplier (k χ : ℝ) (z : Torus) : ℝ :=
  dot (stableVector k (standardMap k z)) (standardDerivative k z (stableVector k z)) *
    stableScale k χ (standardMap k z) / stableScale k χ z
noncomputable def unstableMultiplier (k χ : ℝ) (z : Torus) : ℝ :=
  dot (unstableVector k (standardMap k z)) (standardDerivative k z (unstableVector k z)) *
    unstableScale k χ (standardMap k z) / unstableScale k χ z

lemma ae_lyapunov_normal_form (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      (lyapunovCoframe k χ (standardMap k z)).comp
        ((standardDerivative k z).comp (lyapunovFrame k χ z)) =
      diagonalPlane (stableMultiplier k χ z) (unstableMultiplier k χ z) := by
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae (ae_transverseLines k hk)).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le,
    (ae_stableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    (ae_unstableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz htr hs hu
  have hp : 0<standardLyapunov k hk z := hχ.trans_lt hz
  exact planeFrame_normal_form _ (norm_stableVector k _) (norm_unstableVector k _)
    (htr (by simpa only [standardLyapunov_invariant] using hp)) (hs hp) (hu hp)
    (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z)))

lemma ae_stableMultiplier_bound (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      |stableMultiplier k χ z|≤Real.exp (-χ) := by
  have hreg := ae_stableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le,
    (ae_stableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1 hc
  have hz' : χ<standardLyapunov k hk z := hz
  have he := (h0 hz').2.2.2
  rw [← (h0 hz').2.2.1,
    ← (h1 (by simpa only [standardLyapunov_invariant] using hz')).2.2.1] at he
  have ha := zero_lt_one.trans_le (stableScale_ge_one k χ z)
  have hb := zero_lt_one.trans_le (stableScale_ge_one k χ (standardMap k z))
  have hn := collinear_image_norm (standardDerivative k z) (norm_stableVector k _) (hc (hχ.trans_lt hz'))
  simpa only [stableMultiplier, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, ← hn] using
    energy_contraction ha hb.le (norm_nonneg _) he

lemma covariant_inverse_norm_product (D E : ℂ →L[ℝ] ℂ) (hDE : ∀ x, E (D x)=x)
    {s t : ℂ} (hs : ‖s‖=1) (ht : ‖t‖=1) (hcov : wedge t (D s)=0) :
    ‖D s‖*‖E t‖=1 := by
  have he := unit_collinear_eq_smul ht hcov
  have hn := collinear_image_norm D ht hcov
  calc
    _ = ‖E (D s)‖ := by conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs, ← hn]
    _ = 1 := by rw [hDE,hs]

lemma ae_unstableMultiplier_bound (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Real.exp χ≤|unstableMultiplier k χ z| := by
  have hreg := ae_unstableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le,
    (ae_unstableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1 hc
  have hz' : χ<standardLyapunov k hk z := hz
  have hnext : χ<standardLyapunov k hk (standardMap k z) := by simpa only [standardLyapunov_invariant] using hz'
  have he := (h1 hnext).2.2.2
  rw [inverseMap_standardMap, ← (h0 hz').2.2.1, ← (h1 hnext).2.2.1] at he
  have ha := zero_lt_one.trans_le (unstableScale_ge_one k χ (standardMap k z))
  have hb := zero_lt_one.trans_le (unstableScale_ge_one k χ z)
  have hcon := energy_contraction ha hb.le (norm_nonneg _) he
  have hn := collinear_image_norm (standardDerivative k z) (norm_unstableVector k _) (hc (hχ.trans_lt hz'))
  have hprod := covariant_inverse_norm_product (standardDerivative k z)
    (standardInverseDerivative k (standardMap k z)) (standardInverseDerivative_standardDerivative k z)
    (norm_unstableVector k _) (norm_unstableVector k _) (hc (hχ.trans_lt hz'))
  have hh := mul_le_mul_of_nonneg_left hcon (norm_nonneg (standardDerivative k z (unstableVector k z)))
  have hbasic : unstableScale k χ z / unstableScale k χ (standardMap k z) ≤
      ‖standardDerivative k z (unstableVector k z)‖*Real.exp (-χ) := by
    simpa only [← mul_div_assoc, ← mul_assoc, hprod, one_mul] using hh
  have hexp : Real.exp χ*Real.exp (-χ)=1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hh' := mul_le_mul_of_nonneg_left ((div_le_iff₀ ha).mp hbasic) (Real.exp_pos χ).le
  have hfinal : Real.exp χ*unstableScale k χ z ≤
      ‖standardDerivative k z (unstableVector k z)‖*unstableScale k χ (standardMap k z) := by
    calc
      _ ≤ Real.exp χ*(‖standardDerivative k z (unstableVector k z)‖*Real.exp (-χ)*unstableScale k χ (standardMap k z)) := hh'
      _ = (Real.exp χ*Real.exp (-χ))*(‖standardDerivative k z (unstableVector k z)‖*unstableScale k χ (standardMap k z)) := by ring
      _ = _ := by rw [hexp,one_mul]
  simpa only [unstableMultiplier, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, ← hn] using
    (le_div_iff₀ hb).mpr hfinal

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

@[simp] lemma standardMap_measurableEquiv_apply (k : ℝ) (z : Torus) :
    standardMap_measurableEquiv k z=standardMap k z := rfl
@[simp] lemma standardMap_measurableEquiv_symm_apply (k : ℝ) (z : Torus) :
    (standardMap_measurableEquiv k).symm z=inverseMap k z := rfl

lemma log_max_one_rate {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (max 1 (a n))/(n : ℝ)) atTop (𝓝 0) := by
  have hlim := ha.abs
  rw [abs_zero] at hlim
  apply squeeze_zero (fun n => div_nonneg (Real.log_nonneg (le_max_left _ _)) (Nat.cast_nonneg n))
    (fun n => show Real.log (max 1 (a n))/(n : ℝ)≤|Real.log (a n)/(n : ℝ)| from ?_) hlim
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  by_cases hh : 1≤a n
  · rw [max_eq_right hh]
    exact le_abs_self _
  · rw [max_eq_left (not_le.mp hh).le,Real.log_one]
    exact abs_nonneg _

noncomputable def chartControl (k χ : ℝ) (z : Torus) : ℝ := max 1 ‖lyapunovCoframe k χ z‖
noncomputable def chartRadius (k χ ε : ℝ) : Torus → ℝ :=
  TemperedControl.radius (standardMap_measurableEquiv k) (chartControl k χ) ε
lemma chartControl_ge_one (k χ : ℝ) (z : Torus) : 1≤chartControl k χ z := le_max_left _ _
lemma measurable_chartControl (k χ : ℝ) : Measurable (chartControl k χ) :=
  measurable_const.max (measurable_lyapunovCoframe k χ).norm
lemma measurable_chartRadius (k χ ε : ℝ) : Measurable (chartRadius k χ ε) :=
  TemperedControl.measurable_radius _ (measurable_chartControl k χ) ε
lemma chartRadius_pos (k χ ε : ℝ) (z : Torus) : 0<chartRadius k χ ε z :=
  TemperedControl.radius_pos _ (fun z => zero_le_one.trans (chartControl_ge_one k χ z)) ε z
lemma chartRadius_le_one (k χ ε : ℝ) (z : Torus) : chartRadius k χ ε z≤1 :=
  TemperedControl.radius_le_one _ (fun z => zero_le_one.trans (chartControl_ge_one k χ z)) ε z

lemma ae_chartControl_summable (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) (ε : ℝ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Summable (fun n : ℤ => chartControl k χ (TemperedControl.orbit (standardMap_measurableEquiv k) n z)*
        TemperedControl.weight ε n) := by
  filter_upwards [ae_lyapunovCoframe_tempered k hk χ hχ] with z hz
  exact TemperedControl.summable_control _
    (fun z => zero_lt_one.trans_le (chartControl_ge_one k χ z)) hε
    (log_max_one_rate hz.1) (log_max_one_rate hz.2)

theorem ae_chartRadius_control (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) (ε : ℝ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      chartRadius k χ ε z*‖lyapunovCoframe k χ z‖≤1 ∧
      Real.exp (-ε)*chartRadius k χ ε z≤chartRadius k χ ε (standardMap k z) ∧
      Real.exp (-ε)*chartRadius k χ ε (standardMap k z)≤chartRadius k χ ε z := by
  filter_upwards [ae_chartControl_summable k hk χ hχ ε hε] with z hz
  have hc : ∀ z, 0≤chartControl k χ z := fun z => zero_le_one.trans (chartControl_ge_one k χ z)
  have hs := TemperedControl.summable_control_orbit (standardMap_measurableEquiv k) hc hε.le hz 1
  have h0 := TemperedControl.radius_mul_control_le (standardMap_measurableEquiv k) hc ε z hz
  have h1 := TemperedControl.radius_orbit_lower (standardMap_measurableEquiv k) hc hε.le hz 1
  have h2 := TemperedControl.radius_orbit_lower (standardMap_measurableEquiv k) hc hε.le hs (-1)
  refine ⟨?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (chartRadius_pos k χ ε z).le).trans h0
  · simpa only [chartRadius,Int.cast_one,abs_one,mul_one,TemperedControl.orbit_one,
      standardMap_measurableEquiv_apply] using h1
  · simpa only [chartRadius,TemperedControl.orbit_neg_one,TemperedControl.orbit_one,
      standardMap_measurableEquiv_apply, standardMap_measurableEquiv_symm_apply, inverseMap_standardMap,
      Int.cast_neg,Int.cast_one,abs_neg,abs_one,mul_one] using h2

end StandardMapEntropy

end
end

end OAI
