import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.TransverseLines

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {T : X → X}

noncomputable def observationCocycle (g : X → ℝ) (hT : Measurable T) (hg : Measurable g)
    (h0 : ∀ x, 0≤g x) (h1 : ∀ x, g x≤1) : Cocycle X T where
  value := birkhoffSum T g
  measurable n := Finset.measurable_sum _ (fun i _ => hg.comp (hT.iterate i))
  nonneg n x := Finset.sum_nonneg fun i _ => h0 _
  le_time n x := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 _
      _ = n := by simp
  subadd m n x := (birkhoffSum_add_right_apply T g m n x).le
  shift_bound n x := by
    rw [birkhoffSum_apply_sub_birkhoffSum]
    exact abs_le.mpr ⟨by linarith [h0 (T^[n] x), h1 x], by linarith [h1 (T^[n] x), h0 x]⟩

lemma ae_exists_bounded_average_limit {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0<C) (hbound : ∀ x, |g x|≤C) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 l) := by
  let r : X → ℝ := fun x => (g x+C)/(2*C)
  have hr : Measurable r := (hg.add_const C).div_const _
  have hr0 (x) : 0≤r x := div_nonneg (by have := (abs_le.mp (hbound x)).1; linarith) (by positivity)
  have hr1 (x) : r x≤1 := by
    apply (div_le_iff₀ (show 0<2*C by positivity)).mpr
    have := (abs_le.mp (hbound x)).2
    linarith
  let f := observationCocycle r hT.measurable hr hr0 hr1
  have he (n : ℕ) (x : X) : birkhoffSum T g n x =
      2*C*birkhoffSum T r n x-(n : ℝ)*C := by
    have hpoint (y : X) : g y=2*C*r y-C := by dsimp only [r]; field_simp; ring
    unfold birkhoffSum
    calc
      _ = ∑ i ∈ Finset.range n, (2*C*r (T^[i] x)-C) := Finset.sum_congr rfl fun i _ => hpoint _
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
  filter_upwards [f.ae_tendsto_average hT] with x hx
  refine ⟨2*C*f.lowerRate x-C, ?_⟩
  have hh := (hx.const_mul (2*C)).sub_const C
  apply hh.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  change 2*C*(birkhoffSum T r n x/(n : ℝ))-C = birkhoffSum T g n x/(n : ℝ)
  rw [he]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem ae_nonnegative_coboundary_tempered {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {u : X → ℝ} (hu : Measurable u) (h0 : ∀ x, 0≤u x)
    {C : ℝ} (hC : 0<C) (hstep : ∀ᵐ x ∂μ, |u (T x)-u x|≤C) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => u (T^[n] x)/(n : ℝ)) atTop (𝓝 0) := by
  let g : X → ℝ := fun x => max (-C) (min C (u (T x)-u x))
  have hg : Measurable g := measurable_const.max
    (measurable_const.min ((hu.comp hT.measurable).sub hu))
  have hbound (x : X) : |g x|≤C := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have heq : ∀ᵐ x ∂μ, g x=u (T x)-u x := by
    filter_upwards [hstep] with x hx
    dsimp only [g]
    rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]
  have htel : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T g n x=u (T^[n] x)-u x := by
    filter_upwards [ae_all_iff.mpr (fun n : ℕ => (hT.iterate n).quasiMeasurePreserving.ae heq)] with x hx
    intro n
    induction n with
    | zero => simp only [birkhoffSum_zero_apply, Function.iterate_zero_apply, sub_self]
    | succ n ih =>
      rw [birkhoffSum_succ_apply, ih, hx n, Function.iterate_succ_apply']
      ring
  have hrec : ∀ᵐ x ∂μ, ∀ N : ℕ, u x≤N → ∃ᶠ n : ℕ in atTop, u (T^[n] x)≤N := by
    exact ae_all_iff.mpr fun N => hT.conservative.ae_mem_imp_frequently_image_mem
      (measurableSet_le hu measurable_const).nullMeasurableSet
  filter_upwards [ae_exists_bounded_average_limit hT hg hC hbound, htel, hrec] with x hx ht hr
  obtain ⟨l,hl⟩ := hx
  have hlim : Tendsto (fun n : ℕ => u (T^[n] x)/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => u x/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [ht, sub_div, sub_add_cancel, add_zero] using hl.add hc
  have hl0 : 0≤l := ge_of_tendsto hlim (Eventually.of_forall fun n => div_nonneg (h0 _) (Nat.cast_nonneg _))
  obtain ⟨N,hN⟩ := exists_nat_ge (u x)
  have hreturn := hr N hN
  have hnlim : Tendsto (fun n : ℕ => (N : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl1 : l≤0 := le_of_tendsto_of_tendsto_of_frequently hlim hnlim
    (hreturn.mono fun n hn => div_le_div_of_nonneg_right hn (Nat.cast_nonneg _))
  have he : l=0 := le_antisymm hl1 hl0
  rwa [he] at hlim

end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) : Set Torus :=
  {z | χ < standardLyapunov k hk z}
lemma measurableSet_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurableSet (spectralGapRegion k hk χ) :=
  measurableSet_lt measurable_const (measurable_standardLyapunov k hk)
lemma preimage_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    standardMap k ⁻¹' spectralGapRegion k hk χ = spectralGapRegion k hk χ := by
  ext z
  simp only [spectralGapRegion, mem_preimage, mem_ofPred_eq, standardLyapunov_invariant]
lemma preimage_inverse_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    inverseMap k ⁻¹' spectralGapRegion k hk χ = spectralGapRegion k hk χ := by
  ext z
  simp only [spectralGapRegion, mem_preimage, mem_ofPred_eq, standardLyapunov_inverse]
lemma measurePreserving_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurePreserving (standardMap k) (area.restrict (spectralGapRegion k hk χ))
      (area.restrict (spectralGapRegion k hk χ)) := by
  have hh := (measurePreserving_standardMap k).restrict_preimage (measurableSet_spectralGapRegion k hk χ)
  rwa [preimage_spectralGapRegion] at hh
lemma measurePreserving_inverse_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurePreserving (inverseMap k) (area.restrict (spectralGapRegion k hk χ))
      (area.restrict (spectralGapRegion k hk χ)) := by
  have hh := (measurePreserving_inverseMap k).restrict_preimage (measurableSet_spectralGapRegion k hk χ)
  rwa [preimage_inverse_spectralGapRegion] at hh

lemma unit_image_bounds (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {K : ℝ} (hbound : ‖A‖≤K) {v : ℂ} (hv : ‖v‖=1) :
    ‖A v‖≤K ∧ 1≤K*‖A v‖ := by
  constructor
  · calc ‖A v‖ ≤ ‖A‖ := by simpa only [hv, mul_one] using A.le_opNorm v
         _ ≤ K := hbound
  · calc 1 ≤ ‖A‖*‖A v‖ := by simpa only [hv] using hA.norm_lower v
         _ ≤ K*‖A v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

lemma positive_energy_ratio_bounds {a b ρ K t : ℝ}
    (ha : 1≤a) (hb : 1≤b) (hρ : 0≤ρ) (hK : 1≤K) (ht : 1≤t)
    (hu : ρ≤K) (hl : 1≤K*ρ) (he : a=1+t*ρ^2*b) :
    a≤(1+t*K^2+K^2)*b ∧ b≤(1+t*K^2+K^2)*a := by
  have hb0 : 0≤b := zero_le_one.trans hb
  have ha0 : 0≤a := zero_le_one.trans ha
  have hK0 : 0≤K := zero_le_one.trans hK
  have ht0 : 0≤t := zero_le_one.trans ht
  have hρK : ρ^2≤K^2 := (sq_le_sq₀ hρ hK0).mpr hu
  have hprod : 1≤K^2*ρ^2 := by nlinarith [sq_nonneg (K*ρ-1)]
  have hmain : ρ^2*b≤a := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg ρ) hb0)]
  constructor
  · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρK ht0) hb0
    nlinarith [mul_nonneg (sq_nonneg K) hb0]
  · have hh := mul_le_mul_of_nonneg_right hprod hb0
    have hh' := mul_le_mul_of_nonneg_left hmain (sq_nonneg K)
    have hp := mul_nonneg (show 0≤1+t*K^2 by positivity) ha0
    nlinarith

lemma log_ratio_bound {a b R : ℝ} (ha : 0<a) (hb : 0<b) (hR : 0<R)
    (hab : a≤R*b) (hba : b≤R*a) : |Real.log b-Real.log a|≤Real.log R := by
  have h1 := Real.log_le_log ha hab
  have h2 := Real.log_le_log hb hba
  rw [Real.log_mul hR.ne' hb.ne'] at h1
  rw [Real.log_mul hR.ne' ha.ne'] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma ae_both_coboundary_tempered {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {T S : X → X}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hTS : ∀ x, T (S x)=x) {u : X → ℝ} (hu : Measurable u) (h0 : ∀ x, 0≤u x)
    {C : ℝ} (hC : 0<C) (hstep : ∀ᵐ x ∂μ, |u (T x)-u x|≤C) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => u (T^[n] x)/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => u (S^[n] x)/(n : ℝ)) atTop (𝓝 0) := by
  have hstep' : ∀ᵐ x ∂μ, |u (S x)-u x|≤C := by
    filter_upwards [hS.quasiMeasurePreserving.ae hstep] with x hx
    rwa [hTS, abs_sub_comm] at hx
  exact (BoundedSubadditive.ae_nonnegative_coboundary_tempered hT hu h0 hC hstep).and
    (BoundedSubadditive.ae_nonnegative_coboundary_tempered hS hu h0 hC hstep')

noncomputable def energyRatioBound (k χ : ℝ) : ℝ :=
  1+Real.exp (2*χ)*(9*growthBase k)^2+(9*growthBase k)^2
lemma energyRatioBound_ge_one (k χ : ℝ) : 1≤energyRatioBound k χ := by
  unfold energyRatioBound
  have hh : 0 ≤ Real.exp (2*χ)*(9*growthBase k)^2 := by positivity
  nlinarith [sq_nonneg (9*growthBase k)]

lemma ae_stableEnergy_log_increment (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      |Real.log (max 1 (stableEnergy k χ (standardMap k z)))-
        Real.log (max 1 (stableEnergy k χ z))| ≤ Real.log (energyRatioBound k χ) := by
  have hreg := ae_stableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1
  have hz' : χ < standardLyapunov k hk z := hz
  have ha := (h0 hz').2.1
  have hb := (h1 (by simpa only [standardLyapunov_invariant] using hz')).2.1
  have hi := unit_image_bounds _ (standardDerivative_area k z) (standardDerivative_norm_bound k hk z)
    (norm_stableVector k z)
  have hrat := positive_energy_ratio_bounds ha hb (norm_nonneg _)
    (show 1≤9*growthBase k by have := growthBase_ge_four k hk; linarith)
    (Real.one_le_exp_iff.mpr (by linarith : 0≤2*χ)) hi.1 hi.2 (h0 hz').2.2.2
  rw [max_eq_right ha, max_eq_right hb]
  exact log_ratio_bound (zero_lt_one.trans_le ha) (zero_lt_one.trans_le hb)
    (zero_lt_one.trans_le (energyRatioBound_ge_one k χ)) hrat.1 hrat.2

lemma ae_unstableEnergy_log_increment (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      |Real.log (max 1 (unstableEnergy k χ (inverseMap k z)))-
        Real.log (max 1 (unstableEnergy k χ z))| ≤ Real.log (energyRatioBound k χ) := by
  have hreg := ae_unstableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_inverseMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1
  have hz' : χ < standardLyapunov k hk z := hz
  have ha := (h0 hz').2.1
  have hb := (h1 (by simpa only [standardLyapunov_inverse] using hz')).2.1
  have hi := unit_image_bounds _ (standardInverseDerivative_area k z) (standardInverseDerivative_norm_bound k hk z)
    (norm_unstableVector k z)
  have hrat := positive_energy_ratio_bounds ha hb (norm_nonneg _)
    (show 1≤9*growthBase k by have := growthBase_ge_four k hk; linarith)
    (Real.one_le_exp_iff.mpr (by linarith : 0≤2*χ)) hi.1 hi.2 (h0 hz').2.2.2
  rw [max_eq_right ha, max_eq_right hb]
  exact log_ratio_bound (zero_lt_one.trans_le ha) (zero_lt_one.trans_le hb)
    (zero_lt_one.trans_le (energyRatioBound_ge_one k χ)) hrat.1 hrat.2

lemma log_stableScale (k χ : ℝ) (z : Torus) :
    Real.log (stableScale k χ z)=Real.log (max 1 (stableEnergy k χ z))/2 :=
  Real.log_sqrt (zero_le_one.trans (le_max_left _ _))
lemma log_unstableScale (k χ : ℝ) (z : Torus) :
    Real.log (unstableScale k χ z)=Real.log (max 1 (unstableEnergy k χ z))/2 :=
  Real.log_sqrt (zero_le_one.trans (le_max_left _ _))

theorem ae_lyapunovScale_tempered (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Tendsto (fun n : ℕ => Real.log (stableScale k χ ((standardMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (stableScale k χ ((inverseMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (unstableScale k χ ((standardMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (unstableScale k χ ((inverseMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) := by
  have hC : 0<Real.log (energyRatioBound k χ)+1 := by
    have := Real.log_nonneg (energyRatioBound_ge_one k χ)
    linarith
  have hs := ae_both_coboundary_tempered
    (measurePreserving_spectralGapRegion k hk χ) (measurePreserving_inverse_spectralGapRegion k hk χ)
    (standardMap_inverseMap k)
    ((measurable_const.max (measurable_stableEnergy k χ)).log)
    (fun z => Real.log_nonneg (le_max_left _ _)) hC
    ((ae_stableEnergy_log_increment k hk χ hχ).mono fun z hz => hz.trans (by linarith))
  have hu := ae_both_coboundary_tempered
    (measurePreserving_inverse_spectralGapRegion k hk χ) (measurePreserving_spectralGapRegion k hk χ)
    (inverseMap_standardMap k)
    ((measurable_const.max (measurable_unstableEnergy k χ)).log)
    (fun z => Real.log_nonneg (le_max_left _ _)) hC
    ((ae_unstableEnergy_log_increment k hk χ hχ).mono fun z hz => hz.trans (by linarith))
  filter_upwards [hs,hu] with z hz hw
  have hdiv {f : ℕ → ℝ} (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)) atTop (𝓝 0)) :
      Tendsto (fun n : ℕ => f n/2/(n : ℝ)) atTop (𝓝 0) := by
    have hh := hf.div_const 2
    rw [zero_div] at hh
    convert hh using 1
    funext n
    ring
  exact ⟨by simpa only [log_stableScale] using hdiv hz.1,
    by simpa only [log_stableScale] using hdiv hz.2,
    by simpa only [log_unstableScale] using hdiv hw.2,
    by simpa only [log_unstableScale] using hdiv hw.1⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def planeFrame (s u : ℂ) (a b : ℝ) : ℂ →L[ℝ] ℂ :=
  (Complex.reCLM.smulRight ((2*a)⁻¹ • s)) +
    (Complex.imCLM.smulRight ((2*b)⁻¹ • u))

lemma planeFrame_apply (s u v : ℂ) (a b : ℝ) :
    planeFrame s u a b v = (v.re/(2*a)) • s + (v.im/(2*b)) • u := by
  simp only [planeFrame, add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_smul, div_eq_mul_inv]

noncomputable def planeCoframe (s u : ℂ) (a b : ℝ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨2*a*wedge v u / wedge s u, 2*b*wedge s v / wedge s u⟩
      map_add' := by intro v w; apply Complex.ext <;> simp [wedge] <;> ring
      map_smul' := by intro t v; apply Complex.ext <;> simp [wedge] <;> ring }

lemma planeCoframe_apply (s u v : ℂ) (a b : ℝ) :
    planeCoframe s u a b v = ⟨2*a*wedge v u / wedge s u, 2*b*wedge s v / wedge s u⟩ := rfl

lemma planeCoframe_frame (s u : ℂ) {a b : ℝ} (ha : a≠0) (hb : b≠0)
    (hw : wedge s u≠0) :
    (planeCoframe s u a b).comp (planeFrame s u a b)=ContinuousLinearMap.id ℝ ℂ := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, planeCoframe_apply,
    planeFrame_apply, wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right,
    wedge_refl]
  apply Complex.ext <;> dsimp only
  all_goals (field_simp [ha,hb,hw]; ring)

lemma planeFrame_coframe (s u : ℂ) {a b : ℝ} (ha : a≠0) (hb : b≠0)
    (hw : wedge s u≠0) :
    (planeFrame s u a b).comp (planeCoframe s u a b)=ContinuousLinearMap.id ℝ ℂ := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, planeCoframe_apply,
    planeFrame_apply]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  all_goals field_simp [ha,hb,hw]; dsimp only [wedge]; ring

lemma planeFrame_norm_le {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) : ‖planeFrame s u a b‖≤1 := by
  have ha0 : 0<a := zero_lt_one.trans_le ha
  have hb0 : 0<b := zero_lt_one.trans_le hb
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [planeFrame_apply, one_mul]
  calc
    _ ≤ ‖(v.re/(2*a))•s‖+‖(v.im/(2*b))•u‖ := norm_add_le _ _
    _ = |v.re|/(2*a)+|v.im|/(2*b) := by
      rw [norm_smul, norm_smul, hs, hu, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_div, abs_div, abs_of_pos (by positivity : 0<2*a),
        abs_of_pos (by positivity : 0<2*b), mul_one, mul_one]
    _ ≤ ‖v‖/2+‖v‖/2 := add_le_add
      (le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm v) (by positivity))
        (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)))
      (le_trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm v) (by positivity))
        (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)))
    _ = ‖v‖ := by ring

lemma planeCoframe_norm_le {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) (hw : wedge s u≠0) :
    ‖planeCoframe s u a b‖≤4*a*b/|wedge s u| := by
  have ha0 : 0≤a := zero_le_one.trans ha
  have hb0 : 0≤b := zero_le_one.trans hb
  have hw0 : 0 < |wedge s u| := abs_pos.mpr hw
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h1 : |wedge v u|≤‖v‖ := by simpa only [hu,mul_one] using abs_wedge_le_norm_mul v u
  have h2 : |wedge s v|≤‖v‖ := by simpa only [hs,one_mul] using abs_wedge_le_norm_mul s v
  have hab : a+b≤2*a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  calc
    _ ≤ |(planeCoframe s u a b v).re|+|(planeCoframe s u a b v).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (2*a*|wedge v u|+2*b*|wedge s v|)/|wedge s u| := by
      simp only [planeCoframe_apply, abs_div, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0,
        abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      ring
    _ ≤ (2*a*‖v‖+2*b*‖v‖)/|wedge s u| :=
      div_le_div_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))) hw0.le
    _ ≤ 4*a*b/|wedge s u| * ‖v‖ := by
      have hh := mul_le_mul_of_nonneg_right hab (by positivity : 0≤2*‖v‖)
      have hh' := div_le_div_of_nonneg_right hh hw0.le
      calc
        _ = ((a+b)*(2*‖v‖))/|wedge s u| := by ring
        _ ≤ ((2*a*b)*(2*‖v‖))/|wedge s u| := hh'
        _ = _ := by ring

noncomputable def lyapunovFrame (k χ : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  planeFrame (stableVector k z) (unstableVector k z) (stableScale k χ z) (unstableScale k χ z)
noncomputable def lyapunovCoframe (k χ : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  planeCoframe (stableVector k z) (unstableVector k z) (stableScale k χ z) (unstableScale k χ z)

lemma lyapunovFrame_norm_le (k χ : ℝ) (z : Torus) : ‖lyapunovFrame k χ z‖≤1 :=
  planeFrame_norm_le (norm_stableVector k z) (norm_unstableVector k z)
    (stableScale_ge_one k χ z) (unstableScale_ge_one k χ z)

lemma lyapunovCoframe_frame (k χ : ℝ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) :
    (lyapunovCoframe k χ z).comp (lyapunovFrame k χ z)=ContinuousLinearMap.id ℝ ℂ :=
  planeCoframe_frame _ _ (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z))) hw
lemma lyapunovFrame_coframe (k χ : ℝ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) :
    (lyapunovFrame k χ z).comp (lyapunovCoframe k χ z)=ContinuousLinearMap.id ℝ ℂ :=
  planeFrame_coframe _ _ (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z))) hw

lemma planeCoframe_norm_ge_one {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) (hw : wedge s u≠0) :
    1≤‖planeCoframe s u a b‖ := by
  have hh := (planeCoframe s u a b).opNorm_comp_le (planeFrame s u a b)
  rw [planeCoframe_frame s u (ne_of_gt (zero_lt_one.trans_le ha))
    (ne_of_gt (zero_lt_one.trans_le hb)) hw, ContinuousLinearMap.norm_id] at hh
  apply hh.trans
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left
    (planeFrame_norm_le hs hu ha hb) (norm_nonneg (planeCoframe s u a b)))

lemma planeCoframe_log_bound {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) (hw : wedge s u≠0) :
    0≤Real.log ‖planeCoframe s u a b‖ ∧
      Real.log ‖planeCoframe s u a b‖≤Real.log 4+Real.log a+Real.log b-Real.log |wedge s u| := by
  have hh := planeCoframe_norm_ge_one hs hu ha hb hw
  refine ⟨Real.log_nonneg hh, ?_⟩
  have hle := Real.log_le_log (zero_lt_one.trans_le hh) (planeCoframe_norm_le hs hu ha hb hw)
  have ha0 : a≠0 := ne_of_gt (zero_lt_one.trans_le ha)
  have hb0 : b≠0 := ne_of_gt (zero_lt_one.trans_le hb)
  rwa [Real.log_div (by positivity) (abs_ne_zero.mpr hw),
    Real.log_mul (mul_ne_zero (by norm_num) ha0) hb0, Real.log_mul (by norm_num) ha0] at hle

lemma coframe_tempered {s u : ℕ → ℂ} {a b : ℕ → ℝ}
    (hs : ∀ n, ‖s n‖=1) (hu : ∀ n, ‖u n‖=1)
    (ha : ∀ n, 1≤a n) (hb : ∀ n, 1≤b n) (hw : ∀ n, wedge (s n) (u n)≠0)
    (hta : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ)) atTop (𝓝 0))
    (htb : Tendsto (fun n : ℕ => Real.log (b n)/(n : ℝ)) atTop (𝓝 0))
    (htw : Tendsto (fun n : ℕ => Real.log |wedge (s n) (u n)|/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log ‖planeCoframe (s n) (u n) (a n) (b n)‖/(n : ℝ)) atTop (𝓝 0) := by
  have hcon : Tendsto (fun n : ℕ => Real.log 4/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := ((hcon.add hta).add htb).sub htw
  simp only [zero_add, zero_sub, neg_zero] at hlim
  apply squeeze_zero (fun n => div_nonneg (planeCoframe_log_bound (hs n) (hu n) (ha n) (hb n) (hw n)).1 (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right (planeCoframe_log_bound (hs n) (hu n) (ha n) (hb n) (hw n)).2 (Nat.cast_nonneg n))
  convert hlim using 1
  funext n
  ring

theorem ae_lyapunovCoframe_tempered (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Tendsto (fun n : ℕ => Real.log ‖lyapunovCoframe k χ ((standardMap k)^[n] z)‖/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log ‖lyapunovCoframe k χ ((inverseMap k)^[n] z)‖/(n : ℝ)) atTop (𝓝 0) := by
  have hf : ∀ᵐ z ∂area, ∀ n : ℕ, 0<standardLyapunov k hk z →
      wedge (stableVector k ((standardMap k)^[n] z)) (unstableVector k ((standardMap k)^[n] z))≠0 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [((measurePreserving_standardMap k).iterate n).quasiMeasurePreserving.ae
      (ae_transverseLines k hk)] with z hz hp
    exact hz (by simpa only [standardLyapunov_iterate] using hp)
  have hb : ∀ᵐ z ∂area, ∀ n : ℕ, 0<standardLyapunov k hk z →
      wedge (stableVector k ((inverseMap k)^[n] z)) (unstableVector k ((inverseMap k)^[n] z))≠0 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [((measurePreserving_inverseMap k).iterate n).quasiMeasurePreserving.ae
      (ae_transverseLines k hk)] with z hz hp
    exact hz (by simpa only [standardLyapunov_inverse_iterate] using hp)
  filter_upwards [ae_lyapunovScale_tempered k hk χ hχ,
    hf.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    hb.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    (ae_angle_tempered k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ae_restrict_mem (measurableSet_spectralGapRegion k hk χ)] with z hz hf hb hw hp
  have hpos : 0<standardLyapunov k hk z := hχ.trans_lt hp
  constructor
  · exact coframe_tempered (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => stableScale_ge_one k χ _) (fun n => unstableScale_ge_one k χ _)
      (fun n => hf n hpos) hz.1 hz.2.2.1 (hw hpos).1
  · exact coframe_tempered (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => stableScale_ge_one k χ _) (fun n => unstableScale_ge_one k χ _)
      (fun n => hb n hpos) hz.2.1 hz.2.2.2 (hw hpos).2

end StandardMapEntropy

end
end

end OAI
