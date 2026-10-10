import OAI.Analysis.IntegralMeans.AreaTransport

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight

def outsideCore : Set ℂ := {z | z ∈ halfPlane ∧ (1/2 : ℝ) ≤ ‖diskCayley z‖}

lemma measurable_diskCayley : Measurable diskCayley :=
  (measurable_id.sub_const _).div (measurable_id.add_const _)

lemma measurableSet_outsideCore : MeasurableSet outsideCore :=
  isOpen_halfPlane.measurableSet.inter (measurableSet_le measurable_const measurable_diskCayley.norm)

lemma classFun_lower_outsideCore (g : DiskClass) {z : ℂ} (hz : z ∈ outsideCore) :
    (1/16 : ℝ) ≤ ‖classFun g z‖ := by
  have hl := schlicht_lower_growth g.2 (diskCayley_maps hz.1)
  have he : ‖classFun g z‖ = 2*‖diskExtend g.1 (diskCayley z)‖ := by
    simp [classFun,diskToHalf]
  rw [he]
  have hm := hz.2
  linarith

lemma classFun_ne_zero_outsideCore (g : DiskClass) {z : ℂ} (hz : z ∈ outsideCore) :
    classFun g z ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) (classFun_lower_outsideCore g hz)))

def planeClassValue (g : DiskClass) (z : ℂ) : ℂ :=
  by classical exact if z ∈ halfPlane then classFun g z else 0

attribute [local irreducible] classFun

lemma measurable_planeClassValue : Measurable (fun p : DiskClass × ℂ => planeClassValue p.1 p.2) := by
  classical
  let s : Set (DiskClass × ℂ) := Prod.snd ⁻¹' halfPlane
  have hc : Continuous (fun p : s => classFun p.val.1 p.val.2) := by
    exact continuous_classFun_eval.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [planeClassValue,s,Set.mem_preimage,dite_eq_ite] using
    hc.measurable.dite (measurable_const (a := (0 : ℂ)))
      (isOpen_halfPlane.measurableSet.preimage measurable_snd)

lemma planeClassValue_eq (g : DiskClass) {z : ℂ} (hz : z ∈ halfPlane) :
    planeClassValue g z = classFun g z := by simp [planeClassValue,hz]

lemma continuous_classFun_at (z : halfPlane) : Continuous (fun g : DiskClass => classFun g z) :=
  continuous_classFun_eval.comp (continuous_id.prodMk continuous_const)

lemma measurable_classFun_at {z : ℂ} (hz : z ∈ halfPlane) : Measurable (fun g : DiskClass => classFun g z) :=
  (continuous_classFun_at ⟨z,hz⟩).measurable

lemma integral_closedBall_translate.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) (r : ℝ) :
    (∫ w in Metric.closedBall (0 : ℂ) r, f (w+z)) = ∫ w in Metric.closedBall z r, f w := by
  have he : (fun w : ℂ => w+z) ⁻¹' Metric.closedBall z r = Metric.closedBall 0 r := by
    ext w
    simp [Metric.mem_closedBall,dist_eq_norm]
  rw [← he]
  exact (measurePreserving_add_right volume z).setIntegral_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f _

lemma volume_real_closedBall_complex (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall z r) = Real.pi*r^2 := by
  rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp only [ENNReal.coe_toReal,NNReal.coe_real_pi]
  ring

lemma holomorphic_sq_submean_center {f : ℂ → ℂ} {z : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z R)) (hr : 0 < r) (hrR : r < R) :
    Real.pi*r^2*‖f z‖^2 ≤ ∫ w in Metric.closedBall z r, ‖f w‖^2 := by
  have hfd : DifferentiableOn ℂ (fun w => f (w+z)) (Metric.ball 0 R) := by
    apply hf.comp (differentiable_id.add_const z).differentiableOn
    intro w hw
    simpa [Metric.mem_ball,dist_eq_norm] using hw
  have hh := holomorphic_sq_submean hfd hr hrR
  rw [integral_closedBall_translate (fun w => ‖f w‖^2) z r] at hh
  simpa only [volume_real_closedBall_complex 0 hr.le,zero_add] using hh

lemma holomorphic_sq_submean_lintegral {f : ℂ → ℂ} {z : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z R)) (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (Real.pi*r^2*‖f z‖^2) ≤
      ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖^2) := by
  have hi : IntegrableOn (fun w => ‖f w‖^2) (Metric.closedBall z r) volume := ((hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)).norm.pow 2).integrableOn_compact
    (isCompact_closedBall z r)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (holomorphic_sq_submean_center hf hr hrR)

lemma finite_density_compact_tail (s : Set ℂ) (b : ℂ → ℝ≥0∞)
    (hf : (∫⁻ z in s, b z) < ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ (∫⁻ z in s \ K, b z) < ε := by
  let ν := (volume.restrict s).withDensity b
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.ne
  obtain ⟨K,hKsub,hK,hKε⟩ := (MeasurableSet.univ (α := ℂ)).exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top ν univ) hε.ne'
  refine ⟨K,hK,?_⟩
  have he : ν (univ \ K) = ∫⁻ z in s \ K, b z := by
    dsimp only [ν]
    have heK : (univ \ K : Set ℂ) = Kᶜ := by ext z; simp
    rw [heK]
    rw [withDensity_apply _ hK.isClosed.measurableSet.compl]
    rw [Measure.restrict_restrict hK.isClosed.measurableSet.compl]
    have hsK : Kᶜ ∩ s = s \ K := by ext z; simp [and_comm]
    rw [hsK]
  rwa [he] at hKε

lemma weighted_holomorphic_tail {q : ℂ → ℂ} {s : Set ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (hR₀ : 0 ≤ R₀)
    (hs : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → z ∈ s)
    (hq : ∀ z ∈ s, DifferentiableAt ℂ q z)
    (hfin : (∫⁻ z in s, ENNReal.ofReal (z.im^a*‖q z‖^2)) < ∞) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      z.im^(a+2)*‖q z‖^2 < ε := by
  intro ε hε
  let C : ℝ := 16*(2 : ℝ)^a/Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨K,hK,hKε⟩ := finite_density_compact_tail s
    (fun z => ENNReal.ofReal (z.im^a*‖q z‖^2)) hfin
    (ENNReal.ofReal_pos.mpr (div_pos hε hC))
  obtain ⟨M,hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨2*(max R₀ M+1),fun z hy hz => ?_⟩
  have hn : 0 < ‖z‖ := by nlinarith [le_max_left R₀ M]
  have hball (w : ℂ) (hw : w ∈ Metric.ball z (z.im/2)) :
      0 < w.im ∧ R₀ < ‖w‖ ∧ w ∉ K := by
    have hd : ‖w-z‖ < z.im/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hi := Complex.abs_im_le_norm (w-z)
    have him : z.im/2 < w.im := by
      rw [Complex.sub_im] at hi
      have hl := neg_le_of_abs_le hi
      linarith
    have himz : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
    have hnw := norm_sub_norm_le z w
    have hdist : ‖z-w‖ = ‖w-z‖ := norm_sub_rev z w
    rw [hdist] at hnw
    have hnw' : max R₀ M < ‖w‖ := by nlinarith
    refine ⟨by linarith,lt_of_le_of_lt (le_max_left _ _) hnw',?_⟩
    intro hwK
    have hm := hM hwK
    simp only [Metric.mem_closedBall,dist_zero_right] at hm
    exact (not_lt_of_ge (hm.trans (le_max_right _ _))) hnw'
  have hhol : DifferentiableOn ℂ q (Metric.ball z (z.im/2)) := fun w hw =>
    (hq w (hs w (hball w hw).1 (hball w hw).2.1)).differentiableWithinAt
  have hsmall : Metric.closedBall z (z.im/4) ⊆ Metric.ball z (z.im/2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub : Metric.closedBall z (z.im/4) ⊆ s \ K := by
    intro w hw
    obtain ⟨hwi,hwn,hwK⟩ := hball w (hsmall hw)
    exact ⟨hs w hwi hwn,hwK⟩
  have hmean := holomorphic_sq_submean_lintegral hhol (by linarith : 0 < z.im/4) (by linarith)
  have hcomp (w : ℂ) (hw : w ∈ Metric.closedBall z (z.im/4)) :
      z.im^a*‖q w‖^2 ≤ (2 : ℝ)^a*(w.im^a*‖q w‖^2) := by
    have hwi := (hball w (hsmall hw)).1
    have hd : ‖w-z‖ ≤ z.im/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have hi := Complex.abs_im_le_norm (w-z)
    rw [Complex.sub_im] at hi
    have hl := neg_le_of_abs_le hi
    have hle : z.im ≤ 2*w.im := by linarith
    have hh := Real.rpow_le_rpow hy.le hle ha
    rw [Real.mul_rpow (by norm_num) hwi.le] at hh
    nlinarith [sq_nonneg ‖q w‖]
  have hweighted : ENNReal.ofReal (z.im^a)*(∫⁻ w in Metric.closedBall z (z.im/4), ENNReal.ofReal (‖q w‖^2)) ≤
      ENNReal.ofReal ((2 : ℝ)^a)*(∫⁻ w in s \ K, ENNReal.ofReal (w.im^a*‖q w‖^2)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply le_trans ?_ (lintegral_mono_set hsub)
    apply setLIntegral_mono' measurableSet_closedBall
    intro w hw
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    exact ENNReal.ofReal_le_ofReal (hcomp w hw)
  have hineq : ENNReal.ofReal (z.im^(a+2)*‖q z‖^2) ≤
      ENNReal.ofReal C*(∫⁻ w in s \ K, ENNReal.ofReal (w.im^a*‖q w‖^2)) := by
    have hh := (mul_le_mul' (le_refl (ENNReal.ofReal (z.im^a))) hmean).trans hweighted
    have hmul : ENNReal.ofReal (z.im^a)*ENNReal.ofReal (Real.pi*(z.im/4)^2*‖q z‖^2) =
        ENNReal.ofReal (Real.pi/16)*ENNReal.ofReal (z.im^(a+2)*‖q z‖^2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
        ← ENNReal.ofReal_mul (by positivity),Real.rpow_add hy,Real.rpow_two]
      congr 1
      ring
    rw [hmul] at hh
    apply (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (Real.pi/16) ≠ 0)
      ENNReal.ofReal_ne_top).mp
    have he : ENNReal.ofReal (Real.pi/16)*ENNReal.ofReal C = ENNReal.ofReal ((2 : ℝ)^a) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp only [C]
      field_simp
    rw [← mul_assoc,he]
    exact hh
  have hh := hineq.trans_lt ((ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top).mpr hKε)
  have he : ENNReal.ofReal C*ENNReal.ofReal (ε/C) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hC.le,mul_div_cancel₀ ε (ne_of_gt hC)]
  rw [he] at hh
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hh

def HasQuarticTail (F : ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
    z.im^a*‖F z‖⁻¹^4 < ε

lemma quartic_tail_proper {F : ℂ → ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (ht : HasQuarticTail F a)
    (hzero : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc : ContinuousOn F {z | 0 < z.im}) {K : Set ℂ} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K) := by
  obtain ⟨M₀,hM₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let M := max M₀ 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right M₀ 1)
  have hδ : 0 < η^a*M⁻¹^4 := mul_pos (Real.rpow_pos_of_pos hη _) (pow_pos (inv_pos.mpr hM) _)
  obtain ⟨R,hR⟩ := ht (η^a*M⁻¹^4) hδ
  have hb : {z : ℂ | η ≤ z.im} ∩ F ⁻¹' K ⊆ Metric.closedBall 0 (max R (R₀+1)) := by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra! hzn
    have hy : 0 < z.im := hη.trans_le hz.1
    have hznR : R ≤ ‖z‖ := (le_max_left _ _).trans hzn.le
    have hzn₀ : R₀ < ‖z‖ := by linarith [le_max_right R (R₀+1)]
    have hFn : 0 < ‖F z‖ := norm_pos_iff.mpr (hzero z hy hzn₀)
    have hFle : ‖F z‖ ≤ M := by
      have hh := hM₀ hz.2
      exact (show ‖F z‖ ≤ M₀ by simpa using hh).trans (le_max_left _ _)
    have hpow : M⁻¹^4 ≤ ‖F z‖⁻¹^4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hM.le) ((inv_le_inv₀ hM hFn).mpr hFle) 4
    have hheight := Real.rpow_le_rpow hη.le hz.1 ha
    have hle := mul_le_mul hheight hpow (by positivity) (Real.rpow_nonneg hy.le _)
    exact (not_lt_of_ge hle) (hR z hy hznR)
  apply (isCompact_closedBall (0 : ℂ) (max R (R₀+1))).of_isClosed_subset _ hb
  exact (hc.mono (fun z hz => hη.trans_le hz)).preimage_isClosed_of_isClosed
    (isClosed_le continuous_const Complex.continuous_im) hK.isClosed

lemma quartic_tail_height_bound {F : ℂ → ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (ht : HasQuarticTail F a)
    (hzero : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc : ContinuousOn F {z | 0 < z.im}) {K : Set ℂ} (hK : IsCompact K) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, 0 < z.im → F z ∈ K → z.im ≤ H := by
  have hk := quartic_tail_proper ha ht hzero hc hK (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M,hM⟩ := hk.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num) (le_max_right M 1),fun z _ hz => ?_⟩
  by_cases hy : 1 ≤ z.im
  · have hh : ‖z‖ ≤ M := by simpa using hM ⟨hy,hz⟩
    exact ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans (hh.trans (le_max_left _ _))
  · exact (le_of_lt (lt_of_not_ge hy)).trans (le_max_right _ _)

lemma quartic_tail_iff_power {F : ℂ → ℂ} {k : ℝ} (ht : HasQuarticTail F (4*k)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      z.im^k*‖F z‖⁻¹ < ε := by
  intro ε hε
  obtain ⟨R,hR⟩ := ht (ε^4) (pow_pos hε _)
  refine ⟨R,fun z hz hzr => ?_⟩
  have hh := hR z hz hzr
  have he : z.im^(4*k)*‖F z‖⁻¹^4 = (z.im^k*‖F z‖⁻¹)^4 := by
    rw [mul_comm (4 : ℝ) k,Real.rpow_mul hz.le,Real.rpow_ofNat,mul_pow]
  rw [he] at hh
  by_contra! hle
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le hle 4)) hh

lemma outsideCore_of_norm {z : ℂ} (hz : z ∈ halfPlane) (hn : 3 < ‖z‖) :
    z ∈ outsideCore := by
  refine ⟨hz,?_⟩
  change (1/2 : ℝ) ≤ ‖(z-Complex.I)/(z+Complex.I)‖
  rw [norm_div,le_div_iff₀ (norm_pos_iff.mpr (cayley_den_ne_zero hz))]
  have h₁ : ‖z‖ ≤ ‖z-Complex.I‖+1 := by
    simpa only [sub_add_cancel,Complex.norm_I] using norm_add_le (z-Complex.I) Complex.I
  have h₂ : ‖z+Complex.I‖ ≤ ‖z‖+1 := by
    simpa only [Complex.norm_I] using norm_add_le z Complex.I
  linarith

lemma class_quartic_tail (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞) :
    HasQuarticTail (classFun g) (β+3) := by
  let q : ℂ → ℂ := fun z => (classFun g z)⁻¹^2
  have hnorm (z : ℂ) : ‖q z‖^2 = ‖classFun g z‖⁻¹^4 := by
    simp only [q,norm_pow,norm_inv,← pow_mul]
  have hhol (z : ℂ) (hz : z ∈ outsideCore) : DifferentiableAt ℂ q z :=
    (((classFun_schlicht g).1.1.differentiableAt
      (isOpen_halfPlane.mem_nhds hz.1)).inv (classFun_ne_zero_outsideCore g hz)).pow 2
  have hfq : (∫⁻ z in outsideCore, ENNReal.ofReal (z.im^(β+1)*‖q z‖^2)) < ∞ := by
    simpa only [hnorm] using hfin
  have hh := weighted_holomorphic_tail (by linarith : 0 ≤ β+1) (by norm_num : (0 : ℝ) ≤ 3)
    (fun z hz hn => outsideCore_of_norm hz hn) hhol hfq
  intro ε hε
  obtain ⟨R,hR⟩ := hh ε hε
  refine ⟨R,fun z hz hzr => ?_⟩
  have he : β+1+2 = β+3 := by ring
  simpa only [he,hnorm] using hR z hz hzr

lemma class_proper_preimage (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞)
    {K : Set ℂ} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    IsCompact ({z : ℂ | η ≤ z.im} ∩ classFun g ⁻¹' K) :=
  quartic_tail_proper (by linarith : 0 ≤ β+3) (class_quartic_tail g hβ hfin)
    (fun z hz hn => classFun_ne_zero_outsideCore g (outsideCore_of_norm hz hn))
    (classFun_schlicht g).1.1.continuousOn hK hη

lemma class_preimage_height_bound (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, 0 < z.im → classFun g z ∈ K → z.im ≤ H :=
  quartic_tail_height_bound (by linarith : 0 ≤ β+3) (class_quartic_tail g hβ hfin)
    (fun z hz hn => classFun_ne_zero_outsideCore g (outsideCore_of_norm hz hn))
    (classFun_schlicht g).1.1.continuousOn hK

end Brennan

end

end OAI
