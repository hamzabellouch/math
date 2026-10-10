import OAI.Geometry.LatticeCovering.Marginals

namespace OAI

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma integrable_normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsFiniteMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (g : MatrixSpace n k) :
    Integrable (normalizedProjection μ s r g) volume := by
  change Integrable (fun y => normalizedProjection μ s r g y) volume
  simp_rw [normalizedProjection_kernel]
  exact convolution_integrable μ ((s • colLinear g).continuous_of_finiteDimensional.measurable)
    (by have := sq_pos_of_ne_zero hr; positivity)

lemma integral_normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (g : MatrixSpace n k) :
    (∫ y, normalizedProjection μ s r g y)=1 := by
  simp_rw [normalizedProjection_kernel]
  exact convolution_integral μ ((s • colLinear g).continuous_of_finiteDimensional.measurable)
    (by have := sq_pos_of_ne_zero hr; positivity)

lemma continuous_normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsFiniteMeasure μ] (s r : ℝ) (g : MatrixSpace n k) :
    Continuous (normalizedProjection μ s r g) :=
  (continuous_smoothedProjection_y μ s r g).const_mul _

lemma normalizedProjection_pos {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (g : MatrixSpace n k) (y : Isotropization.E k) :
    0 < normalizedProjection μ s r g y := by
  rw [normalizedProjection]
  apply mul_pos (inv_pos.mpr (normalizer_pos k (by have := sq_pos_of_ne_zero hr; positivity)))
  have hi : Integrable (fun x : Isotropization.E n => Real.exp (-r^2*‖y-s•colApply g x‖^2/2)) μ := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc : Continuous (fun x : Isotropization.E n => colApply g x) := continuous_colApply.comp (continuous_const.prodMk continuous_id)
      fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (y-s•colApply g x))
  exact integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi |>.mpr (by simp [Function.support,ne_of_gt (Real.exp_pos _)])

end SingleLatticeCovering.GaussianProjection

end

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def scaleVariance {n : ℕ} (s r : ℝ) (x : Isotropization.E n) : ℝ :=
  (s*‖x‖)^2+1/r^2

lemma scaleVariance_pos {n : ℕ} (s : ℝ) {r : ℝ} (hr : r ≠ 0) (x : Isotropization.E n) :
    0 < scaleVariance s r x := by
  unfold scaleVariance
  have := sq_pos_of_ne_zero hr
  positivity

lemma scaleVariance_integrable {n : ℕ} {μ : Measure (Isotropization.E n)}
    [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (s r : ℝ) :
    Integrable (scaleVariance s r) μ := by
  change Integrable (fun x => (s*‖x‖)^2+1/r^2) μ
  simp only [mul_pow]
  exact (hμ.norm.integrable_sq.const_mul _).add (integrable_const _)

lemma scaleVariance_mean {n : ℕ} {μ : Measure (Isotropization.E n)}
    [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s r : ℝ) :
    (∫ x, scaleVariance s r x ∂μ)=s^2*(n:ℝ)+1/r^2 := by
  unfold scaleVariance
  simp only [mul_pow]
  have hi : Integrable (fun x : Isotropization.E n => s^2*‖x‖^2) μ := hμ.norm.integrable_sq.const_mul _
  rw [integral_add hi (integrable_const _),integral_const_mul,
    isotropic_norm_sq hμ hiso]
  simp

noncomputable def normalizedModel {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (y : Isotropization.E k) : ℝ :=
  (normalizer k (r^2/2))⁻¹*radialSmoothedDensity μ s r y

lemma normalizedModel_mixture {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Isotropization.E k) :
    normalizedModel μ s r y=∫ x, density (1/(2*scaleVariance s r x)) y ∂μ :=
  normalized_radialSmoothedDensity_mixture μ s hr y

noncomputable def projectionError (n k : ℕ) (s r : ℝ) : ℝ :=
  (normalizer k (r^2/2))⁻¹*|r*s| *Real.sqrt (Real.sqrt (n:ℝ))*Real.sqrt (k:ℝ)

lemma projectionError_nonneg (n k : ℕ) (s r : ℝ) : 0 ≤ projectionError n k s r := by
  dsimp [projectionError,normalizer]
  positivity

lemma exists_normalized_projection {n k : ℕ} {μ : Measure (Isotropization.E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ∃ g : MatrixSpace n k, ∀ y : Isotropization.E k,
      |normalizedProjection μ s r g y-normalizedModel μ s r y| ≤ projectionError n k s r := by
  obtain ⟨g,hg⟩ := exists_uniform_smoothed_projection (k := k) hμ hiso s r
  refine ⟨g,fun y => ?_⟩
  have hN : 0 < normalizer k (r^2/2) := normalizer_pos k (by have := sq_pos_of_ne_zero hr; positivity)
  have H := hg y
  rw [←radialSmoothedDensity_cast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at H
  unfold normalizedProjection normalizedModel
  rw [←mul_sub,abs_mul,abs_of_nonneg (inv_nonneg.mpr hN.le)]
  have HH := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hN.le)
  exact HH.trans_eq (by dsimp [projectionError]; ring)



theorem actual_model_shell {n k : ℕ} (hk : 2 ≤ k) {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) {r T : ℝ}
    (hr : r ≠ 0) (hT : 0 < T) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ y : Isotropization.E k in {y | ‖y‖ ≤ (1-ε)*r₀}, normalizedModel μ s r y)+
        (∫ y : Isotropization.E k in {y | (1+ε)*r₀ < ‖y‖}, normalizedModel μ s r y) ≤
      (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))+
        2*(projectionError n k s r*volume.real (Metric.closedBall (0:Isotropization.E k) T)+
          (k:ℝ)*(s^2*(n:ℝ)+1/r^2)/T^2) := by
  obtain ⟨g,hg⟩ := exists_normalized_projection (k := k) hμ hiso s hr
  have hmod : (normalizedModel μ s r : Isotropization.E k → ℝ)=
      fun y => ∫ x, density (1/(2*scaleVariance s r x)) y ∂μ := by
    funext y; exact normalizedModel_mixture μ s hr y
  have hm : Measurable (scaleVariance (n := n) s r) := by unfold scaleVariance; fun_prop
  have hMi : Integrable (normalizedModel μ s r : Isotropization.E k → ℝ) volume := by
    rw [hmod]; exact mixture_integrable μ hm (scaleVariance_pos s hr)
  have hMn (y : Isotropization.E k) : 0 ≤ normalizedModel μ s r y := by
    rw [hmod]
    exact integral_nonneg (fun x => (density_pos (by have := scaleVariance_pos s hr x; positivity) y).le)
  have hMr (x y : Isotropization.E k) (hxy : ‖x‖=‖y‖) : normalizedModel μ s r x=normalizedModel μ s r y := by
    unfold normalizedModel
    rw [radialSmoothedDensity_norm_eq μ s r hxy]
  obtain ⟨r₀,hr₀,H⟩ := radial_model_shell hk (logConcave_normalizedProjection hK hc μ hdef s r g)
    (normalizedProjection_pos μ s hr g) (continuous_normalizedProjection μ s r g)
    (integrable_normalizedProjection μ s hr g) (integral_normalizedProjection μ s hr g)
    hMi hMn hMr (projectionError_nonneg n k s r) hg T
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  have ht : (∫ y : Isotropization.E k in (Metric.closedBall (0:Isotropization.E k) T)ᶜ,
      normalizedModel μ s r y) ≤ (k:ℝ)*(s^2*(n:ℝ)+1/r^2)/T^2 := by
    simp_rw [normalizedModel_mixture μ s hr]
    have HH := mixture_tail_markov (k := k) μ hm (scaleVariance_pos s hr) (scaleVariance_integrable hμ s r) hT
    rwa [scaleVariance_mean hμ hiso] at HH
  linarith [H ε hε hε1]


end SingleLatticeCovering.GaussianProjection

end

section

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

lemma probability_interval_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (a b : ℝ) :
    1-μ.real {x | v x ≤ a}-μ.real {x | b ≤ v x} ≤ μ.real {x | a ≤ v x ∧ v x ≤ b} := by
  let B := {x | a ≤ v x ∧ v x ≤ b}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hs : Bᶜ ⊆ {x | v x ≤ a} ∪ {x | b ≤ v x} := by
    intro x hx
    by_cases hxa : a ≤ v x
    · exact Or.inr (le_of_lt (lt_of_not_ge (fun hxb => hx ⟨hxa,hxb⟩)))
    · exact Or.inl (le_of_lt (lt_of_not_ge hxa))
  have H := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le _ _)
  rw [probReal_compl_eq_one_sub hB] at H
  change 1-μ.real {x | v x ≤ a}-μ.real {x | b ≤ v x} ≤ μ.real B
  linarith



theorem mixture_shell_scales {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hk : 0 < k)
    {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x)
    {r₀ ε S : ℝ} (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1)
    (hshell : (∫ y : E k in {y | ‖y‖ ≤ (1-ε)*r₀}, ∫ x, density (1/(2*v x)) y ∂μ)+
      (∫ y : E k in {y | (1+ε)*r₀ < ‖y‖}, ∫ x, density (1/(2*v x)) y ∂μ) ≤ S) :
    1-S/(1-Real.exp (-(k:ℝ)*ε^2/16)) ≤
      μ.real {x | ((1-ε)*r₀)^2/((1+ε)*(k:ℝ)) ≤ v x ∧
        v x ≤ ((1+ε)*r₀)^2/((1-ε)*(k:ℝ))} := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hc : 0 < 1-Real.exp (-(k:ℝ)*ε^2/16) := by
    have hh : -(k:ℝ)*ε^2/16 < 0 := by nlinarith [sq_pos_of_pos hε]
    linarith [Real.exp_lt_one_iff.mpr hh]
  let a := ((1-ε)*r₀)^2/((1+ε)*(k:ℝ))
  let b := ((1+ε)*r₀)^2/((1-ε)*(k:ℝ))
  have heA : {x | v x*(1+ε)*(k:ℝ) ≤ ((1-ε)*r₀)^2}={x | v x ≤ a} := by
    ext x
    simp only [mem_ofPred_eq,a,le_div_iff₀ (mul_pos (show 0 < 1+ε by linarith) hkR)]
    ring_nf
  have heB : {x | ((1+ε)*r₀)^2 ≤ v x*(1-ε)*(k:ℝ)}={x | b ≤ v x} := by
    ext x
    simp only [mem_ofPred_eq,b,div_le_iff₀ (mul_pos (show 0 < 1-ε by linarith) hkR)]
    ring_nf
  have HA := mixture_scale_small (k := k) μ hm hv (show 0 ≤ (1-ε)*r₀ by positivity) hε hε1
  have HB := mixture_scale_large (k := k) μ hm hv (show 0 ≤ (1+ε)*r₀ by positivity) hε hε1
  rw [heA] at HA
  rw [heB] at HB
  have Hsum : μ.real {x | v x ≤ a}+μ.real {x | b ≤ v x} ≤ S/(1-Real.exp (-(k:ℝ)*ε^2/16)) := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  exact le_trans (by linarith) (probability_interval_lower μ hm a b)


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

lemma good_scale_anchors {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Ω → ℝ} (hm : Measurable v) (hi : Integrable v μ) (hn : ∀ x, 0 ≤ v x)
    (hmean : (∫ x, v x ∂μ) ≤ 2) {p u w : ℝ}
    (hbig : p ≤ μ.real {x | 1/2 ≤ v x})
    (hgood : 1-p < μ.real {x | u ≤ v x ∧ v x ≤ w})
    (hhalf : 1/2 ≤ μ.real {x | u ≤ v x ∧ v x ≤ w})
    (huw : w ≤ 2*u) : 1/4 ≤ u ∧ u ≤ 4 := by
  let B := {x | u ≤ v x ∧ v x ≤ w}
  let A := {x | (1:ℝ)/2 ≤ v x}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hsum := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hunion : μ.real (A ∪ B) ≤ 1 := by
    simpa only [probReal_univ] using measureReal_mono (μ := μ) (subset_univ (A ∪ B))
  have hp : 0 < μ.real (A ∩ B) := by change p ≤ μ.real A at hbig; change 1-p < μ.real B at hgood; linarith
  have hne : (A ∩ B).Nonempty := by
    by_contra h
    have he : A ∩ B=∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he,measureReal_empty] at hp
    exact (lt_irrefl (0:ℝ)) hp
  obtain ⟨x,hxA,hxB⟩ := hne
  have hul : 1/4 ≤ u := by
    change 1/2 ≤ v x at hxA
    change u ≤ v x ∧ v x ≤ w at hxB
    linarith
  have H := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Filter.Eventually.of_forall hn) hi u
  have hmono : μ.real B ≤ μ.real {x | u ≤ v x} := measureReal_mono (fun x hx => hx.1)
  have hh : 1/2 ≤ μ.real {x | u ≤ v x} := hhalf.trans hmono
  constructor
  · exact hul
  · nlinarith

lemma scale_interval_ratio {k : ℕ} (hk : 0 < k) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let u := ((1-ε)*r)^2/((1+ε)*(k:ℝ))
    let w := ((1+ε)*r)^2/((1-ε)*(k:ℝ))
    0 < u ∧ u ≤ w ∧ w/u=((1+ε)/(1-ε))^3 := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  dsimp only
  have hp : 0 < 1-ε := by linarith
  have hq : 0 < 1+ε := by linarith
  have hu : 0 < ((1-ε)*r)^2/((1+ε)*(k:ℝ)) := by positivity
  refine ⟨hu,?_,?_⟩
  · apply (div_le_div_iff₀ (mul_pos hq hkR) (mul_pos hp hkR)).mpr
    have H : (1-ε)^3 ≤ (1+ε)^3 := pow_le_pow_left₀ hp.le (by linarith) 3
    have HH := mul_le_mul_of_nonneg_right H (mul_nonneg (sq_nonneg r) hkR.le)
    nlinarith
  · field_simp

lemma scale_ratio_le_two {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) :
    ((1+ε)/(1-ε))^3 ≤ 2 := by
  have hp : 0 < 1-ε := by linarith
  have hh : (1+ε)/(1-ε) ≤ 11/9 := (div_le_iff₀ hp).mpr (by linarith)
  have H := pow_le_pow_left₀ (by positivity : 0 ≤ (1+ε)/(1-ε)) hh 3
  norm_num at H ⊢
  linarith


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def shellError (n k : ℕ) (s r T ε : ℝ) : ℝ :=
  (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))+
    2*(projectionError n k s r*volume.real (Metric.closedBall (0:Isotropization.E k) T)+
      (k:ℝ)*(s^2*(n:ℝ)+1/r^2)/T^2)

noncomputable def shellLoss (n k : ℕ) (s r T ε : ℝ) : ℝ :=
  shellError n k s r T ε/(1-Real.exp (-(k:ℝ)*ε^2/16))

lemma scaleVariance_measurable {n : ℕ} (s r : ℝ) : Measurable (scaleVariance (n := n) s r) := by
  unfold scaleVariance
  fun_prop




theorem actual_good_scales {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (μ : Measure (Isotropization.E n)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε : ℝ} (hs : s^2*(n:ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10)
    (hloss : shellLoss n k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss n k s r T ε ≤ 1/8) :
    ∃ u w : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧ u ≤ w ∧
      w/u=((1+ε)/(1-ε))^3 ∧
      1-shellLoss n k s r T ε ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w} := by
  have hr0 : r ≠ 0 := by linarith
  have hk0 : 0 < k := by omega
  obtain ⟨r₀,hr₀,hsh⟩ := actual_model_shell hk hK hc μ hdef hμ hiso s hr0 hT
  have hshell := hsh ε hε (by linarith)
  simp_rw [normalizedModel_mixture μ s hr0] at hshell
  have hv := scaleVariance_pos (n := n) s hr0
  have hvm := scaleVariance_measurable (n := n) s r
  have hgood := mixture_shell_scales μ hk0 hvm hv hr₀ hε (by linarith) hshell
  let u := ((1-ε)*r₀)^2/((1+ε)*(k:ℝ))
  let w := ((1+ε)*r₀)^2/((1-ε)*(k:ℝ))
  change 1-shellLoss n k s r T ε ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w} at hgood
  obtain ⟨hu,huw,hratio⟩ := scale_interval_ratio hk0 hr₀ hε.le (show ε < 1 by linarith)
  change 0 < u at hu
  change u ≤ w at huw
  change w/u=((1+ε)/(1-ε))^3 at hratio
  have ratio2 : w ≤ 2*u := (div_le_iff₀ hu).mp (hratio ▸ scale_ratio_le_two hε.le hε1)
  have hbig : 1/(4*fourthMomentConstant) ≤ μ.real {x | 1/2 ≤ scaleVariance s r x} := by
    apply le_trans (uniform_body_radius_lower hn hK hc μ hdef hμ hiso)
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    change (n:ℝ)/2 ≤ ‖x‖^2 at hx
    change 1/2 ≤ (s*‖x‖)^2+1/r^2
    have H := mul_le_mul_of_nonneg_left hx (sq_nonneg s)
    have hq : 0 ≤ 1/r^2 := by positivity
    nlinarith
  have hmean : (∫ x, scaleVariance s r x ∂μ) ≤ 2 := by
    rw [scaleVariance_mean hμ hiso,hs]
    have hh : 1 ≤ r^2 := by nlinarith
    have hq : 1/r^2 ≤ 1 := (div_le_one (by positivity : 0 < r^2)).mpr hh
    linarith
  obtain ⟨hulo,huhi⟩ := good_scale_anchors μ hvm (scaleVariance_integrable hμ s r)
    (fun x => (hv x).le) hmean hbig (lt_of_lt_of_le (by linarith : 1-1/(4*fourthMomentConstant) < 1-shellLoss n k s r T ε) hgood)
    (le_trans (by linarith : (1:ℝ)/2 ≤ 1-shellLoss n k s r T ε) hgood) ratio2
  exact ⟨u,w,hulo,huhi,huw,hratio,hgood⟩


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

lemma normalizer_ratio {k : ℕ} {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    normalizer k (1/(2*u))/normalizer k (1/(2*w))=(u/w)^((k:ℝ)/2) := by
  unfold normalizer
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  simp only [one_div,div_inv_eq_mul]
  rw [←Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

lemma inverse_scale_ratio_lower {u w ε : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (hratio : w/u=((1+ε)/(1-ε))^3) :
    1-6*ε ≤ u/w := by
  have _ := hu
  have _ := hw
  have hp : 0 < 1-ε := by linarith
  have hq : 0 < 1+ε := by linarith
  have he : u/w=((1-ε)/(1+ε))^3 := by
    have H := congrArg (fun x : ℝ => x⁻¹) hratio
    rw [inv_div,←inv_pow,inv_div] at H
    exact H
  rw [he]
  have hh : 1-2*ε ≤ (1-ε)/(1+ε) := (le_div_iff₀ hq).mpr (by nlinarith)
  have H := pow_le_pow_left₀ (by linarith : 0 ≤ 1-2*ε) hh 3
  have HB := one_add_mul_le_pow (a := -2*ε) (by linarith : -2 ≤ -2*ε) 3
  norm_num only [Nat.cast_ofNat] at HB
  nlinarith

lemma normalizer_ratio_lower {k : ℕ} {u w ε : ℝ} (hu : 0 < u) (huw : u ≤ w)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (hratio : w/u=((1+ε)/(1-ε))^3)
    (hsmall : (k:ℝ)*ε ≤ 1/48) :
    7/8 ≤ normalizer k (1/(2*u))/normalizer k (1/(2*w)) := by
  have hw : 0 < w := hu.trans_le huw
  rw [normalizer_ratio hu hw]
  have hr0 : 0 < u/w := div_pos hu hw
  have hr1 : u/w ≤ 1 := (div_le_one hw).mpr huw
  have HB := one_add_mul_le_pow (a := -6*ε) (by linarith : -2 ≤ -6*ε) k
  have HP := pow_le_pow_left₀ (by linarith : 0 ≤ 1-6*ε)
    (inverse_scale_ratio_lower hu hw hε hε1 hratio) k
  have HR := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (show (k:ℝ)/2 ≤ k by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  rw [Real.rpow_natCast] at HR
  have HBB : 1-6*(k:ℝ)*ε ≤ (1-6*ε)^k := by
    calc
      1-6*(k:ℝ)*ε=1+(k:ℝ)*(-6*ε) := by ring
      _ ≤ (1+(-6*ε))^k := HB
      _ = (1-6*ε)^k := by congr 1; ring
  exact le_trans (by nlinarith) (HBB.trans (HP.trans HR))


end SingleLatticeCovering.GaussianDensity

end

section

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

lemma normalizer_variance_mono {k : ℕ} {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normalizer k (1/(2*u)) ≤ normalizer k (1/(2*v)) := by
  unfold normalizer
  have he (a : ℝ) : Real.pi/(1/(2*a))=Real.pi*(2*a) := by simp only [one_div,div_inv_eq_mul]
  simp only [he]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le

lemma density_variance_le_peak {k : ℕ} {a v : ℝ} (ha : 0 < a) (hav : a ≤ v) (y : E k) :
    density (1/(2*v)) y ≤ (normalizer k (1/(2*a)))⁻¹ := by
  have hv : 0 < v := ha.trans_le hav
  apply le_trans _ (inv_anti₀ (normalizer_pos k (by positivity)) (normalizer_variance_mono ha hav))
  unfold density
  apply mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k (by positivity)).le)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)

lemma integrable_mixture_at {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v)
    {a : ℝ} (ha : 0 < a) (hav : ∀ x, a ≤ v x) (y : E k) :
    Integrable (fun x => density (1/(2*v x)) y) μ := by
  apply (integrable_const ((normalizer k (1/(2*a)))⁻¹)).mono' (by
    have H := (measurable_mixture_kernel (k := k) hm).comp (measurable_id.prodMk (measurable_const (a := y)))
    exact H.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    have hvx : 0 < 1/(2*v x) := by have := ha.trans_le (hav x); positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg (density_pos hvx y).le] using density_variance_le_peak ha (hav x) y)

lemma density_scales_lower {k : ℕ} {u v w : ℝ} (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w) (y : E k) :
    (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*density (1/(2*u)) y ≤
      density (1/(2*v)) y := by
  have hv : 0 < v := hu.trans_le huv
  have hw : 0 < w := hv.trans_le hvw
  have hNu : 0 < normalizer k (1/(2*u)) := normalizer_pos k (by positivity)
  have hNv : 0 < normalizer k (1/(2*v)) := normalizer_pos k (by positivity)
  have hNw : 0 < normalizer k (1/(2*w)) := normalizer_pos k (by positivity)
  have he : (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*(normalizer k (1/(2*u)))⁻¹=
      (normalizer k (1/(2*w)))⁻¹ := by field_simp
  unfold density
  rw [←mul_assoc,he]
  apply mul_le_mul (inv_anti₀ hNv (normalizer_variance_mono hv hvw)) _
    (Real.exp_pos _).le (inv_nonneg.mpr hNv.le)
  apply Real.exp_le_exp.mpr
  have hh : 1/(2*v) ≤ 1/(2*u) := one_div_le_one_div_of_le (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖y‖)]



theorem mixture_lower {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v)
    {a u w : ℝ} (ha : 0 < a) (hav : ∀ x, a ≤ v x) (hu : 0 < u) (huw : u ≤ w)
    (y : E k) :
    μ.real {x | u ≤ v x ∧ v x ≤ w}*
      (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*density (1/(2*u)) y ≤
      ∫ x, density (1/(2*v x)) y ∂μ := by
  have _ := huw
  classical
  let B := {x | u ≤ v x ∧ v x ≤ w}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  let c := (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*density (1/(2*u)) y
  have hh (x : Ω) : B.indicator (fun _ => c) x ≤ density (1/(2*v x)) y := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact density_scales_lower hu hx.1 hx.2 y
    · rw [indicator_of_notMem hx]
      exact (density_pos (by have := ha.trans_le (hav x); positivity) y).le
  have H := integral_mono ((integrable_const c).indicator hB) (integrable_mixture_at μ hm ha hav y) hh
  rw [integral_indicator hB,integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H
  change μ.real B*c ≤ _ at H
  simpa only [B,c,mul_assoc] using H


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators



theorem actual_smoothed_lower {n k D : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (μ : Measure (Isotropization.E n)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε : ℝ} (hs : s^2*(n:ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48)
    (hloss : shellLoss n k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss n k s r T ε ≤ 1/8) :
    ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧ ∃ g : MatrixSpace n D, ∀ y : Isotropization.E D,
      (3/4)*density (1/(2*u)) y-projectionError n D s r ≤ normalizedProjection μ s r g y := by
  have hr0 : r ≠ 0 := by linarith
  obtain ⟨u,w,hulo,huhi,huw,hratio,hgood⟩ := actual_good_scales hn hk hK hc μ hdef hμ hiso hs hr hT hε hε1 hloss hloss8
  have hu : 0 < u := by linarith
  have hratio' := normalizer_ratio_lower hu huw hε.le hε1 hratio hDε
  have hmass : 7/8 ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w} := by linarith
  have hm : Measurable (scaleVariance (n := n) s r) := scaleVariance_measurable s r
  have ha : 0 < 1/r^2 := by positivity
  have hav (x : Isotropization.E n) : 1/r^2 ≤ scaleVariance s r x := by unfold scaleVariance; nlinarith [sq_nonneg (s*‖x‖)]
  have hmodel (y : Isotropization.E D) : (3/4)*density (1/(2*u)) y ≤ normalizedModel μ s r y := by
    rw [normalizedModel_mixture μ s hr0]
    apply le_trans _ (mixture_lower μ hm ha hav hu huw y)
    have hmul := mul_le_mul hmass hratio' (by norm_num : (0:ℝ) ≤ 7/8) (measureReal_nonneg)
    have hp : (3/4:ℝ) ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w}*
      (normalizer D (1/(2*u))/normalizer D (1/(2*w))) := by nlinarith
    exact mul_le_mul_of_nonneg_right hp (density_pos (by positivity) y).le
  obtain ⟨g,hg⟩ := exists_normalized_projection (k := D) hμ hiso s hr0
  refine ⟨u,hulo,huhi,g,fun y => ?_⟩
  have H := (abs_le.mp (hg y)).1
  linarith [hmodel y]


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

noncomputable def densityFloor (k : ℕ) (R : ℝ) : ℝ :=
  (normalizer k (1/8))⁻¹*Real.exp (-8*(R+1)^2)

lemma densityFloor_pos (k : ℕ) (R : ℝ) : 0 < densityFloor k R := by
  unfold densityFloor
  exact mul_pos (inv_pos.mpr (normalizer_pos k (by norm_num))) (Real.exp_pos _)

lemma variance_density_floor {k : ℕ} {u R : ℝ} (hu : 1/4 ≤ u) (hu4 : u ≤ 4) (hR : 0 ≤ R)
    {y : E k} (hy : ‖y‖ ≤ 2*(R+1)) : densityFloor k R ≤ density (1/(2*u)) y := by
  have _ := hR
  have hu0 : 0 < u := by linarith
  have hb : 0 < 1/(2*u) := by positivity
  have hbu : 1/(2*u) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hN : normalizer k (1/(2*u)) ≤ normalizer k (1/8) := by
    convert normalizer_variance_mono hu0 hu4 using 1 ; norm_num
  unfold densityFloor density
  apply mul_le_mul (inv_anti₀ (normalizer_pos k hb) hN) _ (Real.exp_pos _).le
    (inv_nonneg.mpr (normalizer_pos k hb).le)
  apply Real.exp_le_exp.mpr
  have hy2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  nlinarith [mul_le_mul_of_nonneg_right hbu (sq_nonneg ‖y‖)]

lemma variance_density_nearby {k : ℕ} {u R δ : ℝ} (hu : 1/4 ≤ u) (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/(100*(R+1))) {y w : E k}
    (hy : ‖y‖ ≤ 2*R) (hw : ‖w-y‖ ≤ δ) :
    (3/4)*density (1/(2*u)) y ≤ density (1/(2*u)) w := by
  have hu0 : 0 < u := by linarith
  have hb : 0 < 1/(2*u) := by positivity
  have hbu : 1/(2*u) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hδ1 : δ ≤ 1/100 := by
    apply hδsmall.trans
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hδR : δ*(R+1) ≤ 1/100 := by
    have H := (le_div_iff₀ (by positivity : 0 < 100*(R+1))).mp hδsmall
    nlinarith
  have hwN : ‖w‖ ≤ ‖y‖+δ := by
    have H := norm_add_le (w-y) y
    rw [sub_add_cancel] at H
    linarith
  have hw2 := pow_le_pow_left₀ (norm_nonneg w) hwN 2
  have hdq : δ^2 ≤ δ/100 := by nlinarith
  have hxy : ‖w‖^2-‖y‖^2 ≤ 1/10 := by
    have H := mul_le_mul_of_nonneg_right hy hδ
    nlinarith
  have he : -(1/(2*u))*‖y‖^2-1/4 ≤ -(1/(2*u))*‖w‖^2 := by
    have H := mul_le_mul_of_nonneg_left hxy hb.le
    nlinarith
  have hexp : (3/4)*Real.exp (-(1/(2*u))*‖y‖^2) ≤ Real.exp (-(1/(2*u))*‖w‖^2) := by
    have hl : (3/4:ℝ) ≤ Real.exp (-(1/4:ℝ)) := by linarith [Real.add_one_le_exp (-(1/4:ℝ))]
    calc
      _ ≤ Real.exp (-(1/4:ℝ))*Real.exp (-(1/(2*u))*‖y‖^2) := mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = Real.exp (-(1/(2*u))*‖y‖^2-1/4) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr he
  unfold density
  nlinarith [mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (normalizer_pos k hb).le)]


end SingleLatticeCovering.GaussianDensity

end

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma surjective_of_smoothed_lower {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (A : Isotropization.E n →ₗ[ℝ] Isotropization.E k)
    {b : ℝ} (hb : 0 < b)
    (hlower : ∀ y : Isotropization.E k, ‖y‖=1 →
      (normalizer k b)⁻¹*Real.exp (-b) < ∫ x, density b (y-A x) ∂μ) : Function.Surjective A := by
  by_contra h
  have hr : A.range ≠ ⊤ := fun htop => h (LinearMap.range_eq_top.mp htop)
  have ho : A.rangeᗮ ≠ ⊥ := fun hbot => hr (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
  let u := ‖z‖⁻¹ • z
  have hu : ‖u‖=1 := norm_smul_inv_norm hz0
  have huo : u ∈ A.rangeᗮ := A.rangeᗮ.smul_mem _ hz
  have hfar (x : Isotropization.E n) : 1 ≤ ‖u-A x‖^2 := by
    have hh : ⟪u,A x⟫=0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp huo (A x) (LinearMap.mem_range_self _ _)
    rw [norm_sub_sq_real,hu,hh]
    nlinarith [sq_nonneg ‖A x‖]
  have hi : Integrable (fun x => density b (u-A x)) μ := by
    apply (integrable_const ((normalizer k b)⁻¹)).mono' (by
      exact ((continuous_density k b).comp (continuous_const.sub A.continuous_of_finiteDimensional)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (density_pos hb _).le]
      unfold density
      apply mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k hb).le)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _)))
  have hp (x : Isotropization.E n) : density b (u-A x) ≤ (normalizer k b)⁻¹*Real.exp (-b) := by
    unfold density
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos k hb).le)
    apply Real.exp_le_exp.mpr
    nlinarith [hfar x]
  have H := integral_mono hi (integrable_const ((normalizer k b)⁻¹*Real.exp (-b))) hp
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  exact (not_lt_of_ge H) (hlower u hu)


end SingleLatticeCovering.GaussianProjection

end

section
noncomputable section

end
end

end OAI
