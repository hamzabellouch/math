import OAI.Analysis.StrictMeans.FiberSum

namespace OAI

section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

lemma chart_measurable_fiberSum {G : ℂ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = G) {s : Set ℂ} (hs : MeasurableSet s) (hse : s ⊆ e.source)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) : Measurable (fiberSum G s h) := by
  classical
  have him : MeasurableSet (G '' s) := by
    rw [← he]
    exact hs.image_of_continuousOn_injOn (e.continuousOn.mono hse) (e.injOn.mono hse)
  let φ := e.target.piecewise e.symm (fun _ => 0)
  have hφ : Measurable φ := e.continuousOn_symm.measurable_piecewise
    continuousOn_const e.open_target.measurableSet
  have hinv : ∀ z ∈ s, φ (G z) = z := by
    intro z hz
    rw [show G z = e z from congrFun he.symm z]
    simp only [φ, piecewise_eq_of_mem _ _ _ (e.map_source (hse hz)), e.left_inv (hse hz)]
  rw [fiberSum_eq_indicator_inverse (he ▸ e.injOn.mono hse) h φ hinv]
  exact (hh.comp hφ).indicator him

lemma chart_area_formula {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = G) {s : Set ℂ} (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hse : s ⊆ e.source) (h : ℂ → ℝ≥0∞) :
    ∫⁻ ξ, fiberSum G s h ξ =
      ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| * h z := by
  classical
  have hinv : ∀ z ∈ s, e.symm (G z) = z := by
    intro z hz
    rw [← he]
    exact e.left_inv (hse hz)
  have hi : InjOn G s := he ▸ e.injOn.mono hse
  have hf : ∀ z ∈ s, HasFDerivWithinAt G (fderiv ℝ G z) s z := by
    intro z hz
    exact ((hG.contDiffAt (hU.mem_nhds (hsU hz))).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have him := measurable_image_of_fderivWithin hs hf hi
  rw [fiberSum_eq_indicator_inverse hi h e.symm hinv,lintegral_indicator him]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf hi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hs] with z hz
  rw [hinv z hz]

lemma regular_area_formula {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {s : Set ℂ} (hs : MeasurableSet s)
    (hsR : s ⊆ {z ∈ U | (fderiv ℝ G z).det ≠ 0})
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    Measurable (fiberSum G s h) ∧
      ∫⁻ ξ, fiberSum G s h ξ = ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| * h z := by
  classical
  obtain ⟨C,hC,hchart,hcov⟩ := countable_regular_inverse_charts hU hG
  by_cases hn : C.Nonempty
  · obtain ⟨e,he⟩ := hC.exists_eq_range hn
    have hem (n : ℕ) : e n ∈ C := he ▸ mem_range_self n
    let A (n : ℕ) := s ∩ (e n).source
    let B := disjointed A
    have hmA (n : ℕ) : MeasurableSet (A n) := hs.inter (e n).open_source.measurableSet
    have hmB (n : ℕ) : MeasurableSet (B n) := MeasurableSet.disjointed hmA n
    have hbA (n : ℕ) : B n ⊆ A n := disjointed_le A n
    have hbE (n : ℕ) : B n ⊆ (e n).source := (hbA n).trans inter_subset_right
    have hbS (n : ℕ) : B n ⊆ s := (hbA n).trans inter_subset_left
    have hbs : (⋃ n, B n) = s := by
      rw [iUnion_disjointed]
      apply Subset.antisymm
      · exact iUnion_subset (fun n => inter_subset_left)
      · intro z hz
        obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp (hcov (hsR hz))
        obtain ⟨n,rfl⟩ := he ▸ hc
        exact mem_iUnion.mpr ⟨n,hz,hzc⟩
    have hmb (n : ℕ) : Measurable (fiberSum G (B n) h) :=
      chart_measurable_fiberSum (e n) (hchart _ (hem n)).1 (hmB n) (hbE n) hh
    have heq : fiberSum G s h = fun ξ => ∑' n, fiberSum G (B n) h ξ := by
      funext ξ
      rw [← hbs]
      exact fiberSum_iUnion G B h (disjoint_disjointed A) ξ
    refine ⟨heq ▸ .tsum hmb,?_⟩
    rw [heq,lintegral_tsum (fun n => (hmb n).aemeasurable)]
    simp_rw [chart_area_formula hU hG _ (hchart _ (hem _)).1 (hmB _)
      ((hbS _).trans (fun z hz => (hsR hz).1)) (hbE _)]
    rw [← lintegral_iUnion (fun n => hmB n) (disjoint_disjointed A),hbs]
  · have hs0 : s = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨e,he,_⟩ := mem_iUnion₂.mp (hcov (hsR hz))
      exact hn ⟨e,he⟩
    subst s
    have he : fiberSum G ∅ h = 0 := by ext ξ; simp [fiberSum]
    rw [he]
    exact ⟨measurable_const, by simp⟩

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def unsignedTargetWeight (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1) * ‖halfPlaneQ f z‖^3)

def jacobianPart (k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) : ℝ :=
  max (if positive then jacobianExpression k (halfPlaneFunction f) z else
    -jacobianExpression k (halfPlaneFunction f) z) 0

def sourceMassDensity (β k : ℝ) (f : DiskFamily) (positive : Bool)
    (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1) * ‖halfPlaneQ f z‖ * jacobianPart k f positive z)

def signedJacobianLocus (k : ℝ) (f : DiskFamily) (positive : Bool) : Set ℂ :=
  {z | 0 < z.im ∧ if positive then 0 < jacobianExpression k (halfPlaneFunction f) z
    else jacobianExpression k (halfPlaneFunction f) z < 0}

lemma continuous_unsignedTargetWeight (β : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => unsignedTargetWeight β p.1 p.2) := by
  exact ENNReal.continuous_ofReal.comp (((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
    (fun p => Or.inl p.2.im_ne_zero)).mul (continuous_halfPlaneQ.norm.pow 3))

lemma continuous_jacobianPart (k : ℝ) (positive : Bool) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => jacobianPart k p.1 positive p.2) := by
  cases positive
  · exact (continuous_jacobianExpression_upper k).neg.max continuous_const
  · exact (continuous_jacobianExpression_upper k).max continuous_const

lemma continuous_sourceMassDensity (β k : ℝ) (positive : Bool) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => sourceMassDensity β k p.1 positive p.2) := by
  exact ENNReal.continuous_ofReal.comp ((((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
    (fun p => Or.inl p.2.im_ne_zero)).mul continuous_halfPlaneQ.norm).mul
      (continuous_jacobianPart k positive))

lemma measurableSet_signedJacobianLocus (k : ℝ) (f : DiskFamily) (positive : Bool) :
    MeasurableSet (signedJacobianLocus k f positive) := by
  have hc : Continuous (fun z : UpperHalfPlane => (f,z)) := continuous_const.prodMk continuous_id
  have hm := (continuous_jacobianExpression_upper k).comp hc
  have hs : MeasurableSet {z : UpperHalfPlane | if positive then
      0 < jacobianExpression k (halfPlaneFunction f) z else
      jacobianExpression k (halfPlaneFunction f) z < 0} := by
    cases positive
    · change MeasurableSet {z : UpperHalfPlane | jacobianExpression k (halfPlaneFunction f) z < 0}
      exact measurableSet_lt hm.measurable measurable_const
    · change MeasurableSet {z : UpperHalfPlane | 0 < jacobianExpression k (halfPlaneFunction f) z}
      exact measurableSet_lt measurable_const hm.measurable
  have he : signedJacobianLocus k f positive = UpperHalfPlane.coe '' {z : UpperHalfPlane | if positive then
      0 < jacobianExpression k (halfPlaneFunction f) z else
      jacobianExpression k (halfPlaneFunction f) z < 0} := by
    ext z
    constructor
    · intro hz
      refine ⟨⟨z,hz.1⟩,?_,rfl⟩
      exact hz.2
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.im_pos,hw⟩
  rw [he]
  exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs

lemma criticalMap_det_eq (k : ℝ) (hk : k ≠ 0) (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det =
      ‖deriv (halfPlaneFunction f) z‖^2 * jacobianExpression k (halfPlaneFunction f) z := by
  have ha := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have he := normalizedJacobian_eq hk ha.differentiableAt ha.deriv.differentiableAt
    (halfPlaneFunction_deriv_ne_zero f hz)
  exact (div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (halfPlaneFunction_deriv_ne_zero f hz)))).mp he |>.trans (mul_comm _ _)

lemma sourceMassDensity_eq_targetWeight_det {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (positive : Bool) {z : ℂ} (hz : z ∈ signedJacobianLocus k f positive) :
    sourceMassDensity β k f positive ⟨z,hz.1⟩ =
      ENNReal.ofReal |(fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det| *
        unsignedTargetWeight β f ⟨z,hz.1⟩ := by
  have hJ : jacobianPart k f positive ⟨z,hz.1⟩ = |jacobianExpression k (halfPlaneFunction f) z| := by
    cases positive
    · simp only [signedJacobianLocus,Bool.false_eq_true,↓reduceIte,mem_ofPred_eq] at hz
      simp only [jacobianPart,Bool.false_eq_true,↓reduceIte,max_eq_left (neg_nonneg.mpr hz.2.le),
        abs_of_neg hz.2]
    · simp only [signedJacobianLocus,↓reduceIte,mem_ofPred_eq] at hz
      simp only [jacobianPart,↓reduceIte,max_eq_left hz.2.le,abs_of_pos hz.2]
  have hd : ‖deriv (halfPlaneFunction f) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (halfPlaneFunction_deriv_ne_zero f hz.1)
  rw [sourceMassDensity,unsignedTargetWeight,hJ,criticalMap_det_eq k hk f hz.1,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [halfPlaneQ,norm_inv,abs_mul,abs_pow,abs_norm]
  field_simp

lemma sourceMassDensity_zero_of_not_sign {β k : ℝ} (f : DiskFamily) (positive : Bool)
    (z : UpperHalfPlane) (hz : (z:ℂ) ∉ signedJacobianLocus k f positive) :
    sourceMassDensity β k f positive z = 0 := by
  have hp : jacobianPart k f positive z = 0 := by
    cases positive
    · have hJ : 0 ≤ jacobianExpression k (halfPlaneFunction f) z := by
        simpa only [signedJacobianLocus,mem_ofPred_eq,Bool.false_eq_true,↓reduceIte,
          UpperHalfPlane.coe_im, and_iff_right z.im_pos,not_lt] using hz
      exact max_eq_right (neg_nonpos.mpr hJ)
    · have hJ : jacobianExpression k (halfPlaneFunction f) z ≤ 0 := by
        simpa only [signedJacobianLocus,mem_ofPred_eq,↓reduceIte,
          UpperHalfPlane.coe_im, and_iff_right z.im_pos,not_lt] using hz
      exact max_eq_right hJ
  simp [sourceMassDensity,hp]

lemma source_area_formula {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily) (positive : Bool)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z in {z : ℂ | 0 < z.im}, h z * sourceMassDensity β k f positive (halfPlaneProjection z)) =
      ∫⁻ ξ, fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f positive)
        (fun z => h z * unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  have hreg : signedJacobianLocus k f positive ⊆
      {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0} := by
    intro z hz
    refine ⟨hz.1, (not_congr (jacobianExpression_zero_iff k hk f hz.1)).mp ?_⟩
    cases positive
    · exact ne_of_lt hz.2
    · exact ne_of_gt hz.2
  have hG : ContDiffOn ℝ 1 (criticalMap k (halfPlaneFunction f)) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (criticalMap_contDiffAt k f hz).contDiffWithinAt.of_le (by norm_num)
  have ht : Measurable (fun z => h z * unsignedTargetWeight β f (halfPlaneProjection z)) := hh.mul
    ((continuous_unsignedTargetWeight β).measurable.comp (measurable_const.prodMk measurable_halfPlaneProjection))
  rw [(regular_area_formula isOpen_halfPlane hG (measurableSet_signedJacobianLocus k f positive) hreg ht).2]
  have he : (∫⁻ z in signedJacobianLocus k f positive,
      ENNReal.ofReal |(fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det| *
        (h z * unsignedTargetWeight β f (halfPlaneProjection z))) =
      ∫⁻ z in signedJacobianLocus k f positive,
        h z * sourceMassDensity β k f positive (halfPlaneProjection z) := by
    apply setLIntegral_congr_fun (measurableSet_signedJacobianLocus k f positive)
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz.1,sourceMassDensity_eq_targetWeight_det hk f positive hz]
    ring
  rw [he,← lintegral_indicator (measurableSet_signedJacobianLocus k f positive),
    ← lintegral_indicator isOpen_halfPlane.measurableSet]
  apply lintegral_congr
  intro z
  by_cases hz : 0 < z.im
  · rw [indicator_of_mem (show z ∈ {z : ℂ | 0 < z.im} from hz)]
    by_cases hs : z ∈ signedJacobianLocus k f positive
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs,halfPlaneProjection_of_pos hz,
        sourceMassDensity_zero_of_not_sign f positive ⟨z,hz⟩ hs,mul_zero]
  · rw [indicator_of_notMem (show z ∉ {z : ℂ | 0 < z.im} from hz),
      indicator_of_notMem (show z ∉ signedJacobianLocus k f positive from fun hs => hz hs.1)]

end
end StrictInverseFirstPower

end

end OAI
