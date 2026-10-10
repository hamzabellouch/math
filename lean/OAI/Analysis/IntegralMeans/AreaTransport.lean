import OAI.Analysis.IntegralMeans.BorelPairing

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

def fiberSum.{u_1, u_2} {X : Type u_1} {Y : Type u_2} (f : X → Y) (s : Set X) (u : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∑' x : {x | x ∈ s ∧ f x = y}, u x

lemma BorelBranches.fiberSum_eq.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {s : Set X} (B : BorelBranches f s) (u : X → ℝ≥0∞) (y : Y) :
    fiberSum f s u y = ∑' n, (f '' B.part n).indicator (fun y => u (B.branch n y)) y := by
  classical
  have he : {x | x ∈ s ∧ f x = y} = ⋃ n, {x | x ∈ B.part n ∧ f x = y} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [show x ∈ s ↔ x ∈ ⋃ n, B.part n from by rw [B.cover]]
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  rw [fiberSum,he,ENNReal.tsum_biUnion]
  · apply tsum_congr
    intro n
    by_cases hy : y ∈ f '' B.part n
    · have hx : {x | x ∈ B.part n ∧ f x = y} = {B.branch n y} := by
        ext x
        constructor
        · intro hx
          exact mem_singleton_iff.mpr (B.injective n hx.1 (B.right_inv n y hy).1
            (hx.2.trans (B.right_inv n y hy).2.symm))
        · rintro rfl
          exact B.right_inv n y hy
      rw [hx,tsum_singleton,indicator_of_mem hy]
    · have hx : {x | x ∈ B.part n ∧ f x = y} = ∅ := by
        exact eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx.1,hx.2⟩)
      simp [hx,hy]
  · intro n _ m _ hnm
    exact (B.disjoint hnm).mono (fun _ h => h.1) (fun _ h => h.1)

lemma BorelBranches.measurable_fiberSum.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {s : Set X} (B : BorelBranches f s) {u : X → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fiberSum f s u) := by
  have he := funext (B.fiberSum_eq u)
  rw [he]
  exact Measurable.tsum (fun n => (hu.comp (B.measurable_branch n)).indicator (B.measurable_image n))

lemma weighted_area_formula_regular {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0)
    {u : ℂ → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fiberSum f s u) ∧
    (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
      ∫⁻ y, fiberSum f s u y := by
  let B := Classical.choice (exists_borelBranches
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (exists_countable_injective_partition hs hf hreg))
  have hsub (n : ℕ) : B.part n ⊆ s := fun z hz => by rw [← B.cover]; exact mem_iUnion.mpr ⟨n,hz⟩
  have hder (n : ℕ) (z : ℂ) (hz : z ∈ B.part n) :
      HasFDerivWithinAt f (fderiv ℝ f z) (B.part n) z :=
    ((hf z (hsub n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  refine ⟨B.measurable_fiberSum hu,?_⟩
  calc
    (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
        ∑' n, ∫⁻ z in B.part n, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z := by
      conv_lhs => rw [← B.cover]
      exact lintegral_iUnion B.measurable_part B.disjoint _
    _ = ∑' n, ∫⁻ y in f '' B.part n, u (B.branch n y) := by
      apply tsum_congr
      intro n
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (B.measurable_part n) (hder n) (B.injective n)]
      apply setLIntegral_congr_fun (B.measurable_part n)
      intro z hz
      dsimp only
      rw [B.left_inv n z hz]
    _ = ∫⁻ y, fiberSum f s u y := by
      rw [funext (B.fiberSum_eq u),lintegral_tsum]
      · exact tsum_congr (fun n => (lintegral_indicator (B.measurable_image n) _).symm)
      · exact fun n => ((hu.comp (B.measurable_branch n)).indicator (B.measurable_image n)).aemeasurable

lemma fiberSum_mono_injective.{u_1, u_2} {X : Type u_1} {Y : Type u_2} {f : X → Y} {s t : Set X} {u v : X → ℝ≥0∞}
    (R : X → X) (y : Y)
    (hR : ∀ x ∈ s, f x = y → R x ∈ t ∧ f (R x) = y)
    (hinj : InjOn R {x | x ∈ s ∧ f x = y})
    (hle : ∀ x ∈ s, f x = y → u x ≤ v (R x)) :
    fiberSum f s u y ≤ fiberSum f t v y := by
  let e : {x | x ∈ s ∧ f x = y} → {x | x ∈ t ∧ f x = y} := fun x =>
    ⟨R x,hR x x.property.1 x.property.2⟩
  have hi : Injective e := fun a b h => Subtype.ext
    (hinj a.property b.property (congrArg Subtype.val h))
  exact ENNReal.summable.tsum_le_tsum_of_inj e hi (fun _ _ => zero_le)
    (fun x => hle x x.property.1 x.property.2) ENNReal.summable

lemma contDiffAt_criticalMap {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) : ContDiffAt ℝ 1 (criticalMap f k) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have hc : ContDiffAt ℝ 1 (fun w : ℂ => (w.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z Complex.imCLM.contDiff.contDiffAt
  exact (han.contDiffAt.restrict_scalars ℝ).sub
    ((contDiffAt_const.mul hc).mul (han.deriv.contDiffAt.restrict_scalars ℝ))

lemma measurableSet_halfPlane_pred (P : ℂ → Prop)
    (hP : MeasurableSet {z : halfPlane | P z}) :
    MeasurableSet {z : ℂ | z ∈ halfPlane ∧ P z} := by
  have h := isOpen_halfPlane.measurableSet.subtype_image hP
  convert h using 1
  ext z
  simp only [mem_ofPred_eq,mem_image,Subtype.exists,exists_prop]
  aesop

def jacobianRegion (g : DiskClass) (k σ : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ 0 < σ * normalizedJacobian (classFun g) k z}

lemma measurableSet_jacobianRegion (g : DiskClass) (k σ : ℝ) :
    MeasurableSet (jacobianRegion g k σ) := by
  apply measurableSet_halfPlane_pred
  exact measurableSet_lt measurable_const
    (measurable_const.mul (((continuous_class_normalizedJacobian k).comp
      (continuous_const.prodMk continuous_id)).measurable))

lemma jacobianRegion_regular (g : DiskClass) (k σ : ℝ) {z : ℂ}
    (hz : z ∈ jacobianRegion g k σ) :
    LinearMap.det (fderiv ℝ (criticalMap (classFun g) k) z).toLinearMap ≠ 0 := by
  intro hzero
  have h := hz.2
  simp only [normalizedJacobian,hzero,zero_div,mul_zero] at h
  exact lt_irrefl 0 h

def transportDensity (g : DiskClass) (β : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1)*‖reciprocalDeriv (classFun g) z‖^2)

def targetDensity (g : DiskClass) (β : ℝ) : ℂ → ℝ≥0∞ :=
  halfPlane.indicator (fun z => ENNReal.ofReal (z.im^(β-1)*‖reciprocalDeriv (classFun g) z‖^4))

attribute [local irreducible] classWeight

lemma measurable_targetDensity (g : DiskClass) (β : ℝ) : Measurable (targetDensity g β) := by
  have hc : ContinuousOn (fun z : ℂ => ENNReal.ofReal (z.im^(β-1)*‖reciprocalDeriv (classFun g) z‖^4)) halfPlane := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hm : Continuous (fun z : halfPlane => (g,z)) := continuous_const.prodMk continuous_id
    have hq : Continuous (fun z : halfPlane => classWeight g z) := continuous_classWeight.comp hm
    have hp : Continuous (fun z : halfPlane => z.val.im^(β-1)) :=
      (Complex.continuous_im.comp continuous_subtype_val).rpow_const (fun z => Or.inl (ne_of_gt z.property))
    convert ENNReal.continuous_ofReal.comp (hp.mul (hq.pow 2)) using 1
    funext z
    simp only [domRestrict_apply,Function.comp_apply,Pi.mul_apply,Pi.pow_apply,classWeight,← pow_mul]
  exact hc.measurable_piecewise continuousOn_const isOpen_halfPlane.measurableSet

lemma transportDensity_jacobian (g : DiskClass) (β k σ : ℝ) (hσ : |σ| = 1)
    {z : ℂ} (hz : z ∈ jacobianRegion g k σ) :
    transportDensity g β z * ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ (criticalMap (classFun g) k) z).toLinearMap| * targetDensity g β z := by
  have hD : 0 < ‖deriv (classFun g) z‖ := norm_pos_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz.1)
  have habs : |normalizedJacobian (classFun g) k z| = σ * normalizedJacobian (classFun g) k z := by
    rw [← one_mul |normalizedJacobian (classFun g) k z|,← hσ,← abs_mul,abs_of_pos hz.2]
  have hdet : |LinearMap.det (fderiv ℝ (criticalMap (classFun g) k) z).toLinearMap| =
      ‖deriv (classFun g) z‖^2 * (σ * normalizedJacobian (classFun g) k z) := by
    rw [← habs,normalizedJacobian,abs_div,abs_pow,abs_norm]
    field_simp
  rw [transportDensity,targetDensity,indicator_of_mem hz.1,hdet]
  simp only [reciprocalDeriv,norm_inv]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hz.2.le)]
  congr 1
  field_simp

lemma transport_area (g : DiskClass) (β k σ : ℝ) (hσ : |σ| = 1)
    {h : ℂ → ℝ≥0∞} (hm : Measurable h) :
    (∫⁻ z in halfPlane, transportDensity g β z *
      ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) * h z) =
    ∫⁻ ξ, fiberSum (criticalMap (classFun g) k) (jacobianRegion g k σ)
      (fun z => targetDensity g β z*h z) ξ := by
  have hs := measurableSet_jacobianRegion g k σ
  have he := (weighted_area_formula_regular hs
    (fun z hz => contDiffAt_criticalMap (classFun_schlicht g).1 hz.1 k)
    (fun z hz => jacobianRegion_regular g k σ hz)
    ((measurable_targetDensity g β).mul hm)).2
  refine Eq.trans ?_ he
  have hzero : (fun z => transportDensity g β z *
      ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) * h z) =ᶠ[ae (volume.restrict halfPlane)]
      (jacobianRegion g k σ).indicator (fun z => transportDensity g β z *
        ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) * h z) := by
    filter_upwards [ae_restrict_mem isOpen_halfPlane.measurableSet] with z hz
    by_cases hj : 0 < σ * normalizedJacobian (classFun g) k z
    · rw [indicator_of_mem (show z ∈ jacobianRegion g k σ from ⟨hz,hj⟩)]
    · rw [indicator_of_notMem (show z ∉ jacobianRegion g k σ from fun h => hj h.2),
        ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hj),mul_zero,zero_mul]
  rw [lintegral_congr_ae hzero,lintegral_indicator hs,Measure.restrict_restrict hs]
  have hinter : jacobianRegion g k σ ∩ halfPlane = jacobianRegion g k σ :=
    inter_eq_left.mpr (fun z hz => hz.1)
  rw [hinter]
  apply setLIntegral_congr_fun hs
  intro z hz
  dsimp only
  rw [transportDensity_jacobian g β k σ hσ hz,mul_assoc]
  rfl

lemma targetDensity_eq_height (g : DiskClass) {β k : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) {z : ℂ} (hz : z ∈ halfPlane) :
    targetDensity g β z = ENNReal.ofReal ((criticalHeight (classFun g) k z/k)^4) := by
  rw [targetDensity,indicator_of_mem hz,criticalHeight,hb,mul_comm (4 : ℝ),Real.rpow_mul hz.le]
  congr 1
  simp only [Real.rpow_ofNat]
  field_simp

lemma targetDensity_le_pair (g : DiskClass) {β k : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) {z : ℂ} (hz : z ∈ halfPlane)
    (hJ : 0 < normalizedJacobian (classFun g) k z)
    (hg : GoodPair (classFun g) k (criticalMap (classFun g) k z)) :
    targetDensity g β z ≤ targetDensity g β (criticalPair (classFun g) k z) := by
  have hs := criticalPair_spec (classFun_schlicht g).1 hk hz hJ hg
  rw [targetDensity_eq_height g hk hb hz,targetDensity_eq_height g hk hb hs.1]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  · exact div_nonneg (criticalHeight_pos (classFun_schlicht g).1 hk hz).le hk.le
  · exact hs.2.2.2

end Brennan

end

end OAI
