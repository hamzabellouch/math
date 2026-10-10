import OAI.Analysis.IntegralMeans.InverseDensity

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
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma lintegral_Icc_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ y in Icc a b, ENNReal.ofReal y⁻¹) = ENNReal.ofReal (Real.log (b/a)) := by
  have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (ha.trans_le hy.1))
  have hi : IntegrableOn (fun y : ℝ => y⁻¹) (Icc a b) volume := hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,integral_inv_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)

lemma lintegral_transportBox_inv {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) =
      ENNReal.ofReal (2*R*Real.log (b/a)) := by
  have he : Complex.measurableEquivRealProd ⁻¹' (Icc (-R) R ×ˢ Icc a b) = transportBox R a b := by
    ext z
    simp only [Complex.measurableEquivRealProd_apply,mem_preimage,mem_prod,mem_Icc,transportBox,mem_ofPred_eq,abs_le]
  have hprod := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => ENNReal.ofReal p.2⁻¹)
    (Icc (-R) R ×ˢ Icc a b)
  rw [he] at hprod
  change (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) = _ at hprod
  rw [hprod,show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setLIntegral_prod _ (by fun_prop)]
  dsimp only
  rw [lintegral_Icc_inv ha hab,
    lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
  rw [show R - -R = 2*R from by ring,mul_comm,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]

def rootJac (k σ : ℝ) (g : DiskClass) : ℝ≥0∞ :=
  ENNReal.ofReal (σ * normalizedJacobian (classFun g) k Complex.I)

lemma measurable_rootJac (k σ : ℝ) : Measurable (rootJac k σ) := by
  exact (measurable_const.mul ((continuous_class_normalizedJacobian k).comp
    (continuous_id.prodMk (continuous_const (y := halfOne)))).measurable).ennreal_ofReal

lemma rootJac_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (σ : ℝ) (z : halfPlane) :
    rootJac k σ (rerootClass g z) = ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) := by
  rw [rootJac,class_normalizedJacobian_root g hk z]

def rootWindow (k N : ℝ) : Set DiskClass := {g | (g,halfOne) ∈ transportWindow k N}

def windowTest (k N : ℝ) : DiskClass → ℝ≥0∞ := (rootWindow k N).indicator (rootJac k 1)

lemma measurableSet_rootWindow {k : ℝ} (hk : 0 < k) (N : ℝ) : MeasurableSet (rootWindow k N) :=
  (measurableSet_transportWindow hk N).preimage (measurable_id.prodMk measurable_const)

lemma measurable_windowTest {k : ℝ} (hk : 0 < k) (N : ℝ) : Measurable (windowTest k N) :=
  (measurable_rootJac k 1).indicator (measurableSet_rootWindow hk N)

lemma averagedDensity_window (g : DiskClass) (β : ℝ) {k : ℝ} (hk : 0 < k) (N : ℝ) (z : halfPlane) :
    averagedDensity β (windowTest k N) (g,z) =
      transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
        (transportSlice g k N).indicator 1 z := by
  rw [averagedDensity_of_mem,windowTest]
  have he : rerootClass g z ∈ rootWindow k N ↔ z.val ∈ transportSlice g k N :=
    (transportWindow_root g hk N z).trans (transportSlice_iff g k N z).symm
  by_cases hz : z.val ∈ transportSlice g k N
  · rw [indicator_of_mem (he.mpr hz),rootJac_reroot g hk 1 z,one_mul,indicator_of_mem hz]
    simp
  · rw [indicator_of_notMem (fun h => hz (he.mp h)),indicator_of_notMem hz]
    simp

def rootException (k : ℝ) : Set DiskClass :=
  {g | ¬GoodPair (classFun g) k (criticalMap (classFun g) k Complex.I)}

def exceptionTest (k : ℝ) : DiskClass → ℝ≥0∞ := (rootException k).indicator (rootJac k 1)

lemma measurableSet_rootException {k : ℝ} (hk : 0 < k) : MeasurableSet (rootException k) := by
  have hm : Measurable (fun g : DiskClass => (g,criticalMap (classFun g) k Complex.I)) :=
    continuous_id.measurable.prodMk (((continuous_class_criticalMap k).comp
      (continuous_id.prodMk (continuous_const (y := halfOne)))).measurable)
  exact ((measurableSet_class_goodPairs hk.le).preimage hm).compl

lemma measurable_exceptionTest {k : ℝ} (hk : 0 < k) : Measurable (exceptionTest k) :=
  (measurable_rootJac k 1).indicator (measurableSet_rootException hk)

lemma averagedDensity_exception (g : DiskClass) (β : ℝ) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    averagedDensity β (exceptionTest k) (g,z) =
      transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
        {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator 1 z := by
  rw [averagedDensity_of_mem,exceptionTest]
  have he := class_goodPair_root g hk z
  by_cases hg : GoodPair (classFun g) k (criticalMap (classFun g) k z)
  · rw [indicator_of_notMem (show rerootClass g z ∉ rootException k from fun h => h (he.mpr hg)),
      indicator_of_notMem (show z.val ∉ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} from fun h => h.2 hg)]
    simp
  · rw [indicator_of_mem (show rerootClass g z ∈ rootException k from fun h => hg (he.mp h)),
      rootJac_reroot g hk 1 z,one_mul,indicator_of_mem (show z.val ∈ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} from ⟨z.property,hg⟩)]
    simp

lemma exceptionTest_integral_zero (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {k : ℝ} (hk : 0 < k)
    (hg : ∀ᵐ g ∂(P : Measure DiskClass), ∀ᵐ ξ : ℂ, GoodPair (classFun g) k ξ) :
    (∫⁻ g, exceptionTest k g ∂(P : Measure DiskClass)) = 0 := by
  apply root_test_zero_of_averaging P β hP (measurable_exceptionTest hk)
  filter_upwards [hg] with g hg
  refine Eq.trans ?_ (exceptional_transport_zero g (β := β) hk hg)
  apply setLIntegral_congr_fun isOpen_halfPlane.measurableSet
  intro z hz
  exact averagedDensity_exception g β hk ⟨z,hz⟩

lemma averagedDensity_box (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ)
    {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ g, ∫⁻ z in transportBox R a b, averagedDensity β Φ (g,z) ∂volume ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (2*R*Real.log (b/a)) * ∫⁻ g, Φ g ∂(P : Measure DiskClass) := by
  rw [lintegral_lintegral_swap (f := fun g z => averagedDensity β Φ (g,z)) (μ := (P : Measure DiskClass)) (ν := volume.restrict (transportBox R a b)) (measurable_averagedDensity β hΦ).aemeasurable]
  have he : (∫⁻ z in transportBox R a b, ∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) =
      ∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹ * ∫⁻ g, Φ g ∂(P : Measure DiskClass) := by
    apply setLIntegral_congr_fun (measurableSet_transportBox R a b)
    intro z hz
    exact weighted_averagedDensity P β hP hΦ ⟨z,ha.trans_le hz.2.1⟩
  rw [he,lintegral_mul_const _ (by fun_prop),lintegral_transportBox_inv hR ha hab]

lemma setLIntegral_mul_indicator_one {S T : Set ℂ} (hS : MeasurableSet S) (hST : S ⊆ T)
    (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in T, f z * S.indicator 1 z) = ∫⁻ z in S, f z := by
  have he : (fun z => f z * S.indicator 1 z) = S.indicator f := by
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [he,setLIntegral_indicator hS,inter_eq_left.mpr hST]

lemma transport_box_averaged (g : DiskClass) {β k N R Y : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) (hN : 1 ≤ N) :
    (∫⁻ z in transportBox R 1 Y, averagedDensity β (windowTest k N) (g,z)) ≤
      ∫⁻ z in transportBox (R+N*Y) (1/N) (N*Y), averagedDensity β (rootJac k (-1)) (g,z) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hB : transportBox R 1 Y ⊆ halfPlane := fun z hz => lt_of_lt_of_le zero_lt_one hz.2.1
  have hB' : transportBox (R+N*Y) (1/N) (N*Y) ⊆ halfPlane := fun z hz =>
    lt_of_lt_of_le (one_div_pos.mpr hn) hz.2.1
  have he := transport_box g hk hb hN (R := R) (Y := Y)
  have hp : (∫⁻ z in halfPlane, transportDensity g β z*ENNReal.ofReal (normalizedJacobian (classFun g) k z)*
      (transportSlice g k N ∩ transportBox R 1 Y).indicator 1 z) =
      ∫⁻ z in transportBox R 1 Y, averagedDensity β (windowTest k N) (g,z) := by
    have hid : (fun z => transportDensity g β z*ENNReal.ofReal (normalizedJacobian (classFun g) k z)*
      (transportSlice g k N ∩ transportBox R 1 Y).indicator 1 z) =
      fun z => (transportDensity g β z*ENNReal.ofReal (normalizedJacobian (classFun g) k z)*
        (transportSlice g k N).indicator 1 z)*(transportBox R 1 Y).indicator 1 z := by
      funext z
      rw [inter_indicator_one]
      simp only [Pi.mul_apply,mul_assoc]
    rw [hid,setLIntegral_mul_indicator_one (measurableSet_transportBox _ _ _) hB]
    apply setLIntegral_congr_fun (measurableSet_transportBox _ _ _)
    intro z hz
    exact (averagedDensity_window g β hk N ⟨z,hB hz⟩).symm
  have hm : (∫⁻ z in halfPlane, transportDensity g β z*ENNReal.ofReal (-normalizedJacobian (classFun g) k z)*
      (transportBox (R+N*Y) (1/N) (N*Y)).indicator 1 z) =
      ∫⁻ z in transportBox (R+N*Y) (1/N) (N*Y), averagedDensity β (rootJac k (-1)) (g,z) := by
    rw [setLIntegral_mul_indicator_one (measurableSet_transportBox _ _ _) hB']
    apply setLIntegral_congr_fun (measurableSet_transportBox _ _ _)
    intro z hz
    symm
    exact (averagedDensity_of_mem β (rootJac k (-1)) g ⟨z,hB' hz⟩).trans
      (congrArg (transportDensity g β z * ·) (by simpa only [neg_one_mul] using rootJac_reroot g hk (-1) ⟨z,hB' hz⟩))
  exact hp.symm.trans_le (he.trans_eq hm)

lemma expected_transport_box (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {k N R Y : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) (hN : 1 ≤ N) (hR : 0 ≤ R) (hY : 1 ≤ Y) :
    ENNReal.ofReal (2*R*Real.log Y) * (∫⁻ g, windowTest k N g ∂(P : Measure DiskClass)) ≤
      ENNReal.ofReal (2*(R+N*Y)*Real.log (N^2*Y)) * (∫⁻ g, rootJac k (-1) g ∂(P : Measure DiskClass)) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hny : 1 / N ≤ N*Y := by
    rw [div_le_iff₀ hn]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY hn.le) hn.le
    nlinarith [sq_nonneg (N-1)]
  have hp := averagedDensity_box P β hP (measurable_windowTest hk N) hR zero_lt_one hY
  have hm := averagedDensity_box P β hP (measurable_rootJac k (-1))
    (add_nonneg hR (mul_nonneg hn.le (zero_le_one.trans hY))) (one_div_pos.mpr hn) hny
  simp only [div_one] at hp
  rw [show N*Y/(1/N) = N^2*Y from by field_simp] at hm
  rw [← hp,← hm]
  exact lintegral_mono (fun g => transport_box_averaged g hk hb hN)

lemma transport_ratio_tendsto (N : ℝ) :
    Tendsto (fun Y : ℝ => (1+N/Y)*(1+2*Real.log N/Real.log Y)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun Y : ℝ => N/Y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun Y : ℝ => 2*Real.log N/Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h1).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h2)

lemma transport_box_limit {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ Y : ℝ, 1 < Y →
      ENNReal.ofReal (2*Y^2*Real.log Y)*A ≤
        ENNReal.ofReal (2*(Y^2+N*Y)*Real.log (N^2*Y))*B) : A ≤ B := by
  have hn : 0 < N := zero_lt_one.trans_le hN
  have hineq : ∀ Y : ℝ, 1 < Y → A.toReal ≤ (1+N/Y)*(1+2*Real.log N/Real.log Y)*B.toReal := by
    intro Y hY
    have hy : 0 < Y := zero_lt_one.trans hY
    have hl : 0 < Real.log Y := Real.log_pos hY
    have hny : 1 < N^2*Y := by nlinarith [sq_nonneg (N-1)]
    have hlny : 0 ≤ Real.log (N^2*Y) := Real.log_nonneg hny.le
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) (h Y hY)
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Y^2*Real.log Y),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(Y^2+N*Y)*Real.log (N^2*Y))] at hb
    have hlog : Real.log (N^2*Y) = 2*Real.log N + Real.log Y := by
      rw [Real.log_mul (by positivity) (ne_of_gt hy),Real.log_pow]
      norm_num
    rw [hlog] at hb
    apply (mul_le_mul_iff_right₀ (show 0 < 2*Y^2*Real.log Y by positivity)).mp
    calc
      _ ≤ 2*(Y^2+N*Y)*(2*Real.log N+Real.log Y)*B.toReal := hb
      _ = _ := by field_simp; ring
  apply (ENNReal.toReal_le_toReal hA hB).mp
  have ht := (transport_ratio_tendsto N).mul_const B.toReal
  simp only [one_mul] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  exact hineq Y hY

lemma rootJac_integral_lt_top (P : ProbabilityMeasure DiskClass) (k σ : ℝ) :
    (∫⁻ g, rootJac k σ g ∂(P : Measure DiskClass)) < ∞ := by
  have hc : Continuous (fun g : DiskClass => σ*normalizedJacobian (classFun g) k Complex.I) :=
    continuous_const.mul ((continuous_class_normalizedJacobian k).comp
      (continuous_id.prodMk (continuous_const (y := halfOne))))
  have hi : Integrable (fun g : DiskClass => σ*normalizedJacobian (classFun g) k Complex.I) (P : Measure DiskClass) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply lt_of_le_of_lt (lintegral_mono (fun g => ENNReal.ofReal_le_ofReal (le_abs_self _)))
  exact (hasFiniteIntegral_iff_norm _).mp hi.2

lemma windowTest_le (k N : ℝ) (g : DiskClass) : windowTest k N g ≤ rootJac k 1 g := by
  by_cases hg : g ∈ rootWindow k N <;> simp [windowTest,indicator_of_mem,indicator_of_notMem,hg]

lemma windowTest_integral_lt_top (P : ProbabilityMeasure DiskClass) (k N : ℝ) :
    (∫⁻ g, windowTest k N g ∂(P : Measure DiskClass)) < ∞ :=
  (lintegral_mono (windowTest_le k N)).trans_lt (rootJac_integral_lt_top P k 1)

lemma windowTest_mono {k : ℝ} (hk : 0 < k) :
    Monotone (fun n : ℕ => windowTest k (n+1)) := by
  intro n m hnm g
  have hs : rootWindow k (n+1) ⊆ rootWindow k (m+1) :=
    fun g hg => transportWindow_mono hk (by exact_mod_cast Nat.add_le_add_right hnm 1) hg
  by_cases hg : g ∈ rootWindow k (n+1)
  · simp only [windowTest,indicator_of_mem hg,indicator_of_mem (hs hg),le_refl]
  · simp only [windowTest,indicator_of_notMem hg]
    exact bot_le

lemma iSup_windowTest {k : ℝ} (hk : 0 < k) (g : DiskClass) :
    (⨆ n : ℕ, windowTest k (n+1) g) =
      {g : DiskClass | (g,halfOne) ∈ pairingDomain k}.indicator (rootJac k 1) g := by
  by_cases hg : (g,halfOne) ∈ pairingDomain k
  · rw [indicator_of_mem (show g ∈ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from hg)]
    apply le_antisymm (iSup_le (fun n : ℕ => windowTest_le k (n+1) g))
    have hu : (g,halfOne) ∈ ⋃ n : ℕ, transportWindow k (n+1) := (iUnion_transportWindow hk).symm ▸ hg
    obtain ⟨n,hn⟩ := mem_iUnion.mp hu
    have he : windowTest k (n+1) g = rootJac k 1 g := indicator_of_mem (show g ∈ rootWindow k (n+1) from hn) _
    exact he ▸ le_iSup (fun n : ℕ => windowTest k (n+1) g) n
  · rw [indicator_of_notMem (show g ∉ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from hg)]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro n
    apply le_of_eq
    apply indicator_of_notMem
    intro hn
    exact hg hn.1

lemma rootJac_eq_window_exception {k : ℝ} (hk : 0 < k) (g : DiskClass) :
    rootJac k 1 g = (⨆ n : ℕ, windowTest k (n+1) g) + exceptionTest k g := by
  rw [iSup_windowTest hk g,exceptionTest]
  by_cases hG : GoodPair (classFun g) k (criticalMap (classFun g) k Complex.I)
  · rw [indicator_of_notMem (show g ∉ rootException k from fun h => h hG),add_zero]
    by_cases hJ : 0 < normalizedJacobian (classFun g) k Complex.I
    · exact (indicator_of_mem (show g ∈ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from ⟨hJ,hG⟩) _).symm
    · rw [indicator_of_notMem (show g ∉ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from fun h => hJ h.1)]
      exact ENNReal.ofReal_eq_zero.mpr (by simpa only [one_mul] using le_of_not_gt hJ)
  · rw [indicator_of_mem (show g ∈ rootException k from hG),indicator_of_notMem (show g ∉ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from fun h => hG h.2),zero_add]

lemma jacobian_positive_le_negative (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {k : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1))
    (hg : ∀ᵐ g ∂(P : Measure DiskClass), ∀ᵐ ξ : ℂ, GoodPair (classFun g) k ξ) :
    (∫⁻ g, rootJac k 1 g ∂(P : Measure DiskClass)) ≤ ∫⁻ g, rootJac k (-1) g ∂(P : Measure DiskClass) := by
  have hw (n : ℕ) : (∫⁻ g, windowTest k (n+1) g ∂(P : Measure DiskClass)) ≤ ∫⁻ g, rootJac k (-1) g ∂(P : Measure DiskClass) := by
    apply transport_box_limit (N := (n:ℝ)+1) (windowTest_integral_lt_top P k (n+1)).ne (rootJac_integral_lt_top P k (-1)).ne
      (by have h := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n+1)
    intro Y hY
    exact expected_transport_box P β hP hk hb (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) (sq_nonneg Y) hY.le
  have he (g : DiskClass) := rootJac_eq_window_exception hk g
  simp_rw [he]
  rw [lintegral_add_left (Measurable.iSup (fun n : ℕ => measurable_windowTest hk (n+1))),
    exceptionTest_integral_zero P β hP hk hg,add_zero,lintegral_iSup (fun n : ℕ => measurable_windowTest hk (n+1)) (windowTest_mono hk)]
  exact iSup_le hw

end Brennan

end

end OAI
