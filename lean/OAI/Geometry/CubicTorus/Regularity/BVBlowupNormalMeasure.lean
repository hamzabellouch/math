import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVC1Patch

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

instance finiteMeasure_cover_closedBall (a : Cover) (R : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.closedBall a R)) :=
  isFiniteMeasure_restrict.mpr Metric.isBounded_closedBall.measure_lt_top.ne

lemma blowupCharacteristic_translation_density {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) {r : ℝ} (hr : 0 < r) {R : ℝ} (hR : 0 ≤ R)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {A : ℝ} (hA : 0 ≤ A)
    (harea : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap c) (r*(R+2))) ≤ A*(r*(R+2))^2)
    (y : Cover) (hy : ‖y‖ ≤ 1) :
    (∫ x in Metric.ball (0 : Cover) R,
      |blowupCharacteristic E c r (x-y)-blowupCharacteristic E c r x|) ≤
      ‖y‖ * (A*(R+2)^2) := by
  have hq : ‖quotientMap (r • y)‖ ≤ r*‖y‖ := by
    simpa only [norm_smul,Real.norm_of_nonneg hr.le] using norm_quotientMap_le (r • y)
  have hqr : ‖quotientMap (r • y)‖ ≤ r :=
    hq.trans (by simpa using mul_le_mul_of_nonneg_left hy hr.le)
  have hb : r*R+r+‖quotientMap (r • y)‖ ≤ r*(R+2) := by nlinarith
  have hm := (measureReal_mono (μ := (spatialNormalMeasure μ : Measure Torus))
    (Metric.ball_subset_ball hb)).trans harea
  have h := (blowupCharacteristic_translation_bound hE hμ c hr R hr hc y).trans
    (mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) 3) (norm_nonneg _)))
  have h' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq (pow_nonneg (inv_nonneg.mpr hr.le) 3))
    (mul_nonneg hA (sq_nonneg (r*(R+2))))
  apply h.trans (h'.trans_eq _)
  field_simp

theorem totallyBounded_blowupCharacteristic {ι : Type*} {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) (r : ι → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 0 < R)
    (hc : ∀ i, Metric.ball c (r i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {A : ℝ} (hA : 0 ≤ A)
    (harea : ∀ i, (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap c) (r i*((R+1)+2))) ≤ A*(r i*((R+1)+2))^2) :
    TotallyBounded (range fun i ↦ boundedFunctionL1
      (volume.restrict (Metric.closedBall (0 : Cover) R)) (blowupCharacteristic E c (r i))
      (measurable_blowupCharacteristic hE c (r i)) (blowupCharacteristic_bound E c (r i))) := by
  apply totallyBounded_local_translation (η := volume) (isCompact_closedBall _ _)
    (fun i ↦ blowupCharacteristic E c (r i))
    (fun i ↦ measurable_blowupCharacteristic hE c (r i))
    (fun i ↦ blowupCharacteristic_bound E c (r i))
    (A := A*((R+1)+2)^2) (ε₀ := 1) (by positivity) (by norm_num)
  intro i y hy
  have htrans := blowupCharacteristic_translation_density hE hμ c (hr i)
    (by linarith : 0 ≤ R+1) (hc i) hA (harea i) y hy
  apply le_trans _ htrans
  apply setIntegral_mono_set _ (ae_of_all _ fun _ ↦ abs_nonneg _)
    (ae_of_all _ fun _ hx ↦ Metric.closedBall_subset_ball (by linarith : R < R+1) hx)
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Cover) (R+1))) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hf := measurable_blowupCharacteristic hE c (r i)
  have hbound := blowupCharacteristic_bound E c (r i)
  apply Integrable.of_bound (μ := volume.restrict (Metric.ball (0 : Cover) (R+1)))
    (((hf.comp (measurable_id.sub_const y)).sub hf).abs.aestronglyMeasurable) 2
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs,abs_abs,Function.comp_apply,id_eq,Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith [hbound (x-y),hbound x])

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev BlowupNormalBundle := Cover × NormalSphere

def blowupNormalMap (c : Cover) (r : ℝ) (z : NormalBundle) : BlowupNormalBundle :=
  (r⁻¹ • ((z.1 : Cover)-c),z.2)

lemma continuous_blowupNormalMap (c : Cover) (r : ℝ) :
    Continuous (blowupNormalMap c r) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((hx.sub continuous_const).const_smul r⁻¹).prodMk continuous_snd

def blowupNormalMeasure (μ : FiniteMeasure NormalBundle) (c : Cover) (r R : ℝ) :
    FiniteMeasure BlowupNormalBundle :=
  Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (blowupNormalMap c r)

lemma blowupNormalMeasure_mass (μ : FiniteMeasure NormalBundle) (c : Cover) (r R : ℝ) :
    ((blowupNormalMeasure μ c r R).mass : ℝ) = r⁻¹^2*cellBallMass μ c (r*R) := by
  change (((Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (blowupNormalMap c r)) univ) : ℝ) = _
  rw [FiniteMeasure.smul_apply,FiniteMeasure.map_apply _
    (continuous_blowupNormalMap c r).measurable MeasurableSet.univ]
  rw [Set.preimage_univ,FiniteMeasure.restrict_apply _ _ MeasurableSet.univ,univ_inter]
  change (Real.toNNReal (r⁻¹^2) : ℝ) *
    (((μ : Measure NormalBundle) {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma blowupNormalMap_mem (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (z : NormalBundle) :
    (blowupNormalMap c r z).1 ∈ Metric.ball (0 : Cover) R ↔
      (z.1 : Cover) ∈ Metric.ball c (r*R) := by
  simp only [blowupNormalMap,Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul,div_lt_iff₀ hr]
  rw [mul_comm R r]

lemma blowupNormalMeasure_supported (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    blowupNormalMeasure μ c r R ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 := by
  have hm : MeasurableSet ((Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere))ᶜ) :=
    (Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ).compl
  have he : (blowupNormalMap c r ⁻¹' ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ)) ∩
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 ⟨Metric.ball_subset_closedBall ((blowupNormalMap_mem c hr R z).mpr hz.2),mem_univ _⟩
  unfold blowupNormalMeasure
  rw [FiniteMeasure.smul_apply,
    FiniteMeasure.map_apply _ (continuous_blowupNormalMap c r).measurable hm,
    FiniteMeasure.restrict_apply _ _ (hm.preimage (continuous_blowupNormalMap c r).measurable),he]
  simp [FiniteMeasure.coeFn_def]

theorem blowupNormalMeasure_cluster {μ : FiniteMeasure NormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, cellBallMass μ c (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ blowupNormalMeasure μ c (r i) R) := by
  have hm (i) : (blowupNormalMeasure μ c (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,blowupNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ blowupNormalMeasure μ c (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,blowupNormalMeasure_supported μ c (hr i) R⟩))
  refine ⟨ν,?_,hν.2,hcl⟩
  simpa only [Real.coe_toNNReal _ hA] using (NNReal.coe_le_coe.mpr hν.1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma integral_blowupNormalMeasure (μ : FiniteMeasure NormalBundle) (c : Cover)
    (r R : ℝ) {g : BlowupNormalBundle → ℝ} (hg : Continuous g) :
    (∫ z, g z ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)},
        g (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
  rw [blowupNormalMeasure,FiniteMeasure.toMeasure_smul,integral_smul_nnreal_measure,
    FiniteMeasure.toMeasure_map,integral_map
      (continuous_blowupNormalMap c r).measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  change (Real.toNNReal (r⁻¹^2) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma tangentialDivergence_zero_of_notMem_tsupport {F : Cover → Cover} {x : Cover}
    (hx : x ∉ tsupport F) (n : Cover) : tangentialDivergence F x n = 0 := by
  simp [tangentialDivergence,divergence_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]

lemma hasCompactSupport_normalBundle_test {F : Cover → Cover} (hF : HasCompactSupport F)
    {g : BlowupNormalBundle → ℝ} (hg : ∀ z, z.1 ∉ tsupport F → g z = 0) :
    HasCompactSupport g := by
  apply (hF.prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ (isClosed_closure.prod isClosed_univ)
  intro z hz
  refine ⟨?_,mem_univ _⟩
  by_contra hh
  exact hz (hg z hh)

lemma continuous_blowupFluxTest {F : Cover → Cover} (hF : Continuous F) :
    Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) :=
  (continuous_subtype_val.comp continuous_snd).inner (hF.comp continuous_fst)

lemma continuous_blowupTangentTest {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun z : BlowupNormalBundle ↦ tangentialDivergence F z.1 z.2) :=
  ((continuous_divergence hF).comp continuous_fst).sub
    ((continuous_subtype_val.comp continuous_snd).inner
      (((hF.continuous_fderiv (by simp)).comp continuous_fst).clm_apply
        (continuous_subtype_val.comp continuous_snd)))

def blowupFluxTest {F : Cover → Cover} (hF : Continuous F) (hs : HasCompactSupport F) :
    BlowupNormalBundle →ᵇ ℝ :=
  ofCompactSupport _ (continuous_blowupFluxTest hF)
    (hasCompactSupport_normalBundle_test hs (fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport hz]))

def blowupTangentTest {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : HasCompactSupport F) : BlowupNormalBundle →ᵇ ℝ :=
  ofCompactSupport _ (continuous_blowupTangentTest hF)
    (hasCompactSupport_normalBundle_test hs (fun z hz ↦
      tangentialDivergence_zero_of_notMem_tsupport hz z.2))

lemma integral_blowup_test (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r R : ℝ} (hr : 0 < r) {g : BlowupNormalBundle → ℝ} (hg : Continuous g)
    (hzero : ∀ z, z.1 ∉ Metric.ball (0 : Cover) R → g z = 0) :
    (∫ z, g z ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z, g (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
  rw [integral_blowupNormalMeasure μ c r R hg]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hzero _ (by rwa [blowupNormalMap_mem c hr R z])

lemma tangentialDivergence_scaledTestField {F : Cover → Cover}
    (hF : Differentiable ℝ F) (c x n : Cover) {r : ℝ} (hr : r ≠ 0) :
    tangentialDivergence (scaledTestField c r F) x n =
      tangentialDivergence F (r⁻¹ • (x-c)) n := by
  simp only [tangentialDivergence,divergence_scaledTestField hF c x hr,
    fderiv_scaledTestField hF c x hr]

theorem weakCMC_blowup_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (c : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall c r ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    (∫ z, tangentialDivergence F z.1 z.2
      ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      (r*H) * ∫ z, ⟪(z.2 : Cover),F z.1⟫
        ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle) := by
  have ht (z : BlowupNormalBundle) (hz : z.1 ∉ Metric.ball (0 : Cover) R) :
      z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
  rw [integral_blowup_test μ c hr (continuous_blowupTangentTest hF)
      (fun z hz ↦ tangentialDivergence_zero_of_notMem_tsupport (ht z hz) z.2),
    integral_blowup_test μ c hr (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport (ht z hz)])]
  have hid := weakCMC_local_identity hμ hH (scaledTestField_contDiff hF c r)
    (scaledTestField_hasCompactSupport hs c hr) ((scaledTestField_tsupport hs c hr).trans hc)
  simp only [tangentialDivergence_scaledTestField (hF.differentiable (by simp)) c _ _ hr.ne',
    scaledTestField,inner_smul_right,integral_const_mul] at hid
  change r⁻¹^2*(∫ z, tangentialDivergence F (r⁻¹ • ((z.1 : Cover)-c)) z.2
    ∂(μ : Measure NormalBundle)) = _
  rw [hid]
  simp only [blowupNormalMap]
  ring

theorem weakCMC_blowup_limit_stationary {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall c (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) R) l (𝓝 ν))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have ht := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupTangentTest hF hFs)
  have hf := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupFluxTest hF.continuous hFs)
  have hh := (hrlim.mul_const H).mul hf
  simp only [zero_mul] at hh
  have he (i) := weakCMC_blowup_identity hμ hH hF hs c (hr i) hR (hc i)
  exact tendsto_nhds_unique ht (hh.congr (fun i ↦ (he i).symm))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_indicator_bound (F : Set Cover) (x : Cover) :
    |F.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
  classical
  by_cases hx : x ∈ F <;> simp [hx]

lemma boundedFunctionL1_ae {η : Measure Cover} [IsFiniteMeasure η]
    {g : Cover → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) :
    boundedFunctionL1 η g hg hb =ᵐ[η] g := (integrable_bounded_one hg hb).coeFn_toL1

theorem exists_cover_indicator_limit {η : Measure Cover} [IsFiniteMeasure η]
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) (hphase : ∀ i x, g i x = 0 ∨ g i x = 1)
    (ht : TotallyBounded (range fun i ↦ boundedFunctionL1 η (g i) (hg i) (hgb i))) :
    ∃ F : Set Cover, ∃ hF : MeasurableSet F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ boundedFunctionL1 η (g (φ i)) (hg (φ i)) (hgb (φ i))) atTop
        (𝓝 (boundedFunctionL1 η (F.indicator (fun _ ↦ (1 : ℝ)))
          (measurable_const.indicator hF) (cover_indicator_bound F))) ∧
      ∀ᵐ x ∂η, Tendsto (fun i ↦ g (φ i) x) atTop
        (𝓝 (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  let gs (i) := boundedFunctionL1 η (g i) (hg i) (hgb i)
  obtain ⟨f,_,ns,hns,hconv⟩ := (ht.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (fun i ↦ subset_closure (mem_range_self i))
  obtain ⟨ms,hms,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂η, ∀ i, gs (ns (ms i)) x = g (ns (ms i)) x :=
    ae_all_iff.mpr (fun i ↦ boundedFunctionL1_ae (hg _) (hgb _))
  have hlim : ∀ᵐ x ∂η, Tendsto (fun i ↦ g (ns (ms i)) x) atTop (𝓝 (f x)) := by
    filter_upwards [hae,hcoe] with x hx hh
    convert hx using 1
    ext i
    exact (hh i).symm
  let F : Set Cover := {x | f x = 1}
  have hF : MeasurableSet F := (Lp.stronglyMeasurable f).measurable (measurableSet_singleton 1)
  have hchar : f =ᵐ[η] F.indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have hf : f x ∈ ({0,1} : Set ℝ) := by
      apply ((finite_singleton (1 : ℝ)).insert 0).isClosed.mem_of_tendsto hx
      exact Eventually.of_forall fun i ↦ by
        rcases hphase (ns (ms i)) x with h|h <;> simp [h]
    rcases mem_insert_iff.mp hf with h0|h1
    · have hxF : x ∉ F := by simp [F,h0]
      simp [hxF,h0]
    · have hxF : x ∈ F := h1
      simp [hxF,show f x = 1 from h1]
  have heq : f = boundedFunctionL1 η (F.indicator (fun _ ↦ (1 : ℝ)))
      (measurable_const.indicator hF) (cover_indicator_bound F) :=
    Lp.ext (hchar.trans (boundedFunctionL1_ae (measurable_const.indicator hF)
      (cover_indicator_bound F)).symm)
  refine ⟨F,hF,ns ∘ ms,hns.comp hms,?_,?_⟩
  · simpa only [Function.comp_def,heq] using hconv.comp hms.tendsto_atTop
  · filter_upwards [hlim,hchar] with x hx hh
    simpa only [Function.comp_apply,← hh] using hx

lemma boundedFunctionL1_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i)) (hgb : ∀ i x, |g i x| ≤ 1)
    {f : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ boundedFunctionL1 η (g i) (hg i) (hgb i)) atTop
      (𝓝 (boundedFunctionL1 η f hf hfb))) :
    Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) atTop (𝓝 0) := by
  have h := hlim.dist (tendsto_const_nhds (x := boundedFunctionL1 η f hf hfb))
  simpa only [dist_self,boundedFunctionL1_dist] using h

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_blowup_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : Cover) {d : ℝ} (hd : 0 < d)
    (hc : Metric.ball c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∃ F : Set Cover, MeasurableSet F ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E c (r (φ i)) x-F.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Cover) R),
        Tendsto (fun i ↦ blowupCharacteristic E c (r (φ i)) x) atTop
          (𝓝 (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  have hsmall : 0 < min (d/(R+1)) (S/((R+1)+2)) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let s : ℕ → ℝ := fun i ↦ r (i+k)
  have hs (i) : 0 < s i := hr _
  have hsb (i) : s i < min (d/(R+1)) (S/((R+1)+2)) := hk _ (by omega)
  have hchart (i) : Metric.ball c (s i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply (Metric.ball_subset_ball _).trans hc
    exact ((lt_div_iff₀ (by linarith : 0 < R+1)).mp
      ((hsb i).trans_le (min_le_left _ _))).le
  have hb (i) : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap c) (s i*((R+1)+2))) ≤ A*(s i*((R+1)+2))^2 := by
    apply harea μ hμ _ _ (by have hh := hs i; positivity)
    exact ((lt_div_iff₀ (by linarith : 0 < (R+1)+2)).mp
      ((hsb i).trans_le (min_le_right _ _))).le
  have ht := totallyBounded_blowupCharacteristic hE hμ c s hs hR hchart hA.le hb
  obtain ⟨F,hF,φ,hφ,hconv,hae⟩ := exists_cover_indicator_limit
    (fun i ↦ blowupCharacteristic E c (s i))
    (fun i ↦ measurable_blowupCharacteristic hE c (s i))
    (fun i ↦ blowupCharacteristic_bound E c (s i))
    (fun i x ↦ characteristic_dichotomy E (quotientMap (c+s i • x))) ht
  refine ⟨F,hF,fun i ↦ φ i+k,fun i j hij ↦ Nat.add_lt_add_right (hφ hij) k,?_,hae⟩
  exact boundedFunctionL1_integral_tendsto
    (fun i ↦ blowupCharacteristic E c (s (φ i)))
    (fun i ↦ measurable_blowupCharacteristic hE c (s (φ i)))
    (fun i ↦ blowupCharacteristic_bound E c (s (φ i)))
    (measurable_const.indicator hF) (cover_indicator_bound F) hconv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_blowupCharacteristic_ball {E : Set Torus} (hE : MeasurableSet E)
    (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap c) (r*R)) =
      r^3 * ∫ x in Metric.ball (0 : Cover) R, blowupCharacteristic E c r x := by
  rw [← setIntegral_characteristic hE _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball _ (measurable_characteristic hE) c _ hc,
    integral_ball_affine_scaling _ c hr R]
  rfl

lemma localL1_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) atTop (𝓝 0))
    (s : Set Cover) :
    Tendsto (fun i ↦ ∫ x in s, g i x ∂η) atTop (𝓝 (∫ x in s, f x ∂η)) := by
  have hi (i) : Integrable (fun x ↦ |g i x-f x|) η :=
    ((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs
  have hl : Tendsto (fun i ↦ ∫ x in s, |g i x-f x| ∂η) atTop (𝓝 0) := by
    apply squeeze_zero (fun i ↦ integral_nonneg (fun x ↦ abs_nonneg _)) _ hlim
    intro i
    exact setIntegral_le_integral (hi i) (ae_of_all _ (fun x ↦ abs_nonneg _))
  apply tendsto_integral_of_L1 f hf.aestronglyMeasurable
    (Eventually.of_forall (fun i ↦ integrable_bounded_one (η := η.restrict s) (hg i) (hgb i)))
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl
  simp only [ENNReal.ofReal_zero] at ho
  convert ho using 1
  funext i
  symm
  simpa only [Real.norm_eq_abs,Pi.sub_apply,Function.comp_apply] using ofReal_integral_norm_eq_lintegral_enorm
    (((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).restrict (s := s))

lemma localL1_ball_integral_tendsto {R ρ : ℝ} (hρ : ρ ≤ R)
    (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |g i x-f x|) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Cover) ρ, g i x) atTop
      (𝓝 (∫ x in Metric.ball (0 : Cover) ρ, f x)) := by
  have h := localL1_integral_tendsto g hg hgb hf hfb hlim (Metric.ball (0 : Cover) ρ)
  simpa only [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
    inter_eq_left.mpr ((Metric.ball_subset_ball hρ).trans Metric.ball_subset_closedBall)] using h

theorem isMinimizerAt_blowup_limit_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : Cover) (hb : quotientMap c ∈ volumeSupport E ∩ volumeSupport Eᶜ)
    {d : ℝ} (hd : 0 < d)
    (hc : Metric.ball c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) {F : Set Cover} (hF : MeasurableSet F)
    (hlim : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E c (r i) x-F.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0)) :
    ∃ b : ℝ, 0 < b ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      b*ρ^3 ≤ volume.real (F ∩ Metric.ball (0 : Cover) ρ) ∧
      b*ρ^3 ≤ volume.real (Fᶜ ∩ Metric.ball (0 : Cover) ρ) := by
  obtain ⟨S,b,hS,hbpos,hden⟩ := isMinimizerAt_two_sided_density hV hE hmin
  refine ⟨b,hbpos,?_⟩
  intro ρ hρ hρR
  have hsmall : 0 < min d S / R := div_pos (lt_min hd hS) hR
  have hevent : ∀ᶠ i in atTop, r i*ρ < min d S := by
    filter_upwards [hrlim.eventually (gt_mem_nhds hsmall)] with i hi
    exact (mul_le_mul_of_nonneg_left hρR (hr i).le).trans_lt ((lt_div_iff₀ hR).mp hi)
  have hint := localL1_ball_integral_tendsto hρR
    (fun i ↦ blowupCharacteristic E c (r i))
    (fun i ↦ measurable_blowupCharacteristic hE c (r i))
    (fun i ↦ blowupCharacteristic_bound E c (r i))
    (measurable_const.indicator hF) (cover_indicator_bound F) hlim
  have hcomp (i x) : blowupCharacteristic Eᶜ c (r i) x =
      1-blowupCharacteristic E c (r i) x := by
    classical
    by_cases hx : quotientMap (c+r i • x) ∈ E <;>
      simp [blowupCharacteristic,characteristic,hx]
  have hfcomp (x : Cover) : Fᶜ.indicator (fun _ ↦ (1 : ℝ)) x =
      1-F.indicator (fun _ ↦ (1 : ℝ)) x := by
    classical
    by_cases hx : x ∈ F <;> simp [hx]
  have hlimc : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic Eᶜ c (r i) x-Fᶜ.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0) := by
    convert hlim using 2
    rename_i i
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change |blowupCharacteristic Eᶜ c (r i) x-Fᶜ.indicator (fun _ ↦ (1 : ℝ)) x| = _
    rw [hcomp,hfcomp,show 1-blowupCharacteristic E c (r i) x -
      (1-F.indicator (fun _ ↦ (1 : ℝ)) x) =
      -(blowupCharacteristic E c (r i) x-F.indicator (fun _ ↦ (1 : ℝ)) x) by ring,
      abs_neg]
  have hintc := localL1_ball_integral_tendsto hρR
    (fun i ↦ blowupCharacteristic Eᶜ c (r i))
    (fun i ↦ measurable_blowupCharacteristic hE.compl c (r i))
    (fun i ↦ blowupCharacteristic_bound Eᶜ c (r i))
    (measurable_const.indicator hF.compl) (cover_indicator_bound Fᶜ) hlimc
  have hlow : ∀ᶠ i in atTop,
      b*ρ^3 ≤ ∫ x in Metric.ball (0 : Cover) ρ, blowupCharacteristic E c (r i) x ∧
      b*ρ^3 ≤ ∫ x in Metric.ball (0 : Cover) ρ, blowupCharacteristic Eᶜ c (r i) x := by
    filter_upwards [hevent] with i hi
    have hchart : Metric.ball c (r i*ρ) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
      (Metric.ball_subset_ball (hi.trans_le (min_le_left _ _)).le).trans hc
    have hh := hden _ hb (r i*ρ) (mul_pos (hr i) hρ)
      (hi.trans_le (min_le_right _ _)).le
    rw [integral_blowupCharacteristic_ball hE c (hr i) ρ hchart,
      integral_blowupCharacteristic_ball hE.compl c (hr i) ρ hchart] at hh
    constructor
    · apply (mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp
      calc
        _ = b*(r i*ρ)^3 := by ring
        _ ≤ _ := hh.1
    · apply (mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp
      calc
        _ = b*(r i*ρ)^3 := by ring
        _ ≤ _ := hh.2
  have heq (A : Set Cover) (hA : MeasurableSet A) :
      (∫ x in Metric.ball (0 : Cover) ρ, A.indicator (fun _ ↦ (1 : ℝ)) x) =
        volume.real (A ∩ Metric.ball (0 : Cover) ρ) := by
    rw [integral_indicator hA,Measure.restrict_restrict hA,integral_const,
      smul_eq_mul,mul_one,Measure.real_def,Measure.restrict_apply_univ]
    rfl
  rw [← heq F hF,← heq Fᶜ hF.compl]
  exact ⟨ge_of_tendsto hint (hlow.mono (fun _ hi ↦ hi.1)),
    ge_of_tendsto hintc (hlow.mono (fun _ hi ↦ hi.2))⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma localL1_weighted_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    {l : Filter ℕ} (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) l (𝓝 0))
    (k : Cover →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, g i x*k x ∂η) l (𝓝 (∫ x, f x*k x ∂η)) := by
  have hi (i) : Integrable (fun x ↦ g i x*k x) η :=
    Integrable.of_bound ((hg i).mul k.continuous.measurable).aestronglyMeasurable ‖k‖
      (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
          mul_le_mul (hgb i x) (k.norm_coe_le_norm x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
  have hfi : Integrable (fun x ↦ f x*k x) η :=
    Integrable.of_bound (hf.mul k.continuous.measurable).aestronglyMeasurable ‖k‖
      (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
          mul_le_mul (hfb x) (k.norm_coe_le_norm x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
  have hdiff (i) : Integrable (fun x ↦ |g i x-f x|) η :=
    ((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs
  have hbound (i) : ‖(∫ x, g i x*k x ∂η)-(∫ x, f x*k x ∂η)‖ ≤
      ‖k‖ * ∫ x, |g i x-f x| ∂η := by
    rw [← integral_sub (hi i) hfi,← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono ((hi i).sub hfi).norm ((hdiff i).const_mul ‖k‖)
    intro x
    change ‖g i x*k x-f x*k x‖ ≤ ‖k‖*|g i x-f x|
    rw [← sub_mul,Real.norm_eq_abs,abs_mul]
    exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (abs_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i ↦ norm_nonneg _) hbound (by simpa using hlim.const_mul ‖k‖)

theorem blowup_limit_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall c (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) R) l (𝓝 ν))
    {A : Set Cover} (hA : MeasurableSet A)
    (hAconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E c (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ x in A, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hd : HasCompactSupport (divergence F) := hFs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  let k : Cover →ᵇ ℝ := ofCompactSupport _ (continuous_divergence hF) hd
  have hstri := localL1_weighted_integral_tendsto
    (fun i ↦ blowupCharacteristic E c (r i))
    (fun i ↦ measurable_blowupCharacteristic hE c (r i))
    (fun i ↦ blowupCharacteristic_bound E c (r i))
    (measurable_const.indicator hA)
    (fun x ↦ by by_cases hx : x ∈ A <;> simp [hx]) hAconv k
  have hzero (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) R) : divergence F x = 0 :=
    divergence_of_notMem_tsupport (fun hh ↦ hx (Metric.closedBall_subset_closedBall hR.le (hs hh)))
  have heg (i) : (∫ x in Metric.closedBall (0 : Cover) R, blowupCharacteristic E c (r i) x*k x) =
      ∫ x, blowupCharacteristic E c (r i) x*divergence F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hzero x hx,mul_zero])
  have hef : (∫ x in Metric.closedBall (0 : Cover) R, A.indicator (fun _ ↦ (1 : ℝ)) x*k x) =
      ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hzero x hx,mul_zero])]
    change (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence F x) = _
    simp only [← indicator_mul_left,one_mul]
    exact integral_indicator hA
  simp_rw [heg] at hstri
  rw [hef] at hstri
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) (blowupFluxTest hF.continuous hFs)
  have he (i) : (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(blowupNormalMeasure μ c (r i) R : Measure BlowupNormalBundle)) =
      ∫ x, blowupCharacteristic E c (r i) x*divergence F x := by
    rw [integral_blowup_test μ c (hr i) (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by
        have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
        simp [image_eq_zero_of_notMem_tsupport hn])]
    change (r i)⁻¹^2*(∫ z, ⟪(z.2 : Cover),F ((r i)⁻¹ • ((z.1 : Cover)-c))⟫ ∂(μ : Measure NormalBundle)) = _
    rw [show (r i)⁻¹^2 = ((r i)^2)⁻¹ by ring]
    rw [← div_eq_inv_mul,normalMeasure_scaled_flux hE hμ hF hs c (hr i) (hc i)]
    simp only [blowupCharacteristic,add_comm c]
  exact tendsto_nhds_unique (hweak.congr fun i ↦ he i) hstri

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverLocalPerimeter (A O : Set Cover) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
    (_ : HasCompactSupport F) (_ : tsupport F ⊆ O) (_ : ∀ x, ‖F x‖ ≤ 1),
      ENNReal.ofReal (∫ x in A, divergence F x)

lemma coverLocalPerimeter_mono (A : Set Cover) {O P : Set Cover} (hOP : O ⊆ P) :
    coverLocalPerimeter A O ≤ coverLocalPerimeter A P := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hO
  apply iSup_le
  intro hb
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le (hO.trans hOP) (le_iSup_of_le hb le_rfl))))

lemma integral_divergence_le_coverLocalPerimeter {A O : Set Cover} {L : ℝ}
    (hL : coverLocalPerimeter A O ≤ ENNReal.ofReal L) (hL0 : 0 ≤ L)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hb : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) ≤ L := by
  apply (ENNReal.ofReal_le_ofReal_iff hL0).mp
  have hh : ENNReal.ofReal (∫ x in A, divergence F x) ≤ coverLocalPerimeter A O :=
    le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
      (le_iSup_of_le hO (le_iSup_of_le hb le_rfl))))
  exact hh.trans hL

theorem coverLocalPerimeter_le_normal {A O : Set Cover}
    {ν : FiniteMeasure BlowupNormalBundle} (hO : MeasurableSet O)
    (hO1 : O ⊆ Metric.closedBall (0 : Cover) 1)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter A O ≤ (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hFO
  apply iSup_le
  intro hb
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} := hO.preimage measurable_fst
  have hc : Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) :=
    (continuous_subtype_val.comp continuous_snd).inner (hF.continuous.comp continuous_fst)
  have hbd (z : BlowupNormalBundle) : ‖⟪(z.2 : Cover),F z.1⟫‖ ≤ 1 := by
    calc
      _ ≤ ‖(z.2 : Cover)‖*‖F z.1‖ := norm_inner_le_norm _ _
      _ ≤ 1 := by rw [z.2.property,one_mul]; exact hb _
  have hi : Integrable (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) ν :=
    Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ hbd)
  have hri : Integrable ({z : BlowupNormalBundle | z.1 ∈ O}.indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_const 1).indicator hm
  have he : (∫ x in A, divergence F x) ≤ (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ O} := by
    rw [← hflux F hF (hFO.trans hO1)]
    have hh := integral_mono_ae hi hri (ae_of_all _ fun z ↦ ?_)
    · simpa only [integral_indicator hm,integral_const,smul_eq_mul,mul_one,
        measureReal_restrict_apply_univ] using hh
    · by_cases hz : z.1 ∈ O
      · simpa [Set.indicator,hz] using (le_abs_self _).trans (hbd z)
      · have hzero : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz (hFO hh))
        simp [Set.indicator,hz,hzero]
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def coverPrismCoordinates : Cover ≃L[ℝ] PrismCoordinates :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).trans
    { toLinearEquiv :=
        { toFun := fun v ↦ (v 0,(v 1,v 2))
          invFun := fun z ↦ ![z.1,z.2.1,z.2.2]
          left_inv := by intro v; ext i; fin_cases i <;> rfl
          right_inv := by intro z; rfl
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

lemma coverPrismCoordinates_apply (x : Cover) :
    coverPrismCoordinates x = (x 0,(x 1,x 2)) := rfl

lemma coverPrismCoordinates_symm_apply (z : PrismCoordinates) :
    coverPrismCoordinates.symm z = WithLp.toLp 2 ![z.1,z.2.1,z.2.2] := rfl

lemma coverPrismCoordinates_measurePreserving : MeasurePreserving coverPrismCoordinates := by
  have h1 : MeasurePreserving (WithLp.ofLp : Cover → Fin 3 → ℝ) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp h1
  have h3 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  convert! h3.comp h2 using 1

lemma coverPrismCoordinates_symm_measurePreserving :
    MeasurePreserving coverPrismCoordinates.symm :=
  coverPrismCoordinates_measurePreserving.symm coverPrismCoordinates.toHomeomorph.toMeasurableEquiv

lemma prism_component_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : PrismCoordinates ↦ F (coverPrismCoordinates.symm z) i) :=
  (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp (hF.comp coverPrismCoordinates.symm.contDiff)

lemma prism_component_compactSupport {F : Cover → Cover}
    (hF : HasCompactSupport F) (i : Fin 3) :
    HasCompactSupport (fun z : PrismCoordinates ↦ F (coverPrismCoordinates.symm z) i) := by
  have hh := hF.comp_isClosedEmbedding coverPrismCoordinates.symm.toHomeomorph.isClosedEmbedding
  apply hh.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro z hz
  contrapose! hz
  simp only [Function.mem_support,not_not] at hz ⊢
  change F (coverPrismCoordinates.symm z) = 0 at hz
  rw [hz]
  rfl

lemma prism_component_fderiv {F : Cover → Cover} (hF : Differentiable ℝ F)
    (i : Fin 3) (z v : PrismCoordinates) :
    fderiv ℝ (fun w : PrismCoordinates ↦ F (coverPrismCoordinates.symm w) i) z v =
      (fderiv ℝ F (coverPrismCoordinates.symm z) (coverPrismCoordinates.symm v)) i := by
  exact (((EuclideanSpace.proj i).hasFDerivAt.comp _
    ((hF _).hasFDerivAt.comp z coverPrismCoordinates.symm.hasFDerivAt)).fderiv |> congrArg (fun L ↦ L v))

lemma prism_coordinate_divergence {F : Cover → Cover} (hF : Differentiable ℝ F)
    (z : PrismCoordinates) :
    prismCoordinateDivergence (fun w ↦ F (coverPrismCoordinates.symm w) 0)
      (fun w ↦ F (coverPrismCoordinates.symm w) 1)
      (fun w ↦ F (coverPrismCoordinates.symm w) 2) z =
      divergence F (coverPrismCoordinates.symm z) := by
  simp only [prismCoordinateDivergence,prism_component_fderiv hF,divergence,
    Fin.sum_univ_three]
  have he0 : coverPrismCoordinates.symm (1,(0,0)) = EuclideanSpace.single 0 1 := by
    ext i; fin_cases i <;> simp [coverPrismCoordinates_symm_apply]
  have he1 : coverPrismCoordinates.symm (0,(1,0)) = EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp [coverPrismCoordinates_symm_apply]
  have he2 : coverPrismCoordinates.symm (0,(0,1)) = EuclideanSpace.single 2 1 := by
    ext i; fin_cases i <;> simp [coverPrismCoordinates_symm_apply]
  rw [he0,he1,he2]

def euclideanPrism (a c b l u : ℝ) : Set Cover :=
  coverPrismCoordinates ⁻¹' coordinatePrism a c b l u

lemma measurableSet_euclideanPrism (a c b l u : ℝ) : MeasurableSet (euclideanPrism a c b l u) :=
  (measurableSet_Ioc.prod (measurableSet_coordinateTriangle b l u)).preimage
    coverPrismCoordinates.continuous.measurable

theorem integral_euclideanPrism_divergence {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ x in euclideanPrism a c b l u, divergence F x) =
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u +
      prismClosingFlux (fun w ↦ F (coverPrismCoordinates.symm w) 0)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u := by
  have hmeas : MeasurableSet (coordinatePrism a c b l u) :=
    measurableSet_Ioc.prod (measurableSet_coordinateTriangle b l u)
  have hm := coverPrismCoordinates_symm_measurePreserving.restrict_preimage
    (measurableSet_euclideanPrism a c b l u)
  have he : coverPrismCoordinates.symm ⁻¹' euclideanPrism a c b l u = coordinatePrism a c b l u := by
    ext x; simp [euclideanPrism]
  rw [he] at hm
  rw [← hm.integral_comp coverPrismCoordinates.symm.toHomeomorph.measurableEmbedding]
  simp_rw [← prism_coordinate_divergence (hF.differentiable (by simp))]
  exact integral_coordinatePrism_divergence_split
    (prism_component_contDiff hF 0) (prism_component_contDiff hF 1) (prism_component_contDiff hF 2)
    (prism_component_compactSupport hs 0) (prism_component_compactSupport hs 1)
    (prism_component_compactSupport hs 2) hac hb hlu

end CubicTorus

end
end

end

end OAI
