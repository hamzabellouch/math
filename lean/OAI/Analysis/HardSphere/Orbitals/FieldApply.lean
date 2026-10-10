import Mathlib
import OAI.Analysis.HardSphere.Geometry.CoordinateLine

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace L2Contraction
variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

lemma unifIntegrable_of_domination {ι : Type*} {p : ℝ≥0∞}
    {f : ι → α → E} {b : α → F} (hp : 1 ≤ p) (hp' : p ≠ ∞) (hb : MemLp b p μ)
    (hf_meas : ∀ index, AEStronglyMeasurable (f index) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖) : UnifIntegrable f p μ := by
  refine unifIntegrable_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hi⟩ := unifIntegrable_iff.1 (unifIntegrable_const (ι := ι) hp hp' hb) ε hε
  refine ⟨δ, hδ, fun index region hμs ↦ le_trans ?_ (hi index region hμs)⟩
  exact eLpNorm_mono_ae (hf_meas index).restrict (ae_restrict_of_ae (hbound index))

lemma tendsto_toLp_of_domination [IsFiniteMeasure μ]
    {f : ℕ → α → E} {g : α → E} {b : α → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n ↦ (hf n).aestronglyMeasurable) hg
    (unifIntegrable_of_domination (by norm_num) (by norm_num) hb
      (fun index ↦ (hf index).aestronglyMeasurable) hbound) hl

section Field
variable [NormedSpace ℝ E] [NormedSpace ℝ F]
    (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ 1)
include hA hbound

lemma field_memLp (v : Lp E 2 μ) : MemLp (fun x ↦ A x (v x)) 2 μ := by
  apply (Lp.memLp v).of_le ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hA.prodMk (Lp.aestronglyMeasurable v)))
  filter_upwards [hbound] with x hx
  exact (A x).le_opNorm (v x) |>.trans (by nlinarith [norm_nonneg (v x)])

def fieldApply (v : Lp E 2 μ) : Lp F 2 μ :=
  (field_memLp A hA hbound v).toLp _

lemma coe_fieldApply (v : Lp E 2 μ) :
    fieldApply A hA hbound v =ᵐ[μ] fun x ↦ A x (v x) :=
  MemLp.coeFn_toLp _

lemma norm_fieldApply_le (v : Lp E 2 μ) : ‖fieldApply A hA hbound v‖ ≤ ‖v‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coe_fieldApply A hA hbound v, hbound] with x hx hb
  rw [hx]
  exact (A x).le_opNorm (v x) |>.trans (by nlinarith [norm_nonneg (v x)])

lemma fieldApply_sub (v w : Lp E 2 μ) :
    fieldApply A hA hbound (v - w) = fieldApply A hA hbound v - fieldApply A hA hbound w := by
  apply Lp.ext
  filter_upwards [coe_fieldApply A hA hbound (v - w), coe_fieldApply A hA hbound v,
    coe_fieldApply A hA hbound w, Lp.coeFn_sub v w,
    Lp.coeFn_sub (fieldApply A hA hbound v) (fieldApply A hA hbound w)] with x h1 h2 h3 h4 h5
  simp only [h1, h4, Pi.sub_apply, map_sub, h5, h2, h3]

lemma norm_fieldApply_sub_le (v w : Lp E 2 μ) :
    ‖fieldApply A hA hbound v - fieldApply A hA hbound w‖ ≤ ‖v - w‖ := by
  rw [← fieldApply_sub]
  exact norm_fieldApply_le A hA hbound _
end Field

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma coeff_meas (A : G → E →L[ℝ] F) (hA : Continuous A) (u : Lp G 2 μ) :
    AEStronglyMeasurable (fun x ↦ A (u x)) μ :=
  hA.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)

lemma tendsto_fieldApply_fixed [IsFiniteMeasure μ]
    (A : G → E →L[ℝ] F) (hA : Continuous A) (hb : ∀ z, ‖A z‖ ≤ 1)
    (u : ℕ → Lp G 2 μ) (u₀ : Lp G 2 μ)
    (hu : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (u₀ x))) (v : Lp E 2 μ) :
    Tendsto (fun n ↦ fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
      (Eventually.of_forall (fun x ↦ hb (u n x))) v) atTop
      (𝓝 (fieldApply (fun x ↦ A (u₀ x)) (coeff_meas A hA u₀)
        (Eventually.of_forall (fun x ↦ hb (u₀ x))) v)) := by
  apply tendsto_toLp_of_domination _ _ (Lp.memLp v)
  · intro n
    exact Eventually.of_forall fun x ↦ (A (u n x)).le_opNorm (v x) |>.trans
      (by nlinarith [norm_nonneg (v x), hb (u n x)])
  · filter_upwards [hu] with x hx
    exact ((ContinuousLinearMap.apply ℝ F (v x)).continuous.tendsto _).comp
      (hA.continuousAt.tendsto.comp hx)

lemma tendsto_fieldApply [IsFiniteMeasure μ]
    (A : G → E →L[ℝ] F) (hA : Continuous A) (hb : ∀ z, ‖A z‖ ≤ 1)
    (u : ℕ → Lp G 2 μ) (u₀ : Lp G 2 μ)
    (hu : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (u₀ x)))
    (v : ℕ → Lp E 2 μ) (v₀ : Lp E 2 μ) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n ↦ fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
      (Eventually.of_forall (fun x ↦ hb (u n x))) (v n)) atTop
      (𝓝 (fieldApply (fun x ↦ A (u₀ x)) (coeff_meas A hA u₀)
        (Eventually.of_forall (fun x ↦ hb (u₀ x))) v₀)) := by
  have hdiff : Tendsto (fun n ↦
      fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
        (Eventually.of_forall (fun x ↦ hb (u n x))) (v n) -
      fieldApply (fun x ↦ A (u n x)) (coeff_meas A hA (u n))
        (Eventually.of_forall (fun x ↦ hb (u n x))) v₀) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ norm_fieldApply_sub_le _ _ _ (v n) v₀)
    simpa using (hv.sub_const v₀).norm
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add (tendsto_fieldApply_fixed A hA hb u u₀ hu v₀)

end L2Contraction

namespace HardSphere

structure SmoothContraction where
  toFun : ℂ → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toFun
  zero : toFun 0 = 0
  derivative_le : ∀ z, ‖fderiv ℝ toFun z‖ ≤ 1

namespace SmoothContraction
variable (f : SmoothContraction)

lemma lipschitz : LipschitzWith 1 f.toFun :=
  lipschitzWith_of_nnnorm_fderiv_le (f.smooth.differentiable (by simp))
    (fun z ↦ NNReal.coe_le_coe.mp (f.derivative_le z))

lemma derivative_continuous : Continuous (fderiv ℝ f.toFun) :=
  f.smooth.continuous_fderiv (by simp)

lemma coordDerivative_comp {N : ℕ} {L : Length} {a : ℝ}
    (g : SmoothTest N L a) (p : Direction N) :
    coordDerivative N L (f.toFun ∘ g.toFun) p = fun X ↦
      fderiv ℝ f.toFun (g.toFun X) (coordDerivative N L g.toFun p X) := by
  funext X
  unfold coordDerivative
  rw [show (fun Y : LiftedConfiguration N ↦ (f.toFun ∘ g.toFun) (project N L Y)) =
    f.toFun ∘ (fun Y ↦ g.toFun (project N L Y)) from rfl]
  rw [fderiv_comp (representative N L X)
    (f.smooth.differentiable (by simp)).differentiableAt
    (g.smooth.differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, project_representative]

def composeTest {N : ℕ} {L : Length} {a : ℝ}
    (g : SmoothTest N L a) : SmoothTest N L a where
  toFun := f.toFun ∘ g.toFun
  smooth := f.smooth.comp g.smooth
  compact := g.compact.comp_left f.zero
  support_allowed := (tsupport_comp_subset f.zero g.toFun).trans g.support_allowed
  memLp := f.lipschitz.comp_memLp f.zero g.memLp
  partial_memLp := by
    intro p
    rw [f.coordDerivative_comp g p]
    have hm := f.derivative_continuous.comp_aestronglyMeasurable g.memLp.aestronglyMeasurable
    apply (g.partial_memLp p).of_le
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hm.prodMk (g.partial_memLp p).aestronglyMeasurable))
    exact Eventually.of_forall fun X ↦
      (fderiv ℝ f.toFun (g.toFun X)).le_opNorm _ |>.trans
        (by nlinarith [f.derivative_le (g.toFun X),
          norm_nonneg (coordDerivative N L g.toFun p X)])

def onScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) : ScalarL2 N L :=
  f.lipschitz.compLp f.zero u

def onPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) : ScalarL2 N L :=
  L2Contraction.fieldApply (fun X ↦ fderiv ℝ f.toFun (u X))
    (L2Contraction.coeff_meas _ f.derivative_continuous u)
    (Eventually.of_forall (fun X ↦ f.derivative_le (u X))) v

def onJet {N : ℕ} {L : Length} (u : Jet N L) : Jet N L :=
  (f.onScalar u.1, fun p ↦ f.onPartial u.1 (u.2 p))

lemma coe_onScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun (u X) := f.lipschitz.coeFn_compLp f.zero u

lemma coe_onPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) :
    f.onPartial u v =ᵐ[volume] fun X ↦ fderiv ℝ f.toFun (u X) (v X) :=
  L2Contraction.coe_fieldApply _ _ _ v

lemma jet_composeTest {N : ℕ} {L : Length} {a : ℝ}
    (g : SmoothTest N L a) : (f.composeTest g).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(f.composeTest g).memLp.coeFn_toLp, f.coe_onScalar g.jet.1,
      g.memLp.coeFn_toLp] with X h1 h2 h3
    change g.jet.1 X = g.toFun X at h3
    change (f.composeTest g).jet.1 X = f.toFun (g.toFun X) at h1
    change (f.composeTest g).jet.1 X = f.onScalar g.jet.1 X
    rw [h1, h2, h3]
  · funext p
    apply Lp.ext
    filter_upwards [(f.composeTest g).partial_memLp p |>.coeFn_toLp,
      f.coe_onPartial g.jet.1 (g.jet.2 p), g.memLp.coeFn_toLp,
      (g.partial_memLp p).coeFn_toLp] with X h1 h2 h3 h4
    change (f.composeTest g).jet.2 p X = coordDerivative N L (f.toFun ∘ g.toFun) p X at h1
    change g.jet.1 X = g.toFun X at h3
    change g.jet.2 p X = coordDerivative N L g.toFun p X at h4
    change (f.composeTest g).jet.2 p X = f.onPartial g.jet.1 (g.jet.2 p) X
    rw [h1, h2]
    rw [f.coordDerivative_comp g p, h3, h4]

lemma onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) : f.onJet u ∈ dirichletDomain N L a := by
  obtain ⟨v, hv, hl⟩ := mem_closure_iff_seq_limit.mp hu
  choose g hg using hv
  have hl' : Tendsto (fun n ↦ (g n).jet) atTop (𝓝 u) := by simpa only [hg] using hl
  have hs := (continuous_fst.tendsto u).comp hl'
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  have hlim : Tendsto (fun n ↦ (f.composeTest (g (ns n))).jet) atTop (𝓝 (f.onJet u)) := by
    simp only [f.jet_composeTest]
    apply Tendsto.prodMk_nhds
    · exact (f.lipschitz.continuous_compLp f.zero).continuousAt.tendsto.comp
        (hs.comp hns.tendsto_atTop)
    · apply tendsto_pi_nhds.mpr
      intro p
      apply L2Contraction.tendsto_fieldApply _ f.derivative_continuous f.derivative_le
        _ u.1 hae _ (u.2 p)
      exact ((continuous_apply p).tendsto u.2).comp
        ((continuous_snd.tendsto u).comp (hl'.comp hns.tendsto_atTop))
  exact isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall fun n ↦ subset_closure ⟨f.composeTest (g (ns n)), rfl⟩)

lemma energy_onJet_le {N : ℕ} {L : Length} (u : Jet N L) :
    energy (f.onJet u) ≤ energy u := by
  apply Finset.sum_le_sum
  intro p _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact L2Contraction.norm_fieldApply_le _
    (L2Contraction.coeff_meas _ f.derivative_continuous u.1)
    (Eventually.of_forall fun X ↦ f.derivative_le (u.1 X)) (u.2 p)

end SmoothContraction
end HardSphere

open scoped RealInnerProductSpace

end

end OAI
