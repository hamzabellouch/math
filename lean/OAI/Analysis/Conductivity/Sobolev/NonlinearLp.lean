import Mathlib
import OAI.Analysis.Conductivity.Variational.MatrixFiniteLaminate

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma unifIntegrable_of_norm_domination
    {X E F ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} {p : ℝ≥0∞} {f : ι → X → E} {g : ι → X → F}
    (hf : UnifIntegrable f p μ) (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖≤‖f i x‖) :
    UnifIntegrable g p μ := by
  apply unifIntegrable_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := unifIntegrable_iff.mp hf ε hε
  refine ⟨δ,hδ,fun index region hregion => ?_⟩
  exact (eLpNorm_mono_ae (hg index).restrict
    ((hfg index).filter_mono ae_restrict_le)).trans (hb index region hregion)

lemma continuous_comp_tendstoInMeasure
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X → E} {g : X → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : TendstoInMeasure μ f atTop g) {T : E → F} (hT : Continuous T) :
    TendstoInMeasure μ (fun n x => T (f n x)) atTop (fun x => T (g x)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => hT.comp_aestronglyMeasurable (hf n))).mpr
  intro ns hns
  obtain ⟨ms,hms,hlim⟩ := (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hlim] with x hx
  exact hT.continuousAt.tendsto.comp hx

lemma nonlinear_memLp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) {T : E → F} (hT : Continuous T) {C : ℝ}
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) (f : Lp E 2 μ) :
    MemLp (fun x => T (f x)) 2 μ := by
  apply ((Lp.memLp f).const_smul C).mono (hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  filter_upwards [] with x
  simpa only [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hC] using hb (f x)

def nonlinearLp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) (T : E → F) (hT : Continuous T) (C : ℝ)
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) (f : Lp E 2 μ) : Lp F 2 μ :=
  (nonlinear_memLp μ hT hC hb f).toLp _

lemma nonlinearLp_coe_ae
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) (T : E → F) (hT : Continuous T) (C : ℝ)
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) (f : Lp E 2 μ) :
    nonlinearLp μ T hT C hC hb f =ᵐ[μ] fun x => T (f x) :=
  MemLp.coeFn_toLp _

theorem nonlinearLp_continuous
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure X) [IsFiniteMeasure μ] (T : E → F) (hT : Continuous T) (C : ℝ)
    (hC : 0≤C) (hb : ∀ z, ‖T z‖≤C*‖z‖) :
    Continuous (nonlinearLp μ T hT C hC hb) := by
  apply continuous_iff_seqContinuous.mpr
  intro f g hfg
  have hfI := continuous_comp_tendstoInMeasure (fun n => Lp.aestronglyMeasurable (f n))
    (tendstoInMeasure_of_tendsto_Lp hfg) hT
  have hCseq : Tendsto (fun n => C • f n) atTop (𝓝 (C • g)) := hfg.const_smul C
  have hUI := unifIntegrable_of_tendsto_Lp (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun n => Lp.memLp (C • f n)) (Lp.memLp (C • g))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hCseq)
  have hUI' : UnifIntegrable (fun n x => T (f n x)) 2 μ := by
    apply unifIntegrable_of_norm_domination hUI
      (fun n => hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f n)))
    intro n
    filter_upwards [Lp.coeFn_smul C (f n)] with x hx
    rw [hx,Pi.smul_apply,norm_smul,Real.norm_of_nonneg hC]
    exact hb (f n x)
  have hnorm := tendsto_Lp_finite_of_tendstoInMeasure (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun n => hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f n)))
    (nonlinear_memLp μ hT hC hb g) hUI' hfI
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply hnorm.congr
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [nonlinearLp_coe_ae μ T hT C hC hb (f n),
    nonlinearLp_coe_ae μ T hT C hC hb g] with x hx hy
  simp only [Function.comp_apply,Pi.sub_apply,hx,hy]

instance ballMeasure_finite : IsFiniteMeasure ballMeasure := by
  exact isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne

lemma smoothJets_zero : (0 : JetSpace) ∈ smoothJets := by
  obtain ⟨f,hf,_,_,hm,he⟩ := compactSmoothJets_zero
  exact ⟨f,hf,hm,he⟩

lemma smoothJets_add {z w : JetSpace} (hz : z∈smoothJets) (hw : w∈smoothJets) :
    z+w∈smoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  obtain ⟨g,hg,hgm,rfl⟩ := hw
  have hj := smoothJet_add (hf.differentiable (by simp)) (hg.differentiable (by simp))
  have hm : MemLp (smoothJet (f+g)) 2 ballMeasure := by rw [hj]; exact hfm.add hgm
  refine ⟨f+g,hf.add hg,hm,?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (hfm.toLp _) (hgm.toLp _),hfm.coeFn_toLp,
    hgm.coeFn_toLp,hm.coeFn_toLp] with x ha hx hy hz
  rw [ha,hz,hj]
  simp only [Pi.add_apply,hx,hy]

lemma smoothJets_smul (c : ℝ) {z : JetSpace} (hz : z∈smoothJets) :
    c • z∈smoothJets := by
  obtain ⟨f,hf,hfm,rfl⟩ := hz
  have hj := smoothJet_smul c (hf.differentiable (by simp))
  have hm : MemLp (smoothJet (c • f)) 2 ballMeasure := by rw [hj]; exact hfm.const_smul c
  refine ⟨c • f,hf.const_smul c,hm,?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (hfm.toLp _),hfm.coeFn_toLp,hm.coeFn_toLp] with x ha hx hy
  rw [ha,hy,hj]
  simp only [Pi.smul_apply,hx]

lemma span_smoothJets : (Submodule.span ℝ smoothJets : Set JetSpace)=smoothJets := by
  let K : Submodule ℝ JetSpace := {
    carrier := smoothJets
    zero_mem' := smoothJets_zero
    add_mem' := smoothJets_add
    smul_mem' := smoothJets_smul }
  exact congrArg SetLike.coe (Submodule.span_eq K)

lemma H1Space_eq_closure : (H1Space : Set JetSpace)=closure smoothJets := by
  change closure (Submodule.span ℝ smoothJets : Set JetSpace)=closure smoothJets
  rw [span_smoothJets]

lemma zeroTraceAmbient_eq_closure : (zeroTraceAmbient : Set JetSpace)=closure compactSmoothJets := by
  change closure (Submodule.span ℝ compactSmoothJets : Set JetSpace)=closure compactSmoothJets
  rw [span_compactSmoothJets]

lemma nonlinear_closure_preservation {X : Type*} [TopologicalSpace X]
    {T : X → X} (hT : Continuous T) {S : Set X} (hS : MapsTo T S S) :
    MapsTo T (closure S) (closure S) := by
  intro x hx
  exact (image_closure_subset_closure_image hT).trans (closure_mono hS.image_subset) ⟨x,hx,rfl⟩

def jetSuperposition (g dg : ℝ → ℝ) (z : JetFiber) : JetFiber :=
  jetLiftValue (g (jetValue z)) + jetLiftGradient (dg (jetValue z) • jetGradient z)

lemma jetSuperposition_continuous {g dg : ℝ → ℝ} (hg : Continuous g) (hdg : Continuous dg) :
    Continuous (jetSuperposition g dg) := by
  exact (jetLiftValue.continuous.comp (hg.comp jetValue.continuous)).add
    (jetLiftGradient.continuous.comp ((hdg.comp jetValue.continuous).smul jetGradient.continuous))

def jetSuperpositionBound (C : ℝ) : ℝ :=
  ‖jetLiftValue‖*C*‖jetValue‖ + ‖jetLiftGradient‖*C*‖jetGradient‖

lemma jetSuperpositionBound_nonneg {C : ℝ} (hC : 0≤C) : 0≤jetSuperpositionBound C := by
  unfold jetSuperpositionBound
  positivity

lemma jetSuperposition_bound {g dg : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hg : ∀ r, ‖g r‖≤C*‖r‖) (hdg : ∀ r, ‖dg r‖≤C) (z : JetFiber) :
    ‖jetSuperposition g dg z‖≤jetSuperpositionBound C*‖z‖ := by
  have hval := jetValue.le_opNorm z
  have hgrad := jetGradient.le_opNorm z
  have h1 := jetLiftValue.le_opNorm (g (jetValue z))
  have h2 := jetLiftGradient.le_opNorm (dg (jetValue z) • jetGradient z)
  rw [norm_smul] at h2
  calc
    _ ≤ ‖jetLiftValue (g (jetValue z))‖ +
        ‖jetLiftGradient (dg (jetValue z) • jetGradient z)‖ := norm_add_le _ _
    _ ≤ ‖jetLiftValue‖*(C*(‖jetValue‖*‖z‖)) +
        ‖jetLiftGradient‖*(C*(‖jetGradient‖*‖z‖)) := by
      apply add_le_add
      · exact h1.trans (mul_le_mul_of_nonneg_left ((hg _).trans
          (mul_le_mul_of_nonneg_left hval hC)) (norm_nonneg _))
      · exact h2.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul (hdg _) hgrad (norm_nonneg _) hC) (norm_nonneg _))
    _ = _ := by unfold jetSuperpositionBound; ring

lemma gradient_comp_scalar {g dg : ℝ → ℝ} (hdg : ∀ r, HasDerivAt g (dg r) r)
    {f : R3 → ℝ} (hf : Differentiable ℝ f) (x : R3) :
    gradient (g ∘ f) x = dg (f x) • gradient f x := by
  unfold gradient
  rw [((hdg (f x)).comp_hasFDerivAt x (hf x).hasFDerivAt).fderiv]
  simp

lemma smoothJet_comp {g dg : ℝ → ℝ} (hdg : ∀ r, HasDerivAt g (dg r) r)
    {f : R3 → ℝ} (hf : Differentiable ℝ f) (x : R3) :
    smoothJet (g ∘ f) x = jetSuperposition g dg (smoothJet f x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change g (f x)=g (f x)+0; simp
  · change gradient (g ∘ f) x j = 0 + (dg (f x) • gradient f x) j
    rw [gradient_comp_scalar hdg hf]
    simp

end ScalarConductivity

end

end OAI
