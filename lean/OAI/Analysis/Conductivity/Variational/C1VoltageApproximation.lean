import Mathlib
import OAI.Analysis.Conductivity.Scalarization.ConcreteFluxScalarization

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped ENNReal Convolution

abbrev CoordBump := ContDiffBump (0 : Coord3)

def coordDyadicBump (n : ℕ) : CoordBump where
  rIn := (1/2:ℝ)^(n+1)
  rOut := (1/2:ℝ)^n
  rIn_pos := by positivity
  rIn_lt_rOut := by
    rw [pow_succ]
    have h : 0<(1/2:ℝ)^n := by positivity
    linarith

lemma coordDyadicBump_radius : Tendsto (fun n => (coordDyadicBump n).rOut) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

def coordMollify (φ : CoordBump) (f : Coord3 → F) : Coord3 → F :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] in
lemma coordMollify_smooth (φ : CoordBump) {f : Coord3 → F} (hf : Continuous f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coordMollify φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

omit [MeasurableSpace F] [BorelSpace F] in
lemma coordMollify_bound (φ : CoordBump) {f : Coord3 → F} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x,‖f x‖≤M) (x : Coord3) : ‖coordMollify φ f x‖≤M := by
  have hM0 : 0≤M := (norm_nonneg (f 0)).trans (hM 0)
  have h := dist_convolution_le (μ := volume) (z₀ := (0:F)) hM0 φ.support_normed_eq.subset
    φ.nonneg_normed φ.integral_normed hf.aestronglyMeasurable
    (fun y (_ : y∈Metric.ball x φ.rOut) => by simpa using hM y)
  simpa only [coordMollify,dist_zero_right] using h

omit [CompleteSpace F] in
lemma coordMollify_memLp (φ : CoordBump) {f : Coord3 → F} (hf : Continuous f)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    MemLp (coordMollify φ f) 2 (volume.restrict U) :=
  continuous_memLp_bounded_coord (coordMollify_smooth φ hf).continuous hUb hUm

lemma coordMollify_toLp_tendsto {f : Coord3 → F} (hf : Continuous f)
    (hfc : HasCompactSupport f) {U : Set Coord3}
    (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    Tendsto (fun n => (coordMollify_memLp (coordDyadicBump n) hf hUb hUm).toLp _)
      atTop (𝓝 ((continuous_memLp_bounded_coord hf hUb hUm).toLp _)) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hfc.exists_bound_of_continuous hf
  have hM0 : 0≤M := (norm_nonneg (f 0)).trans (hM 0)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (coordMollify_smooth (coordDyadicBump n) hf).continuous.aestronglyMeasurable)
    (continuous_memLp_bounded_coord hf hUb hUm)
  · apply unifIntegrable_of_norm_domination
      (unifIntegrable_const (by norm_num : (1:ℝ≥0∞)≤2) (by norm_num)
        (memLp_const M))
      (fun index =>
        (coordMollify_smooth (coordDyadicBump index) hf).continuous.aestronglyMeasurable)
    intro n
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hM0] using
        coordMollify_bound (coordDyadicBump n) hf hM x)
  · exact ae_of_all _ (fun x => ContDiffBump.convolution_tendsto_right_of_continuous
      coordDyadicBump_radius hf x)

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
lemma coordMollify_fderiv {g : Coord3 → F} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (φ : CoordBump) :
    fderiv ℝ (coordMollify φ g)=coordMollify φ (fderiv ℝ g) := by
  funext x
  have h := (hgc.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.integrable_normed.locallyIntegrable hg x).fderiv
  exact h

theorem compact_C1_voltageJet_mem {g : Coord3 → Fin 2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) {U : Set Coord3}
    (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    ∃ (hv : MemLp g 2 (volume.restrict U))
      (hd : MemLp (voltageGradient g) 2 (volume.restrict U)),
      (hv.toLp _,hd.toLp _)∈voltageH1Jets volume U := by
  have hv := continuous_memLp_bounded_coord hg.continuous hUb hUm
  have hD := continuous_memLp_bounded_coord (hg.continuous_fderiv (by norm_num)) hUb hUm
  have hd : MemLp (voltageGradient g) 2 (volume.restrict U) :=
    gradientVectorCLM.comp_memLp' hD
  let gn (n : ℕ) := coordMollify (coordDyadicBump n) g
  have hgn (n : ℕ) : ContDiff ℝ (↑(⊤:ℕ∞)) (gn n) := coordMollify_smooth _ hg.continuous
  have hgv (n : ℕ) := coordMollify_memLp (coordDyadicBump n) hg.continuous hUb hUm
  have hgD (n : ℕ) : MemLp (fderiv ℝ (gn n)) 2 (volume.restrict U) := by
    rw [show fderiv ℝ (gn n)=coordMollify (coordDyadicBump n) (fderiv ℝ g) from
      coordMollify_fderiv hg hgc _]
    exact coordMollify_memLp _ (hg.continuous_fderiv (by norm_num)) hUb hUm
  have hgd (n : ℕ) : MemLp (voltageGradient (gn n)) 2 (volume.restrict U) :=
    gradientVectorCLM.comp_memLp' (hgD n)
  have he (f : Coord3 → Fin 2 → ℝ)
      (hdf : MemLp (fderiv ℝ f) 2 (volume.restrict U))
      (hgf : MemLp (voltageGradient f) 2 (volume.restrict U)) :
      gradientVectorCLM.compLpL 2 (volume.restrict U) (hdf.toLp _)=hgf.toLp _ := by
    apply Lp.ext
    filter_upwards [gradientVectorCLM.coeFn_compLp (hdf.toLp _),hdf.coeFn_toLp,hgf.coeFn_toLp]
      with x hx hy hz
    change (gradientVectorCLM.compLp (hdf.toLp _)) x = _
    rw [hx,hy,hz]
    rfl
  have hDt : Tendsto (fun n => (hgD n).toLp _) atTop (𝓝 (hD.toLp _)) := by
    convert coordMollify_toLp_tendsto (hg.continuous_fderiv (by norm_num))
      (hgc.fderiv ℝ) hUb hUm using 1
    ext n
    filter_upwards [(hgD n).coeFn_toLp,
      (coordMollify_memLp (coordDyadicBump n) (hg.continuous_fderiv (by norm_num)) hUb hUm).coeFn_toLp]
      with x hx hy
    rw [hx,hy,coordMollify_fderiv hg hgc]
  have hdt : Tendsto (fun n => (hgd n).toLp _) atTop (𝓝 (hd.toLp _)) := by
    have hh := (gradientVectorCLM.compLpL 2 (volume.restrict U)).continuous.tendsto (hD.toLp _) |>.comp hDt
    rw [he g hD hd] at hh
    convert hh using 1
    funext n
    exact (he (gn n) (hgD n) (hgd n)).symm
  refine ⟨hv,hd,?_⟩
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    ((coordMollify_toLp_tendsto hg.continuous hgc hUb hUm).prodMk_nhds hdt)
  exact Eventually.of_forall (fun n => (Submodule.span ℝ (smoothVoltageJets volume U)).le_topologicalClosure
    (Submodule.subset_span ⟨gn n,hgn n,hgv n,hgd n,rfl⟩))

theorem C1_voltageJet_mem {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    ∃ (hu : MemLp v 2 (volume.restrict U))
      (hd : MemLp (voltageGradient v) 2 (volume.restrict U)),
      (hu.toLp _,hd.toLp _)∈voltageH1Jets volume U := by
  obtain ⟨R,hR⟩ := hUb.exists_norm_le
  let φ : CoordBump := {
    rIn := max R 0+1
    rOut := max R 0+2
    rIn_pos := by have := le_max_right R 0; linarith
    rIn_lt_rOut := by linarith }
  let g : Coord3 → Fin 2 → ℝ := fun x => φ x • v x
  have hg : ContDiff ℝ 1 g := φ.contDiff.smul hv
  have hgc : HasCompactSupport g := φ.hasCompactSupport.smul_right
  have heq (x : Coord3) (hx : x∈U) : g =ᶠ[𝓝 x] v := by
    have hxball : x∈Metric.ball (0:Coord3) φ.rIn := by
      rw [Metric.mem_ball,dist_zero_right]
      have := hR x hx
      have := le_max_left R 0
      dsimp [φ]
      linarith
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hxball] with y hy
    dsimp [g]
    rw [hy]
    exact one_smul ℝ (v y)
  have hu := continuous_memLp_bounded_coord hv.continuous hUb hUm
  have hd : MemLp (voltageGradient v) 2 (volume.restrict U) :=
    gradientVectorCLM.comp_memLp'
      (continuous_memLp_bounded_coord (hv.continuous_fderiv (by norm_num)) hUb hUm)
  obtain ⟨hgu,hgd,hmem⟩ := compact_C1_voltageJet_mem hg hgc hUb hUm
  have huEq : hgu.toLp g=hu.toLp v := by
    apply Lp.ext
    filter_upwards [hgu.coeFn_toLp,hu.coeFn_toLp,ae_restrict_mem hUm] with x hx hy hz
    rw [hx,hy]
    exact (heq x hz).eq_of_nhds
  have hdEq : hgd.toLp (voltageGradient g)=hd.toLp (voltageGradient v) := by
    apply Lp.ext
    filter_upwards [hgd.coeFn_toLp,hd.coeFn_toLp,ae_restrict_mem hUm] with x hx hy hz
    rw [hx,hy]
    exact congrArg (fun D => fieldVector (gradientColumns D)) (heq x hz).fderiv_eq
  exact ⟨hu,hd,by rwa [huEq,hdEq] at hmem⟩

end ScalarConductivity

end
end

end OAI
