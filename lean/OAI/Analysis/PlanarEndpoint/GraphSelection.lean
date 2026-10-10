import OAI.Analysis.PlanarEndpoint.DualMass
import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.FrequencyWeak
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.MaximalBridge
import OAI.Analysis.PlanarEndpoint.SobolevGraph
import OAI.Analysis.PlanarEndpoint.WeightedGraph

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace PlanarEndpoint

lemma graph_evolution_pairing_bound {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : L2), BoundedFourierSupport f → InHThird f →
      ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ), Measurable T → Measurable w →
      (∀ x, ‖w x‖ ≤ 1) → (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) →
      ‖∫ x in Metric.ball x₀ 1, w x * evolution f x (T x)‖ ≤ C*hThirdNorm f := by
  obtain ⟨C,hC,hbound⟩ := graph_sobolev_pairing_bound hp hshort
  refine ⟨((2*Real.pi)^2)⁻¹*C,by positivity,?_⟩
  intro f hf hH x₀ T w hT hw hb ht
  have hh := hbound f hf hH x₀ T w hT hw hb ht
  rw [graphFourier_frequency_pairing hf.integrable _ hT hw hb] at hh
  have he : (∫ x in Metric.ball x₀ 1, w x*evolution f x (T x)) =
      (((2*Real.pi)^2)⁻¹:ℝ) • ∫ x in Metric.ball x₀ 1,
        w x*frequencyExtension (fourier f) x (T x) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [evolution,frequencyExtension,Complex.real_smul]
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ((2*Real.pi)^2)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

def normingPhase (z : ℂ) : ℂ := (starRingEnd ℂ) z / (‖z‖ : ℂ)

lemma normingPhase_measurable : Measurable normingPhase :=
  Complex.continuous_conj.measurable.div (Complex.measurable_ofReal.comp measurable_norm)

lemma normingPhase_norm (z : ℂ) : ‖normingPhase z‖ ≤ 1 := by
  rw [normingPhase,norm_div,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)]
  exact div_self_le_one _

lemma normingPhase_mul (z : ℂ) : normingPhase z*z = (‖z‖ : ℂ) := by
  by_cases hz : z=0
  · simp [hz,normingPhase]
  · have hn : (‖z‖:ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    rw [normingPhase,div_mul_eq_mul_div,Complex.conj_mul']
    field_simp

lemma measurable_graph_evolution (f : L2) (hf : Integrable (fourier f) volume)
    {T : Plane → ℝ} (hT : Measurable T) : Measurable (fun x => evolution f x (T x)) := by
  have hgraph : Measurable (fun x : Plane => (x,T x)) := measurable_id.prodMk hT
  change Measurable ((fun z : Plane × ℝ => evolution f z.1 z.2) ∘ (fun x => (x,T x)))
  exact (continuous_evolution hf).measurable.comp hgraph

lemma graph_evolution_norm_integrable (f : L2) (hf : Integrable (fourier f) volume)
    (x₀ : Plane) {T : Plane → ℝ} (hT : Measurable T) :
    Integrable (fun x => ‖evolution f x (T x)‖) (volume.restrict (Metric.ball x₀ 1)) := by
  have hm : Measurable (fun x => evolution f x (T x)) :=
    measurable_graph_evolution f hf hT
  apply (integrable_const ((((2*Real.pi)^2)⁻¹:ℝ) * ∫ ξ, ‖fourier f ξ‖)).mono'
    hm.norm.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using
    norm_evolution_le_fourierL1 f x (T x)

lemma graph_evolution_norm_bound {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : L2), BoundedFourierSupport f → InHThird f →
      ∀ (x₀ : Plane) (T : Plane → ℝ), Measurable T →
      (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) →
      (∫ x in Metric.ball x₀ 1, ‖evolution f x (T x)‖) ≤ C*hThirdNorm f := by
  obtain ⟨C,hC,hbound⟩ := graph_evolution_pairing_bound hp hshort
  refine ⟨C,hC,?_⟩
  intro f hf hH x₀ T hT ht
  let w := fun x => normingPhase (evolution f x (T x))
  have hw : Measurable w := normingPhase_measurable.comp
    (measurable_graph_evolution f hf.integrable hT)
  have hh := hbound f hf hH x₀ T w hT hw (fun x => normingPhase_norm _) ht
  have he : (fun x => w x*evolution f x (T x)) = fun x => (‖evolution f x (T x)‖ : ℂ) :=
    funext (fun x => normingPhase_mul _)
  rw [he,integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  exact hh

abbrev HalfTime := ↥(Ico (0:ℝ) 1)
instance halfTime_nonempty : Nonempty HalfTime := ⟨⟨0,by constructor <;> norm_num⟩⟩

def denseTime : ℕ → HalfTime := TopologicalSpace.denseSeq HalfTime
lemma denseTime_dense : DenseRange denseTime := TopologicalSpace.denseRange_denseSeq HalfTime

lemma denseTime_bound {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ n, ‖g (denseTime n)‖ ≤ B) : ∀ t ∈ Icc (0:ℝ) 1, ‖g t‖ ≤ B := by
  have hh : Ico (0:ℝ) 1 ⊆ {t | ‖g t‖ ≤ B} := by
    intro t ht
    exact denseTime_dense.induction_on (p := fun s : HalfTime => ‖g s.val‖ ≤ B) (⟨t,ht⟩ : HalfTime)
      (isClosed_le (hg.comp continuous_subtype_val).norm continuous_const) hB
  have hc := closure_minimal hh (isClosed_le hg.norm continuous_const)
  rw [closure_Ico (by norm_num : (0:ℝ)≠1)] at hc
  exact hc

lemma exists_denseTime_near_path (f : L2) (hf : Integrable (fourier f) volume)
    (x : Plane) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ‖evolutionPath f hf x‖-ε < ‖evolution f x (denseTime n)‖ := by
  by_contra! hh
  have hpos : 0 ≤ ‖evolutionPath f hf x‖-ε := (norm_nonneg _).trans (hh 0)
  have hbound := denseTime_bound ((continuous_evolution hf).comp
    (continuous_const.prodMk continuous_id)) hh
  have hn : ‖evolutionPath f hf x‖ ≤ ‖evolutionPath f hf x‖-ε :=
    (ContinuousMap.norm_le _ hpos).2 (fun t => hbound t.val t.property)
  linarith

lemma exists_measurable_near_time (f : L2) (hf : Integrable (fourier f) volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Plane → ℝ, Measurable T ∧ (∀ x, T x ∈ Ico 0 1) ∧
      ∀ x, ‖evolutionPath f hf x‖ ≤ ‖evolution f x (T x)‖+ε := by
  classical
  let h := fun x => exists_denseTime_near_path f hf x hε
  let T := fun x => (denseTime (Nat.find (h x))).val
  refine ⟨T,?_,fun x => (denseTime (Nat.find (h x))).property,?_⟩
  · exact Measurable.find (f := fun n (_ : Plane) => (denseTime n).val)
      (fun n => measurable_const) (fun n =>
      measurableSet_lt ((continuous_evolutionPath f hf).norm.measurable.sub measurable_const)
        (((continuous_evolution hf).comp (continuous_id.prodMk continuous_const)).norm.measurable)) h
  · intro x
    have hh := Nat.find_spec (h x)
    dsimp [T]
    linarith

lemma localMaximalBound_of_shortTime {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) : LocalMaximalBound := by
  obtain ⟨C,hC,hbound⟩ := graph_evolution_norm_bound hp hshort
  refine ⟨C,hC,?_⟩
  intro f hf hH x₀
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T,hT,ht,ha⟩ := exists_measurable_near_time f hf.integrable
    (div_pos hε Real.pi_pos)
  have hmono := integral_mono (integrableOn_evolutionPath_ball f hf.integrable x₀).norm
    ((graph_evolution_norm_integrable f hf.integrable x₀ hT).add (integrable_const (ε/Real.pi))) ha
  simp only [Pi.add_apply] at hmono
  rw [integral_add (graph_evolution_norm_integrable f hf.integrable x₀ hT)
    (integrable_const (ε/Real.pi)), integral_const] at hmono
  have hm : (volume.restrict (Metric.ball x₀ 1)).real univ = Real.pi := by
    simpa only [measureReal_def,Measure.restrict_apply_univ] using unit_ball_real x₀
  rw [hm,smul_eq_mul] at hmono
  have hh := hbound f hf hH x₀ T hT (fun x _ => ht x)
  have he : Real.pi*(ε/Real.pi)=ε := by field_simp
  rw [he] at hmono
  linarith

lemma mainConclusion_of_shortTime {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) {f : L2} (hf : InHThird f) :
    MainConclusion f := mainConclusion_of_localMaximalBound
      (localMaximalBound_of_shortTime hp hshort) hf

end PlanarEndpoint
end

end OAI
