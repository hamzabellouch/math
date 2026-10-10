import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Basis

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
section Cut
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def cutLinear (s : Set α) (hs : MeasurableSet s) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun u := ((Lp.memLp u).indicator hs).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (u+v)).indicator hs).coeFn_toLp,
      ((Lp.memLp u).indicator hs).coeFn_toLp, ((Lp.memLp v).indicator hs).coeFn_toLp,
      Lp.coeFn_add (((Lp.memLp u).indicator hs).toLp _)
        (((Lp.memLp v).indicator hs).toLp _), Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.add_apply, h2, h3]
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using h5
    · simp only [Set.indicator_of_notMem hx, add_zero]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (c • u)).indicator hs).coeFn_toLp,
      ((Lp.memLp u).indicator hs).coeFn_toLp,
      Lp.coeFn_smul c (((Lp.memLp u).indicator hs).toLp _), Lp.coeFn_smul c u]
      with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h3, Pi.smul_apply, h2]
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx, Pi.smul_apply] using h4
    · simp only [Set.indicator_of_notMem hx, smul_zero]

lemma cutLinear_norm_le (s : Set α) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖cutLinear (μ := μ) s hs u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [((Lp.memLp u).indicator hs).coeFn_toLp] with x hx
  change ‖((Lp.memLp u).indicator hs).toLp _ x‖ ≤ _
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

def cut (s : Set α) (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (cutLinear s hs).mkContinuous 1 (fun u => by simpa using cutLinear_norm_le s hs u)

lemma cut_norm_sq (s : Set α) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖cut (μ := μ) s hs u‖^2 = ∫ x in s, ‖u x‖^2 ∂μ := by
  rw [l2_norm_sq, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp u).indicator hs).coeFn_toLp] with x hx
  change ‖((Lp.memLp u).indicator hs).toLp _ x‖^2 = _
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

end Cut

open scoped InnerProductSpace

def selectedFrame (g : 𝓢(V, ℝ)) (s : Set (V × V)) (hs : MeasurableSet s) :
    Lp ℂ 2 (volume : Measure V) →L[ℂ]
      Lp ℂ 2 ((volume : Measure V).prod (volume : Measure V)) :=
  cut s hs ∘L frame g

def densityMatrix (g : 𝓢(V, ℝ)) (s : Set (V × V)) (hs : MeasurableSet s) :
    Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (selectedFrame g s hs).adjoint ∘L selectedFrame g s hs

lemma densityMatrix_positive (g : 𝓢(V, ℝ)) (s : Set (V × V)) (hs : MeasurableSet s) :
    (densityMatrix g s hs).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

lemma selectedFrame_norm_le (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (s : Set (V × V)) (hs : MeasurableSet s) (u : Lp ℂ 2 (volume : Measure V)) :
    ‖selectedFrame g s hs u‖ ≤ ‖u‖ := by
  change ‖cut s hs (frame g u)‖ ≤ _
  exact (cutLinear_norm_le s hs (frame g u)).trans (frame_norm g hg u).le

lemma densityMatrix_le_one (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (s : Set (V × V)) (hs : MeasurableSet s) :
    (1 - densityMatrix g s hs).IsPositive := by
  refine ⟨ContinuousLinearMap.isPositive_one.isSymmetric.sub
    (densityMatrix_positive g s hs).isSymmetric, fun u => ?_⟩
  change 0 ≤ (inner ℂ ((1 - densityMatrix g s hs) u) u).re
  rw [sub_apply, one_apply_eq_self, inner_sub_left,
    Complex.sub_re, inner_self_eq_norm_sq_to_K]
  simp only [← RCLike.ofReal_pow]
  change 0 ≤ ‖u‖^2 - (inner ℂ (densityMatrix g s hs u) u).re
  rw [show (inner ℂ (densityMatrix g s hs u) u).re = ‖selectedFrame g s hs u‖^2 from
    (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left (selectedFrame g s hs) u).symm]
  exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (selectedFrame_norm_le g hg s hs u) 2)

lemma densityMatrix_schwartz_form (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (s : Set (V × V)) (hs : MeasurableSet s) (v : 𝓢(V, ℂ)) :
    (inner ℂ (densityMatrix g s hs (v.toLp 2 volume)) (v.toLp 2 volume)).re =
      ∫ p in s, ‖frameFunction g v p‖^2 ∂((volume : Measure V).prod volume) := by
  rw [show (inner ℂ (densityMatrix g s hs (v.toLp 2 volume)) (v.toLp 2 volume)).re =
    ‖selectedFrame g s hs (v.toLp 2 volume)‖^2 from
    (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left (selectedFrame g s hs) (v.toLp 2 volume)).symm]
  change ‖cut s hs (frame g (v.toLp 2 volume))‖^2 = _
  rw [frame_toLp g hg, cut_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (frameFunction_memLp g v).coeFn_toLp] with p hp
  change ‖(frameFunction_memLp g v).toLp _ p‖^2 = _
  rw [hp]

def packetFunction (g : 𝓢(V, ℝ)) (p : V × V) (x : V) : ℂ :=
  conj ((Real.fourierChar (-inner ℝ x p.2) : Circle) : ℂ) * (g (x-p.1) : ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma packetFunction_norm (g : 𝓢(V, ℝ)) (p : V × V) (x : V) :
    ‖packetFunction g p x‖ = ‖g (x-p.1)‖ := by
  simp [packetFunction, Circle.norm_coe]

lemma packetFunction_memLp (g : 𝓢(V, ℝ)) (p : V × V) :
    MemLp (packetFunction g p) 2 (volume : Measure V) := by
  have h : Continuous (packetFunction g p) := by
    unfold packetFunction
    fun_prop
  exact ((g.compSubConstCLM ℝ p.1).memLp 2 volume).congr_norm h.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [SchwartzMap.compSubConstCLM_apply] using (packetFunction_norm g p x).symm)

def packet (g : 𝓢(V, ℝ)) (p : V × V) : Lp ℂ 2 (volume : Measure V) :=
  (packetFunction_memLp g p).toLp _

lemma packet_norm_sq (g : 𝓢(V, ℝ)) (p : V × V) :
    ‖packet g p‖^2 = ∫ x : V, g x^2 := by
  rw [l2_norm_sq]
  calc
    _ = ∫ x : V, g (x-p.1)^2 := by
      apply integral_congr_ae
      filter_upwards [(packetFunction_memLp g p).coeFn_toLp] with x hx
      change ‖(packetFunction_memLp g p).toLp _ x‖^2 = _
      rw [hx, packetFunction_norm, Real.norm_eq_abs, sq_abs]
    _ = _ := integral_sub_right_eq_self (fun x : V => g x^2) p.1

lemma packet_frameFunction (g : 𝓢(V, ℝ)) (p : V × V) (v : 𝓢(V, ℂ)) :
    inner ℂ (packet g p) (v.toLp 2 volume) = frameFunction g v p := by
  rw [L2.inner_def]
  simp only [frameFunction, SchwartzMap.fourier_coe, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [(packetFunction_memLp g p).coeFn_toLp, v.coeFn_toLp 2 volume] with x h1 h2
  change inner ℂ ((packetFunction_memLp g p).toLp _ x) _ = _
  rw [h1, h2, RCLike.inner_apply, packetFunction, windowed_apply]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, Circle.smul_def, smul_eq_mul]
  ring

lemma frame_ae_packet (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (v : Lp ℂ 2 (volume : Measure V)) :
    (frame g v : V × V → ℂ) =ᵐ[(volume : Measure V).prod volume]
      fun p => inner ℂ (packet g p) v := by
  have hd := SchwartzMap.denseRange_toLpCLM (μ := (volume : Measure V))
    (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
  obtain ⟨u, hu, hv⟩ := mem_closure_iff_seq_limit.1 (hd v)
  choose w hw using hu
  have hfr := (frame g).continuous.tendsto v |>.comp hv
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfr).exists_seq_tendsto_ae
  have heq (n : ℕ) : (frame g (u n) : V × V → ℂ) =ᵐ[(volume : Measure V).prod volume]
      fun p => inner ℂ (packet g p) (u n) := by
    rw [← hw n, SchwartzMap.toLpCLM_apply, frame_toLp g hg]
    filter_upwards [(frameFunction_memLp g (w n)).coeFn_toLp] with p hp
    exact hp.trans (packet_frameFunction g p (w n)).symm
  filter_upwards [hae, ae_all_iff.2 heq] with p hp hp'
  have hlim : Tendsto (fun n => inner ℂ (packet g p) (u (ns n))) atTop
      (𝓝 (inner ℂ (packet g p) v)) := tendsto_const_nhds.inner (hv.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique (hp.congr' (Filter.Eventually.of_forall fun n => hp' (ns n))) hlim

end CoulombPackets

end

end OAI
