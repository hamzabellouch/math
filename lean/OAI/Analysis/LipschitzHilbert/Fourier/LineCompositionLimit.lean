import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingDecay
import OAI.Analysis.LipschitzHilbert.Trees.LineSamplingL2Path

namespace OAI

/-! Strong convergence of sampling operators under bounded pointwise
convergence of Lipschitz directions. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingL2Path_schwartz_tendsto
    (v : ℕ → ℝ → ℝ) (u : ℝ → ℝ) (hv : ∀ n, LipschitzWith 1 (v n)) (hu : LipschitzWith 1 u)
    (hvb : ∀ n y, |v n y|≤1) (hub : ∀ y, |u y|≤1)
    (hlim : ∀ y, Tendsto (fun n => v n y) atTop (𝓝 (u y)))
    (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => lineSamplingL2Path (v n) (hv n) t (f.toLp 2 volume)) atTop
      (𝓝 (lineSamplingL2Path u hu t (f.toLp 2 volume))) := by
  let F := fun n y => f (lineSampling (v n) t y)
  let g := fun y => f (lineSampling u t y)
  have hF (n : ℕ) : MemLp (F n) 2 volume :=
    (line_memLp_comp _ (lineSampling_lipschitz (v n) (hv n) t ht).continuous.measurable
      (lineSampling_antilipschitz (v n) (hv n) t ht) f f.continuous.measurable (f.memLp 2 volume)).1
  have hg : MemLp g 2 volume :=
    (line_memLp_comp _ (lineSampling_lipschitz u hu t ht).continuous.measurable
      (lineSampling_antilipschitz u hu t ht) f f.continuous.measurable (f.memLp 2 volume)).1
  have hb : ∀ n y, ‖F n y-g y‖≤8*lineSchwartzDecayConstant f/(1+|y|)^2 := by
    intro n y
    have hvsmall : |t*v n y|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hvb n y) (abs_nonneg t)).trans (by linarith)
    have husmall : |t*u y|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hub y) (abs_nonneg t)).trans (by linarith)
    calc
      _ ≤ ‖f (y-t*v n y)‖+‖f (y-t*u y)‖ := norm_sub_le _ _
      _ ≤ 4*lineSchwartzDecayConstant f/(1+|y|)^2+
          4*lineSchwartzDecayConstant f/(1+|y|)^2 :=
        add_le_add (lineSchwartz_shift_decay f y (t*v n y) hvsmall)
          (lineSchwartz_shift_decay f y (t*u y) husmall)
      _ = _ := by ring
  have hp (y : ℝ) : Tendsto (fun n => F n y) atTop (𝓝 (g y)) :=
    f.continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul (hlim y)))
  have hh := lineLp_tendsto_dominated F g hF hg _ (lineSchwartz_shift_envelope_integrable f)
    (Eventually.of_forall hb) hp
  simpa only [lineSamplingL2Path,dite_eq_left ht,lineCompositionL2_onSchwartz,lineCompositionToL2,LinearMap.coe_mk,AddHom.coe_mk,F,g,Function.comp_def] using hh

theorem lineL2_tendsto_of_schwartz
    (C : ℕ → Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (D : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hC : ∀ n, ‖C n‖≤2) (hD : ‖D‖≤2)
    (hlim : ∀ g : SchwartzMap ℝ ℂ, Tendsto (fun n => C n (g.toLp 2 volume)) atTop (𝓝 (D (g.toLp 2 volume))))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => C n f) atTop (𝓝 (D f)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  obtain ⟨g,hg⟩ := hd.exists_dist_lt f (show 0<eps/8 by positivity)
  have hg' : ‖f-g.toLp 2 volume‖<eps/8 := by simpa only [dist_eq_norm,norm_sub_rev] using hg
  filter_upwards [(Metric.tendsto_nhds.mp (hlim g)) (eps/2) (by positivity)] with n hn
  rw [dist_eq_norm] at hn ⊢
  have h1 : ‖C n f-C n (g.toLp 2 volume)‖≤2*‖f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    exact ((C n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  have h2 : ‖D (g.toLp 2 volume)-D f‖≤2*‖f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    have hh := (D.le_opNorm (g.toLp 2 volume-f)).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    simpa only [norm_sub_rev] using hh
  have htri := norm_add_le (C n f-C n (g.toLp 2 volume))
    (C n (g.toLp 2 volume)-D (g.toLp 2 volume)+ (D (g.toLp 2 volume)-D f))
  have htri' := norm_add_le (C n (g.toLp 2 volume)-D (g.toLp 2 volume)) (D (g.toLp 2 volume)-D f)
  rw [sub_add_sub_cancel,sub_add_sub_cancel] at htri
  rw [sub_add_sub_cancel] at htri'
  linarith

theorem lineSamplingL2Path_tendsto
    (v : ℕ → ℝ → ℝ) (u : ℝ → ℝ) (hv : ∀ n, LipschitzWith 1 (v n)) (hu : LipschitzWith 1 u)
    (hvb : ∀ n y, |v n y|≤1) (hub : ∀ y, |u y|≤1)
    (hlim : ∀ y, Tendsto (fun n => v n y) atTop (𝓝 (u y)))
    (t : ℝ) (ht : |t|≤1/2) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => lineSamplingL2Path (v n) (hv n) t f) atTop
      (𝓝 (lineSamplingL2Path u hu t f)) :=
  lineL2_tendsto_of_schwartz _ _ (fun n => lineSamplingL2Path_bound (v n) (hv n) t)
    (lineSamplingL2Path_bound u hu t)
    (lineSamplingL2Path_schwartz_tendsto v u hv hu hvb hub hlim t ht) f

end LipschitzHilbert.PacketRepresentation

end

end OAI
