import OAI.Analysis.ModularRecovery.SpectralCalculus
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The measurable unitary gauge on the Hilbert space used for the modular
crossed product. This constructs the actual change of representation, not
a semifiniteness or nuclearity assumption. -/

noncomputable section
open Filter MeasureTheory

namespace BoundedRecovery.RealSpectralCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma continuous_unitary_action (D : RealSpectralCalculus H) :
    Continuous (fun p : ℝ × H => D.unitary p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (D.continuous_unitary_apply p.2).continuousAt (ε / 2) (half_pos hε)
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun {q} hq => ?_⟩
  have hmax : max (dist q.1 p.1) (dist q.2 p.2) < min δ (ε / 2) := hq
  have hq₁ : dist q.1 p.1 < δ :=
    (le_max_left _ _).trans_lt (hmax.trans_le (min_le_left _ _))
  have hq₂ : dist q.2 p.2 < ε / 2 :=
    (le_max_right _ _).trans_lt (hmax.trans_le (min_le_right _ _))
  have he : dist (D.unitary q.1 q.2) (D.unitary q.1 p.2) = dist q.2 p.2 := by
    simp only [dist_eq_norm, ← map_sub, D.norm_unitary_apply]
  exact (dist_triangle _ _ _).trans_lt (by rw [he]; linarith [hd hq₁])

variable (D : RealSpectralCalculus H) (μ : Measure ℝ)

lemma aestronglyMeasurable_unitary_gauge (c : ℝ) (f : ℝ → H)
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => D.unitary (c * t) (f t)) μ := by
  have ht : AEStronglyMeasurable (fun t : ℝ => c * t) μ :=
    (continuous_const.mul continuous_id).aestronglyMeasurable
  exact Continuous.comp_aestronglyMeasurable₂
    (g := fun t x => D.unitary t x) D.continuous_unitary_action ht hf

lemma memLp_unitary_gauge (c : ℝ) (f : Lp H 2 μ) :
    MemLp (fun t => D.unitary (c * t) (f t)) 2 μ :=
  (Lp.memLp f).congr_norm
    (D.aestronglyMeasurable_unitary_gauge μ c f (Lp.aestronglyMeasurable f))
    (Eventually.of_forall (fun t => (D.norm_unitary_apply (c * t) (f t)).symm))

def lpGauge (c : ℝ) (f : Lp H 2 μ) : Lp H 2 μ :=
  (D.memLp_unitary_gauge μ c f).toLp (fun t => D.unitary (c * t) (f t))

lemma lpGauge_ae (c : ℝ) (f : Lp H 2 μ) :
    D.lpGauge μ c f =ᵐ[μ] fun t => D.unitary (c * t) (f t) :=
  MemLp.coeFn_toLp _

lemma lpGauge_norm (c : ℝ) (f : Lp H 2 μ) : ‖D.lpGauge μ c f‖ = ‖f‖ := by
  rw [lpGauge, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (D.memLp_unitary_gauge μ c f).aestronglyMeasurable
    (Lp.aestronglyMeasurable f) (Eventually.of_forall fun t => D.norm_unitary_apply _ _)

lemma lpGauge_add (c : ℝ) (f g : Lp H 2 μ) :
    D.lpGauge μ c (f + g) = D.lpGauge μ c f + D.lpGauge μ c g := by
  apply Lp.ext
  filter_upwards [D.lpGauge_ae μ c (f + g), D.lpGauge_ae μ c f,
    D.lpGauge_ae μ c g, Lp.coeFn_add f g,
    Lp.coeFn_add (D.lpGauge μ c f) (D.lpGauge μ c g)] with t hfg hf hg ha hb
  simp only [hfg, ha, map_add, hb, hf, hg, Pi.add_apply]

lemma lpGauge_smul (c : ℝ) (a : ℂ) (f : Lp H 2 μ) :
    D.lpGauge μ c (a • f) = a • D.lpGauge μ c f := by
  apply Lp.ext
  filter_upwards [D.lpGauge_ae μ c (a • f), D.lpGauge_ae μ c f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (D.lpGauge μ c f)] with t haf hf ha hb
  simp only [haf, ha, map_smul, hb, hf, Pi.smul_apply]

lemma lpGauge_comp (c d : ℝ) (f : Lp H 2 μ) :
    D.lpGauge μ c (D.lpGauge μ d f) = D.lpGauge μ (c + d) f := by
  apply Lp.ext
  filter_upwards [D.lpGauge_ae μ c (D.lpGauge μ d f), D.lpGauge_ae μ d f,
    D.lpGauge_ae μ (c + d) f] with t hc hd hcd
  rw [hc, hd, hcd, add_mul, D.unitary_add, mul_apply_eq_comp]

@[simp] lemma lpGauge_zero (f : Lp H 2 μ) : D.lpGauge μ 0 f = f := by
  apply Lp.ext
  filter_upwards [D.lpGauge_ae μ 0 f] with t ht
  simpa only [zero_mul, D.unitary_zero, one_apply_eq_self] using ht

/-- A genuine Hilbert-space unitary, with inverse given by the opposite gauge. -/
def lpGaugeEquiv (c : ℝ) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp H 2 μ where
  toFun := D.lpGauge μ c
  invFun := D.lpGauge μ (-c)
  left_inv f := by rw [D.lpGauge_comp, neg_add_cancel, D.lpGauge_zero]
  right_inv f := by rw [D.lpGauge_comp, add_neg_cancel, D.lpGauge_zero]
  map_add' := D.lpGauge_add μ c
  map_smul' a f := by simpa only [RingHom.id_apply] using D.lpGauge_smul μ c a f
  norm_map' := D.lpGauge_norm μ c

@[simp] lemma lpGaugeEquiv_apply (c : ℝ) (f : Lp H 2 μ) :
    D.lpGaugeEquiv μ c f = D.lpGauge μ c f := rfl

/-- Conjugating a constant operator gives the modularly twisted measurable
operator field. The formula is an almost-everywhere equality on actual L². -/
lemma lpGauge_conjugate_constant_ae (c : ℝ) (T : H →L[ℂ] H) (f : Lp H 2 μ) :
    D.lpGauge μ c (T.compLpL 2 μ (D.lpGauge μ (-c) f)) =ᵐ[μ]
      fun t => D.unitary (c * t) (T (D.unitary (-(c * t)) (f t))) := by
  filter_upwards [D.lpGauge_ae μ c (T.compLpL 2 μ (D.lpGauge μ (-c) f)),
    T.coeFn_compLpL (p := 2) (μ := μ) (D.lpGauge μ (-c) f),
    D.lpGauge_ae μ (-c) f] with t hc hT hf
  rw [hc, hT, hf, neg_mul]

end BoundedRecovery.RealSpectralCalculus

end

end OAI
