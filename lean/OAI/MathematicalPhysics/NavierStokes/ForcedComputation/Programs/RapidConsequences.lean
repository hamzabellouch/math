import OAI.MathematicalPhysics.RapidForcing.JetControl
import OAI.MathematicalPhysics.RapidForcing.Energy

namespace OAI

/-! Slow-decay and space-time energy consequences of the addressed construction. -/

noncomputable section
open Set MeasureTheory
open scoped Topology SchwartzMap ENNReal

namespace RapidForcing

def SlowDecay (f : Field Space) : Prop :=
  ∀ l α, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x,
    ‖mixedD l α f t x‖ ≤ C * (1 + t)⁻¹ ^ (1 + l)

theorem spaceFinite : Module.Finite ℝ Space := inferInstance

theorem spaceBorel : BorelSpace Space := inferInstance

def SpaceTimeL2 (f : Field Space) : Prop :=
  letI := twoAtLeastTwo
  letI := spaceFinite
  letI := spaceBorel
  ∀ l α, MemLp (Function.uncurry (mixedD l α f)) 2
    (volume.restrict (Ici (0 : ℝ) ×ˢ (univ : Set Space)))

theorem Rapid.slowDecay {f : Field Space} (hf : Rapid f) : SlowDecay f := by
  intro l α
  obtain ⟨C, hC, hb⟩ := hf (1 + l) l α
  refine ⟨C, hC, fun t ht x => ?_⟩
  have hp : 0 < (1 + t) ^ (1 + l) := by positivity
  have h : ‖mixedD l α f t x‖ ≤ C / (1 + t) ^ (1 + l) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hb t ht x)
  simpa only [div_eq_mul_inv, inv_pow] using h

theorem JetControl.spaceTimeL2 {f : Field Space} {B : ℕ → ℕ → ℚ}
    (hf : JetControl f B) : SpaceTimeL2 f := by
  intro l α
  obtain ⟨g, hg, he, hb⟩ := hf.mixedD l α
  let : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let s : 𝓢(ℝ × Space, Space) := {
    toFun := g
    smooth' := hg
    decay' := by
      intro J k
      refine ⟨(B J (k + (l + α 0 + α 1 + α 2)) : ℝ), fun p => ?_⟩
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg p) (by linarith : ‖p‖ ≤ 1 + ‖p‖) J)
        (norm_nonneg (iteratedFDeriv ℝ k g p))).trans (hb J k p) }
  have heq : (fun p => s p) =ᶠ[ae (volume.restrict (Ici (0 : ℝ) ×ˢ (univ : Set Space)))]
      Function.uncurry (RapidForcing.mixedD l α f) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.prod MeasurableSet.univ)] with p hp
    exact (he p.1 hp.1 p.2).symm
  exact (memLp_congr_ae heq).mp
    ((s.memLp 2 volume).restrict (Ici (0 : ℝ) ×ˢ (univ : Set Space)))

theorem supported_uniform_energy {f : Field Space}
    (hc : ∀ t, Continuous (f t)) (hs : Supported f)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x, ‖f t x‖ ≤ C) :
    ∃ E : ℝ, ∀ t, 0 ≤ t → (1 / 2 : ℝ) * ∫ x, ‖f t x‖ ^ 2 ≤ E := by
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨(1 / 2 : ℝ) * ((volume K).toReal * C ^ 2), fun t ht => ?_⟩
  have he : (fun x => ‖f t x‖ ^ 2) = K.indicator (fun x => ‖f t x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, hs.zero_off ht hx]
  have hi : IntegrableOn (fun x => ‖f t x‖ ^ 2) K :=
    ((hc t).norm.pow 2).continuousOn.integrableOn_compact K_compact
  have hconst : IntegrableOn (fun _ : Space => C ^ 2) K :=
    integrableOn_const K_compact.measure_ne_top
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [he, integral_indicator K_closed.measurableSet]
  calc
    _ ≤ ∫ _x in K, C ^ 2 := setIntegral_mono_on hi hconst K_closed.measurableSet
      (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hb t ht x) 2)
    _ = _ := by simp [Measure.real]

end RapidForcing

end

end OAI
