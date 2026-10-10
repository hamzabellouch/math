import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

def zeroControl (W : BrownianSystem Ω) (t : ℝ≥0) : Control W t where
  val := fun _ _ => 0
  progressive := isProgressive_const _ _
  bound := by simp

end ZeroTemperatureSK

namespace ZeroTemperatureSK

@[simp] theorem extend_coe (γ : Time → ℝ) (t : Time) : extend γ t = γ t := by
  simp [extend, t.property]

lemma OrderParameter.extend_nonneg (γ : OrderParameter) (t : ℝ) : 0 ≤ extend γ.val t := by
  unfold extend
  split
  · exact γ.nonneg _
  · rfl

lemma OrderParameter.measurable_extend (γ : OrderParameter) : Measurable (extend γ.val) := by
  exact γ.monotone.measurable.dite measurable_const measurableSet_Ico

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Control.measurable {W : BrownianSystem Ω} {t : ℝ≥0} (α : Control W t) :
    Measurable (fun p : ℝ≥0 × Ω => α.val p.1 p.2) := by
  have hclip (n : ℕ) : Measurable (fun p : ℝ≥0 × Ω => α.val (min p.1 n) p.2) := by
    have hs : Measurable[inferInstance, incrementFiltration W t (n : ℝ≥0)]
        (fun p : ℝ≥0 × Ω => p.2) :=
      measurable_snd.mono le_rfl ((incrementFiltration W t).le n)
    exact (α.progressive n).comp
      (((measurable_fst.min measurable_const).subtype_mk
        (h := fun p : ℝ≥0 × Ω => min_le_right p.1 (n : ℝ≥0))).prodMk hs)
  apply measurable_of_tendsto_metrizable hclip
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually
    (eventually_ge_atTop p.1)] with n hn
  simp only [min_eq_left hn]

lemma Control.measurable_elapsed {W : BrownianSystem Ω} {t : ℝ≥0}
    (α : Control W t) (b : ℝ) :
    Measurable (fun p : ℝ × Ω => α.val (Real.toNNReal (p.1 - b)) p.2) := by
  exact α.measurable.comp
    (((measurable_fst.sub measurable_const).real_toNNReal).prodMk measurable_snd)

lemma Control.integrable_weighted {W : BrownianSystem Ω} {t : ℝ≥0}
    (α : Control W t) (γ : OrderParameter) (b : ℝ) (ω : Ω) :
    Integrable (fun s : ℝ => extend γ.val s * α.val (Real.toNNReal (s - b)) ω) := by
  exact γ.integrable.mul_bdd
    ((α.measurable_elapsed b).comp measurable_prodMk_right).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using α.bound _ _))

lemma Control.integrable_weighted_sq {W : BrownianSystem Ω} {t : ℝ≥0}
    (α : Control W t) (γ : OrderParameter) (b : ℝ) (ω : Ω) :
    Integrable (fun s : ℝ => extend γ.val s * (α.val (Real.toNNReal (s - b)) ω)^2) := by
  apply γ.integrable.mul_bdd
    (((α.measurable_elapsed b).comp measurable_prodMk_right).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [Real.norm_eq_abs, abs_pow, one_pow, Function.comp_apply] using
      pow_le_pow_left₀ (abs_nonneg (α.val (Real.toNNReal (s - b)) ω)) (α.bound _ _) 2)

end ZeroTemperatureSK

end
end

end OAI
