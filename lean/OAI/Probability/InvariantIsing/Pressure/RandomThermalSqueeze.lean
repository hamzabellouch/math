import OAI.Probability.InvariantIsing.Pressure.RandomUniformIntegrability
import OAI.Probability.InvariantIsing.Pressure.ThermalLimitSqueeze

namespace OAI

/-! A soft-maximum squeeze for convergence in probability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma tendstoInMeasure_continuous_comp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ) (L : ℝ)
    (hX : ∀ n, Measurable (X n)) (h : TendstoInMeasure P X atTop (fun _ => L))
    (f : ℝ → ℝ) (hf : Continuous f) :
    TendstoInMeasure P (fun n ω => f (X n ω)) atTop (fun _ => f L) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hf.measurable.comp (hX n)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨u,hu,he⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,he.mono fun ω hω => (hf.tendsto L).comp hω⟩

lemma thermal_squeeze_in_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ)
    (v : ℕ → ℝ) (L c : ℝ) (hc : 0 ≤ c)
    (hv : Tendsto v atTop (𝓝 L))
    (hp : ∀ k, TendstoInMeasure P (X k) atTop (fun _ => v k))
    (hb : ∀ k n ω, X k n ω ≤ G n ω ∧ G n ω ≤ X k n ω+c/(k+1)) :
    TendstoInMeasure P G atTop (fun _ => L) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hd : Tendsto (fun k : ℕ => c/(k+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hvd : Tendsto (fun k => |v k-L|+c/(k+1)) atTop (𝓝 0) := by
    simpa using ((hv.sub_const L).abs.add hd)
  obtain ⟨k,hk⟩ := (hvd.eventually (gt_mem_nhds (half_pos hε))).exists
  have hprob := (tendstoInMeasure_iff_norm.mp (hp k)) (ε/2) (half_pos hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  simp only [mem_ofPred_eq,Real.norm_eq_abs] at hω ⊢
  by_contra! hbad
  have hB := hb k n ω
  have hc' : 0 ≤ c/(k+1) := by positivity
  have hG : |G n ω-L| ≤ |X k n ω-v k|+|v k-L|+c/(k+1) := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (X k n ω-v k),le_abs_self (X k n ω-v k),
      neg_abs_le (v k-L),le_abs_self (v k-L)]
  linarith

end InvariantIsing

end

end OAI
