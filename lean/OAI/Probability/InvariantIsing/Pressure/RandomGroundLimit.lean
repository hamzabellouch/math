import OAI.Probability.InvariantIsing.Pressure.RandomThermalSqueeze

namespace OAI

/-! A zero-temperature limit from fixed-temperature random pressures. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_ground_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ) (A : ℝ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hG : UniformIntegrable G 1 P)
    (hpm : ∀ β n, Measurable (p β n))
    (hpi : ∀ β, 0 < β → ∀ n, Integrable (p β n) P)
    (hp : ∀ β, 0 < β → TendstoInMeasure P (p β) atTop (fun _ => A β))
    (hpmean : ∀ β, 0 < β → Tendsto (fun n => ∫ ω, p β n ω ∂P) atTop (𝓝 (A β)))
    (hb : ∀ β, 0 < β → ∀ n ω, p β n ω/β ≤ G n ω ∧ G n ω ≤ p β n ω/β+c/β) :
    ∃ L : ℝ, TendstoInMeasure P G atTop (fun _ => L) ∧
      Tendsto (fun n => eLpNorm (fun ω => G n ω-L) 1 P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, G n ω ∂P) atTop (𝓝 L) ∧
      Tendsto (fun β => A β/β) atTop (𝓝 L) := by
  let g := fun n => ∫ ω, G n ω ∂P
  let q := fun (k n : ℕ) => (∫ ω, p ((k : ℝ)+1) n ω ∂P)/((k : ℝ)+1)
  let v := fun k : ℕ => A ((k : ℝ)+1)/((k : ℝ)+1)
  have hg (n : ℕ) : Integrable (G n) P := memLp_one_iff_integrable.mp (hG.memLp n)
  have hmean (β : ℝ) (hβ : 0 < β) (n : ℕ) :
      (∫ ω, p β n ω ∂P)/β ≤ g n ∧ g n ≤ (∫ ω, p β n ω ∂P)/β+c/β := by
    have hpi' := (hpi β hβ n).div_const β
    have hl := integral_mono hpi' (hg n) (fun ω => (hb β hβ n ω).1)
    have hu := integral_mono (hg n) (hpi'.add (integrable_const (c/β)))
      (fun ω => (hb β hβ n ω).2)
    rw [integral_div] at hl
    simp only [Pi.add_apply] at hu
    rw [integral_add hpi' (integrable_const _),integral_div,integral_const,
      probReal_univ,one_smul] at hu
    exact ⟨hl,hu⟩
  obtain ⟨L,hv,hglim⟩ := exists_thermal_ground_limit q g v c hc
    (fun k => (hpmean ((k : ℝ)+1) (by positivity)).div_const _)
    (fun k => Filter.Eventually.of_forall (hmean ((k : ℝ)+1) (by positivity)))
  have hprob : TendstoInMeasure P G atTop (fun _ => L) := by
    apply thermal_squeeze_in_measure P (fun k n ω => p ((k : ℝ)+1) n ω/((k : ℝ)+1))
      G v L c hc hv
    · intro k
      exact tendstoInMeasure_continuous_comp P _ _ (hpm _) (hp _ (by positivity))
        (fun x => x/((k : ℝ)+1)) (continuous_id.div_const _)
    · intro k n ω
      exact hb ((k : ℝ)+1) (by positivity) n ω
  have hL1 := pressure_L1_of_probability_and_uniformIntegrability P G L hG hprob
  refine ⟨L,hprob,hL1.1,hL1.2,?_⟩
  have hbounds (β : ℝ) (hβ : 0 < β) : A β/β ≤ L ∧ L ≤ A β/β+c/β := by
    have ht := (hpmean β hβ).div_const β
    exact ⟨le_of_tendsto_of_tendsto ht hglim
        (Filter.Eventually.of_forall fun n => (hmean β hβ n).1),
      le_of_tendsto_of_tendsto hglim (ht.add_const _)
        (Filter.Eventually.of_forall fun n => (hmean β hβ n).2)⟩
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ (tendsto_id.const_div_atTop c)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [Real.norm_eq_abs,abs_le]
  simp only [id_eq]
  have hh := hbounds β hβ
  constructor <;> linarith [hh.1,hh.2,div_nonneg hc hβ.le]

end InvariantIsing

end

end OAI
