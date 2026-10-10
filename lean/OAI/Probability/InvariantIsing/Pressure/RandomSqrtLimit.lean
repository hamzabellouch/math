import OAI.Probability.InvariantIsing.Pressure.RandomThermalSqueeze

namespace OAI

/-! Continuous square-root transport with uniform integrability. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

lemma uniformIntegrable_add_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ℕ → Ω → ℝ)
    (hX : UniformIntegrable X 1 P) (hY : UniformIntegrable Y 1 P) :
    UniformIntegrable (fun n ω => X n ω+Y n ω) 1 P := by
  refine ⟨hX.1.add hY.1 le_rfl,?_⟩
  obtain ⟨C,hC⟩ := hX.2
  obtain ⟨D,hD⟩ := hY.2
  refine ⟨C+D,fun n => ?_⟩
  exact (eLpNorm_add_le (f := X n) (g := Y n) le_rfl).trans (add_le_add (hC n) (hD n))

lemma uniformIntegrable_abs_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : UniformIntegrable X 1 P) :
    UniformIntegrable (fun n ω => |X n ω|) 1 P := by
  apply uniformIntegrable_of_abs_le P _ X
    (fun n => (hX.aestronglyMeasurable n).norm) hX
  intro n
  filter_upwards [] with ω
  simp only [Real.norm_eq_abs,abs_abs,le_refl]

lemma random_sqrt_scaled_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (L a : ℝ)
    (ha : |a| ≤ 2) (hX : ∀ n, Measurable (X n)) (hUI : UniformIntegrable X 1 P)
    (hprob : TendstoInMeasure P X atTop (fun _ => L)) :
    TendstoInMeasure P (fun n ω => Real.sqrt (a*X n ω)) atTop (fun _ => Real.sqrt (a*L)) ∧
    Tendsto (fun n => eLpNorm (fun ω => Real.sqrt (a*X n ω)-Real.sqrt (a*L)) 1 P)
      atTop (𝓝 0) := by
  have hs : UniformIntegrable (fun n ω => 1+|X n ω|) 1 P :=
    uniformIntegrable_add_real P _ _ (uniformIntegrable_const le_rfl (by simp) (memLp_const 1))
      (uniformIntegrable_abs_real P X hUI)
  have hsq : UniformIntegrable (fun n ω => Real.sqrt (a*X n ω)) 1 P := by
    apply uniformIntegrable_of_abs_le P _ _
      (fun n => (((hX n).const_mul a).sqrt).aestronglyMeasurable) hs
    intro n
    filter_upwards [] with ω
    rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (by positivity : 0 ≤ 1+|X n ω|)]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hax : a*X n ω ≤ 2*|X n ω| := (le_abs_self (a*X n ω)).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ha (abs_nonneg _))
      nlinarith [sq_nonneg (|X n ω|),sq_abs (X n ω)]
  have hp := tendstoInMeasure_continuous_comp P X L hX hprob
    (fun x => Real.sqrt (a*x)) (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))
  exact ⟨hp,(pressure_L1_of_probability_and_uniformIntegrability P _ _ hsq hp).1⟩

end InvariantIsing

end

end OAI
