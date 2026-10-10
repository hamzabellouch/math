import OAI.Probability.Ballisticity.Main
import OAI.Probability.DirectionalWalk.Main

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

namespace RowBridge

def toReal {d : ℕ} (p : Row d) : DirectionalZeroOne.Row d :=
  ⟨fun e => (p.1 e : ℝ), by
    constructor
    · intro e
      exact ⟨(p.1 e).coe_nonneg, by exact_mod_cast row_entry_le_one p e⟩
    · change ∑ e : Direction d, (p.1 e : ℝ) = 1
      rw [← NNReal.coe_sum, p.2]
      rfl⟩

lemma measurable_toReal {d : ℕ} : Measurable (toReal (d := d)) := by
  apply Measurable.subtype_mk
  exact Measurable.of_eval fun e =>
    ((measurable_pi_apply e).comp measurable_subtype_coe).coe_nnreal_real

noncomputable def rowLaw {d : ℕ} (ν : Measure (Row d)) :
    Measure (DirectionalZeroOne.Row d) := ν.map toReal

instance rowLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (rowLaw ν) :=
  (Measure.isProbabilityMeasure_map_iff measurable_toReal.aemeasurable).2 inferInstance

def environment {d : ℕ} (ω : Environment d) : DirectionalZeroOne.Environment d :=
  fun x => toReal (ω x)

lemma measurable_environment {d : ℕ} : Measurable (environment (d := d)) :=
  Measurable.of_eval fun x => measurable_toReal.comp (measurable_pi_apply x)

lemma environmentLaw_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    (environmentLaw ν).map environment = DirectionalZeroOne.environmentLaw (rowLaw ν) := by
  exact Measure.infinitePi_map_pi (fun _ : Lattice d => ν) (fun _ => measurable_toReal)

lemma strictEllipticity {d : ℕ} (ν : Measure (Row d)) (hue : UniformElliptic ν) :
    DirectionalZeroOne.StrictEllipticity (rowLaw ν) := by
  obtain ⟨κ, hκ, hrows⟩ := hue
  have hm : MeasurableSet {p : DirectionalZeroOne.Row d | ∀ e, 0 < p.1 e} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => measurableSet_lt measurable_const
      ((measurable_pi_apply e).comp (measurable_subtype_coe :
        Measurable (fun p : DirectionalZeroOne.Row d => p.1)))
  apply (ae_map_iff measurable_toReal.aemeasurable hm).mpr
  filter_upwards [hrows] with p hp e
  change (0 : ℝ) < (p.1 e : ℝ)
  exact_mod_cast lt_of_lt_of_le hκ (hp e)

lemma entryWeight {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    DirectionalZeroOne.entryWeight (environment ω) x y = edgeWeight ω x y := by
  classical
  simp only [DirectionalZeroOne.entryWeight, edgeWeight,
    environment, toReal, ENNReal.ofReal_coe_nnreal]
  apply Finset.sum_congr rfl
  intro e _
  change (if x + step e = y then ((ω x).1 e : ℝ≥0∞) else 0) = _
  simp only [eq_comm]

lemma annealedLaw_eq {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    annealedLaw ν = DirectionalZeroOne.annealed (rowLaw ν) 0 := by
  apply pathMeasure_ext
  intro γ n
  rw [annealed_apply ν (measurableSet_pathCylinder γ n)]
  change (∫⁻ ω, quenchedKernel (ω, 0) (pathCylinder γ n) ∂environmentLaw ν) =
    DirectionalZeroOne.annealed (rowLaw ν) 0 (DirectionalZeroOne.pathCylinder n γ)
  rw [DirectionalZeroOne.annealed_cylinder]
  by_cases h0 : γ 0 = 0
  · rw [ite_eq_left h0.symm, ← environmentLaw_map ν,
      lintegral_map (DirectionalZeroOne.measurable_pathWeight n γ) measurable_environment]
    apply lintegral_congr
    intro ω
    rw [quenched_pathCylinder ω 0 γ h0 n]
    simp only [DirectionalZeroOne.pathWeight, entryWeight]
  · rw [ite_eq_right (Ne.symm h0)]
    simp only [quenched_pathCylinder_zero _ _ _ h0, lintegral_zero]

end RowBridge

end DirectionalTransience

end OAI
