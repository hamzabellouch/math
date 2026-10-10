import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def fairSpin (u : ℝ) : IsingSpin :=
  if u ≤ 1 / 2 then IsingSpin.neg else IsingSpin.pos

lemma measurable_fairSpin : Measurable fairSpin := by
  exact measurable_const.ite measurableSet_Iic measurable_const

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

def fairSpinFactor (d : ℕ) (U : TreeVertex d → ℝ) : TreeVertex d → IsingSpin :=
  fun v => fairSpin (U v)

lemma measurable_fairSpinFactor (d : ℕ) : Measurable (fairSpinFactor d) := by
  exact Measurable.of_eval (fun vertex => measurable_fairSpin.comp (measurable_pi_apply vertex))

lemma fairSpinFactor_relabel (d : ℕ) (g : TreeAut d) (U : TreeVertex d → ℝ) :
    fairSpinFactor d (relabel g U) = relabel g (fairSpinFactor d U) := rfl

private lemma fairSpin_measurable_singleton (a : IsingSpin) : MeasurableSet ({a} : Set IsingSpin) := by
  trivial

lemma fairSpinFactor_cylinder (d : ℕ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    (Measure.map (fairSpinFactor d) (labelMeasure d))
      {x | ∀ v ∈ D, x v = eta v} = (1 / 2 : ENNReal) ^ D.card := by
  classical
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    exact MeasurableSet.pi D.countable_toSet (fun v hv => fairSpin_measurable_singleton (eta v))
  rw [Measure.map_apply (measurable_fairSpinFactor d) hmeas]
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01))
    (Set.pi (D : Set (TreeVertex d)) (fun v => fairSpin ⁻¹' {eta v})) = _
  rw [Measure.infinitePi_pi _ (fun v _ => measurable_fairSpin (fairSpin_measurable_singleton (eta v)))]
  simp [fairSpin_mass]

end Problem367

end

end OAI
