import OAI.Probability.InvariantIsing.Fields.FieldPairingPathError
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupPath
import OAI.Probability.InvariantIsing.Fields.FieldBounds

namespace OAI

/-! Approximate self-consistency makes the weighted magnetic field values
approach the entropy supremum. Uniform height bounds avoid needing a limit
of the fields themselves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_group_trial_upper {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (hmag : ∀ a, |mag a| ≤ 1)
    (p : OverlapPath) (h : FieldStep) :
    magneticGroupValue γ mag h + fieldPairing p h / 2 ≤ h.height (Fin.last h.depth) / 2 := by
  have hp : fieldPairing p h ≤ h.height (Fin.last h.depth) := by
    have hh := integral_mono (integrable_path_mul_field p h) (integrable_const (h.height (Fin.last h.depth)))
      (fun s => (mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)).trans
        (fieldFunction_le_last h s))
    simpa only [fieldPairing, integral_const, probReal_univ, one_smul] using hh
  linarith [magneticGroupValue_le γ mag hγ hγsum hmag h, fieldValue_nonpos h]

theorem magnetic_entropy_sequence_of_support {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s * (fieldFunction k s - fieldFunction (h n) s)
        ∂pathMeasure) / 2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n) + fieldPairing p (h n) / 2)
      atTop (𝓝 (magneticEntropyFunctional γ mag p).toReal) := by
  let V := fun n => magneticGroupValue γ mag (h n) + fieldPairing p (h n) / 2
  let e := fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s - p s| ∂pathMeasure
  have he0 n : 0 ≤ e n := integral_nonneg (fun _ => abs_nonneg _)
  have hV n : V n ≤ C / 2 := (magnetic_group_trial_upper γ mag hγ hγsum hmag p (h n)).trans (by linarith [hC n])
  have happrox (n : ℕ) (k : FieldStep) :
      magneticGroupValue γ mag k + fieldPairing p k / 2 ≤ V n +
        ((k.height (Fin.last k.depth) + C) / 2) * e n := by
    have hb := trial_le_of_path_support p (magneticGroupPath γ mag hγ hγsum (h n)) (h n) k _ _ (hsupport n k)
    change magneticGroupValue γ mag k + fieldPairing p k / 2 ≤ V n +
      ((k.height (Fin.last k.depth) + (h n).height (Fin.last (h n).depth)) / 2) * e n at hb
    have hc : (k.height (Fin.last k.depth) + (h n).height (Fin.last (h n).depth)) / 2 ≤
        (k.height (Fin.last k.depth) + C) / 2 := by linarith [hC n]
    exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (he0 n)))
  have hall (k : FieldStep) : magneticGroupValue γ mag k + fieldPairing p k / 2 ≤ C / 2 := by
    have ht : Tendsto (fun n => C / 2 +
        ((k.height (Fin.last k.depth) + C) / 2) * e n) atTop (𝓝 (C / 2)) := by
      simpa only [mul_zero, add_zero] using
        (hself.const_mul ((k.height (Fin.last k.depth) + C) / 2)).const_add (C / 2)
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n => (happrox n k).trans (add_le_add (hV n) le_rfl))
  have hE : magneticEntropyFunctional γ mag p ≤ ((C / 2 : ℝ) : EReal) := by
    apply iSup_le
    intro k
    exact_mod_cast hall k
  have htop : magneticEntropyFunctional γ mag p ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hE
  have hbot : magneticEntropyFunctional γ mag p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      (le_iSup (fun k : FieldStep => ((magneticGroupValue γ mag k + fieldPairing p k / 2 : ℝ) : EReal))
        zeroField)
  let S := (magneticEntropyFunctional γ mag p).toReal
  have hS : magneticEntropyFunctional γ mag p = (S : EReal) := (EReal.coe_toReal htop hbot).symm
  have hVS n : V n ≤ S := by
    have hh := le_iSup (fun k : FieldStep =>
      ((magneticGroupValue γ mag k + fieldPairing p k / 2 : ℝ) : EReal)) (h n)
    change (V n : EReal) ≤ magneticEntropyFunctional γ mag p at hh
    rw [hS] at hh
    exact_mod_cast hh
  refine ⟨htop, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  have hlt : ((S - ε / 2 : ℝ) : EReal) < magneticEntropyFunctional γ mag p := by
    rw [hS]
    exact_mod_cast (show S - ε / 2 < S by linarith)
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
  have hk' : S - ε / 2 < magneticGroupValue γ mag k + fieldPairing p k / 2 := by exact_mod_cast hk
  have hsmall := (hself.const_mul ((k.height (Fin.last k.depth) + C) / 2)).eventually
    (gt_mem_nhds (show ((k.height (Fin.last k.depth) + C) / 2) * 0 < ε / 2 by
      simpa using half_pos hε))
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hVS n))]
  have hb := happrox n k
  change ((k.height (Fin.last k.depth) + C) / 2) * e n < ε / 2 at hn
  change -(V n - S) < ε
  linarith

end InvariantIsing

end

end OAI
