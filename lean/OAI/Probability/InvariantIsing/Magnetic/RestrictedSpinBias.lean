import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinKernel
import OAI.Probability.InvariantIsing.Magnetic.ConstrainedBlockBias

namespace OAI

/-! A constant energy shift on the constraint set cancels from its
actual conditional Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma restrictedSpinLaw_mass {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) (T : Finset (Spin N)) :
    (restrictedSpinLaw S H).real T =
      (∑ σ ∈ S ∩ T, Real.exp (H σ)) / ∑ σ ∈ S, Real.exp (H σ) := by
  classical
  rw [measureReal_def, restrictedSpinLaw, cond_apply S.measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S)⁻¹ *
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real
      ((S : Set (Spin N)) ∩ T) = _
  rw [← Finset.coe_inter, spinGibbs_mass_finset, spinGibbs_mass_finset]
  have hZ := (sum_exp_pos H).ne'
  have hZS := (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS).ne'
  field_simp

lemma restrictedSpinLaw_eq_of_add_on_set {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H G : Spin N → ℝ) (c : ℝ) (hG : ∀ σ ∈ S, G σ = H σ + c) :
    restrictedSpinLaw S G = restrictedSpinLaw S H := by
  classical
  have hscale (T : Finset (Spin N)) (hT : T ⊆ S) :
      (∑ σ ∈ T, Real.exp (G σ)) = Real.exp c * ∑ σ ∈ T, Real.exp (H σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hG σ (hT hσ), Real.exp_add]
    ring
  let _ := restrictedSpinLaw_probability S hS G
  let _ := restrictedSpinLaw_probability S hS H
  apply Measure.ext_of_singleton
  intro σ
  have hreal : (restrictedSpinLaw S G).real ({σ} : Finset (Spin N)) =
      (restrictedSpinLaw S H).real ({σ} : Finset (Spin N)) := by
    rw [restrictedSpinLaw_mass S hS G, restrictedSpinLaw_mass S hS H,
      hscale (S ∩ {σ}) Finset.inter_subset_left, hscale S (fun _ hx => hx)]
    exact mul_div_mul_left _ _ (Real.exp_ne_zero c)
  have he := congrArg ENNReal.ofReal hreal
  rw [measureReal_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  simpa only [Finset.coe_singleton] using he

lemma restrictedSpinKernel_group_bias {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (bias : A → ℝ) (z : Fin N → ℝ) :
    restrictedSpinKernel (spinGroupSlice group k) (z + fun j => bias (group j)) =
      restrictedSpinKernel (spinGroupSlice group k) z := by
  apply restrictedSpinLaw_eq_of_add_on_set _ (spinGroupSlice_nonempty group k hk)
    (fieldEnergy z) (fieldEnergy (z + fun j => bias (group j)))
    (spinGroupFieldConstant group k bias)
  intro σ hσ
  have he : fieldEnergy (z + fun j => bias (group j)) σ =
      fieldEnergy z σ + fieldEnergy (fun j => bias (group j)) σ := by
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [he, fieldEnergy_on_group_slice group k bias hσ]

end InvariantIsing

end

end OAI
