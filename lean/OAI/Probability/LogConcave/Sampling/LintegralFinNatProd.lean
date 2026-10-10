import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

lemma lintegral_fin_nat_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E] {μ : Fin n → Measure E}
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E × (Fin n → E),
          f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
        rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (g := fun x : Fin n → E => ∏ i, f i.succ (x i))
          (hf 0).aemeasurable
          (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable, ih _ (fun i => hf _)]
      _ = _ := by rw [Fin.prod_univ_succ]

theorem pi_withDensity_fin {n : ℕ} {E : Type*}
    [MeasurableSpace E] (μ : Fin n → Measure E)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [Measure.restrict_pi_pi]
  rw [lintegral_fin_nat_prod _ hf]
  apply Finset.prod_congr rfl
  intro i _
  exact (withDensity_apply _ (hs i)).symm

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
