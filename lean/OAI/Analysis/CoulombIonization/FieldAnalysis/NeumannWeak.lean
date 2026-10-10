import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.FlatFermionMollify

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

theorem neumann_global_weak
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x*Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x*(φ x:ℂ))) :
    tfKinetic*(∑ s, ∫ x, cellPressure (pointCell x)*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∑ s, ∫ x, ‖f s x‖^2) := by
  obtain ⟨u,hu,ha',hm',hg',hb,hb',ht⟩ := exists_flatFermion_smooth_approx hm hg ha hw
  let C := neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))
  have hC : 0 ≤ C := mul_nonneg neumannRemainderConstant_pos.le (by positivity)
  have hT : 0 ≤ tfKinetic := CoulombAnalysis.tfKinetic_pos.le
  have hi (n : ℕ) : Integrable (fun x => tfKinetic*∑ s, cellPressure (pointCell x)*‖u n s x‖^2) :=
    (integrable_finsetSum _ (fun s _ => flatPressure_integrable (hm' n s))).const_mul _
  have hif : Integrable (fun x => tfKinetic*∑ s, cellPressure (pointCell x)*‖f s x‖^2) :=
    (integrable_finsetSum _ (fun s _ => flatPressure_integrable (hm s))).const_mul _
  have hbound (n : ℕ) :
      (∫ x, tfKinetic*∑ s, cellPressure (pointCell x)*‖u n s x‖^2) ≤
        (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
    rw [integral_const_mul,integral_finsetSum _ (fun s _ => flatPressure_integrable (hm' n s)),
      Finset.mul_sum]
    calc
      _ ≤ ∑ s, ((1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) +
          C*(∫ x, ‖u n s x‖^2)) := by
        exact Finset.sum_le_sum (fun s _ => neumann_global_smooth_component
          (fun s => (hu n s).of_le (by simp)) (ha' n) (hm' n) (hg' n) s)
      _ = (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) +
          C*(∑ s, ∫ x, ‖u n s x‖^2) := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hb' n) (by norm_num))
        (mul_le_mul_of_nonneg_left (hb n) hC)
  have hh : (∫ x, tfKinetic*∑ s, cellPressure (pointCell x)*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
    apply integral_le_of_nonneg_ae_limit hi hif
    · exact fun n => Eventually.of_forall (fun x => mul_nonneg hT
        (Finset.sum_nonneg fun s _ => mul_nonneg (cellPressure_nonneg _) (sq_nonneg _)))
    · exact Eventually.of_forall (fun x => mul_nonneg hT
        (Finset.sum_nonneg fun s _ => mul_nonneg (cellPressure_nonneg _) (sq_nonneg _)))
    · filter_upwards [ae_all_iff.mpr ht] with x hx
      exact (tendsto_finsetSum Finset.univ (fun s _ =>
        ((hx s).norm.pow 2).const_mul (cellPressure (pointCell x)))).const_mul tfKinetic
    · exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ =>
        Finset.sum_nonneg fun q _ => integral_nonneg fun x => sq_nonneg _))
        (mul_nonneg hC (Finset.sum_nonneg fun s _ => integral_nonneg fun x => sq_nonneg _))
    · exact hbound
  rw [integral_const_mul,integral_finsetSum _ (fun s _ => flatPressure_integrable (hm s))] at hh
  exact hh

end CoulombNeumann

end

end OAI
