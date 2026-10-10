import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannPhysical
import OAI.Analysis.CoulombIonization.FieldAnalysis.RotationTrace

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PressureWeak_scope

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

theorem pressure_weak_of_smooth
    (W : ((Fin N × Fin 3) → ℝ) → ℝ) (hW : ∀ x, 0 ≤ W x)
    (hWi : ∀ {v : ((Fin N × Fin 3) → ℝ) → ℂ}, MemLp v 2 →
      Integrable (fun x => W x*‖v x‖^2))
    {C : ℝ} (hC : 0 ≤ C)
    (hsm : ∀ {u : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ},
      (∀ s, ContDiff ℝ 1 (u s)) → FlatAntisymmetric u →
      (∀ s, MemLp (u s) 2) →
      (∀ s q, MemLp (fun x => fderiv ℝ (u s) x (Pi.single q 1)) 2) →
      ∀ s, tfKinetic*(∫ x, W x*‖u s x‖^2) ≤
        (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (u s) x (Pi.single q 1)‖^2) +
          C*(∫ x, ‖u s x‖^2))
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x*Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x*(φ x:ℂ))) :
    tfKinetic*(∑ s, ∫ x, W x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
  obtain ⟨u,hu,ha',hm',hg',hb,hb',ht⟩ := exists_flatFermion_smooth_approx hm hg ha hw
  have hT : 0 ≤ tfKinetic := CoulombAnalysis.tfKinetic_pos.le
  have hi (n : ℕ) : Integrable (fun x => tfKinetic*∑ s, W x*‖u n s x‖^2) :=
    (integrable_finsetSum _ (fun s _ => hWi (hm' n s))).const_mul _
  have hif : Integrable (fun x => tfKinetic*∑ s, W x*‖f s x‖^2) :=
    (integrable_finsetSum _ (fun s _ => hWi (hm s))).const_mul _
  have hbound (n : ℕ) :
      (∫ x, tfKinetic*∑ s, W x*‖u n s x‖^2) ≤
        (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
    rw [integral_const_mul,integral_finsetSum _ (fun s _ => hWi (hm' n s)),
      Finset.mul_sum]
    calc
      _ ≤ ∑ s, ((1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) +
          C*(∫ x, ‖u n s x‖^2)) := by
        exact Finset.sum_le_sum (fun s _ => hsm
          (fun s => (hu n s).of_le (by simp)) (ha' n) (hm' n) (hg' n) s)
      _ = (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) +
          C*(∑ s, ∫ x, ‖u n s x‖^2) := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hb' n) (by norm_num))
        (mul_le_mul_of_nonneg_left (hb n) hC)
  have hh : (∫ x, tfKinetic*∑ s, W x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
    apply integral_le_of_nonneg_ae_limit hi hif
    · exact fun n => Eventually.of_forall (fun x => mul_nonneg hT
        (Finset.sum_nonneg fun s _ => mul_nonneg (hW _) (sq_nonneg _)))
    · exact Eventually.of_forall (fun x => mul_nonneg hT
        (Finset.sum_nonneg fun s _ => mul_nonneg (hW _) (sq_nonneg _)))
    · filter_upwards [ae_all_iff.mpr ht] with x hx
      exact (tendsto_finsetSum Finset.univ (fun s _ =>
        ((hx s).norm.pow 2).const_mul (W x))).const_mul tfKinetic
    · exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ =>
        Finset.sum_nonneg fun q _ => integral_nonneg fun x => sq_nonneg _))
        (mul_nonneg hC (Finset.sum_nonneg fun s _ => integral_nonneg fun x => sq_nonneg _))
    · exact hbound
  rw [integral_const_mul,integral_finsetSum _ (fun s _ => hWi (hm s))] at hh
  exact hh

end Work_PressureWeak_scope

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

def rotatedGridPressure (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) : ℝ :=
  gridPressure b t ((flatRotation R).symm x)

lemma rotatedGridPressure_nonneg (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) : 0 ≤ rotatedGridPressure b t R x := gridPressure_nonneg _ _ _

lemma rotatedGridPressure_bound (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) :
    rotatedGridPressure b t R x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) := gridPressure_bound _ _ _

lemma rotatedGridPressure_measurable (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    Measurable (rotatedGridPressure (N := N) b t R) :=
  (gridPressure_measurable b t).comp (flatRotation R).symm.continuous.measurable

lemma rotatedGridPressure_integrable {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : MemLp f 2)
    (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    Integrable (fun x => rotatedGridPressure b t R x*‖f x‖^2) := by
  apply hf.norm.integrable_sq.bdd_mul (rotatedGridPressure_measurable b t R).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (rotatedGridPressure_nonneg b t R x)]
    exact rotatedGridPressure_bound b t R x)

theorem neumann_rotated_smooth_component
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (ha : FlatAntisymmetric f)
    (hm : ∀ s, MemLp (f s) 2)
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (s : Fin N → Fin 2) :
    tfKinetic*(∫ x, rotatedGridPressure b t R x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x, ‖f s x‖^2) := by
  have hh := neumann_affine_smooth_component
    (fun s => (hf s).comp (flatRotation R).contDiff) (flatRotation_anti ha R)
    (fun s => (hm s).comp_measurePreserving (flatRotation_preserving R))
    (fun s q => flatRotation_gradient_memLp (hf s) (hg s) R q) hb t s
  have he : (∫ x, gridPressure b t x*‖f s (flatRotation R x)‖^2) =
      ∫ x, rotatedGridPressure b t R x*‖f s x‖^2 := by
    have h := (flatRotation_preserving (N := N) R).integral_comp
      (flatRotation (N := N) R).toHomeomorph.measurableEmbedding
      (fun x => rotatedGridPressure b t R x*‖f s x‖^2)
    simpa only [rotatedGridPressure,ContinuousLinearEquiv.symm_apply_apply] using h
  have hem := (flatRotation_preserving (N := N) R).integral_comp
    (flatRotation (N := N) R).toHomeomorph.measurableEmbedding (fun x => ‖f s x‖^2)
  simp only [Function.comp_def] at hh
  rw [he,hem,flatRotation_kinetic (hf s) (hg s)] at hh
  exact hh

theorem neumann_rotated_weak
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x*Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x*(φ x:ℂ)))
    {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    tfKinetic*(∑ s, ∫ x, rotatedGridPressure b t R x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) +
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∑ s, ∫ x, ‖f s x‖^2) := by
  apply pressure_weak_of_smooth (rotatedGridPressure b t R) (rotatedGridPressure_nonneg b t R)
    (fun hv => rotatedGridPressure_integrable hv b t R)
    (mul_nonneg (mul_nonneg (sq_nonneg _) neumannRemainderConstant_pos.le) (by positivity))
    (fun hu hau hmu hgu s => neumann_rotated_smooth_component hu hau hmu hgu hb t R s) hm hg ha hw

end CoulombNeumann

end

end OAI
