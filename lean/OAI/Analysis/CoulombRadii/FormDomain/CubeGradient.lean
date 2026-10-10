import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.SmoothCompact
import OAI.Analysis.CoulombRadii.FieldAnalysis.SlotTensor

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma positionCLM_single {n : ℕ} (i j : Fin n) (b : Fin 3) :
    positionCLM j (EuclideanSpace.single (i,b) 1) =
      if j = i then EuclideanSpace.single b 1 else 0 := by
  ext c
  by_cases h : j = i
  · subst j
    simp [positionCLM]
  · simp [positionCLM, h]

lemma tensorOrbital_fderiv {n : ℕ} {α : Type*} (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (p : Fin n → α) (s : Spins n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1) =
      (fderiv ℝ (fun y => v (p i) y (s i)) (position x i) (EuclideanSpace.single b 1)) *
        ∏ j ∈ Finset.univ.erase i, v (p j) (position x j) (s j) := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y : Configuration n =>
      v (p j) (position y j) (s j)) x :=
    by
      change DifferentiableAt ℝ ((fun y : Space => v (p j) y (s j)) ∘ (positionCLM j)) x
      exact ((hv (p j) (s j)).differentiable (by simp) (positionCLM j x)).comp x
        (positionCLM j).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun y : Configuration n => v (p j) (position y j) (s j)) x =
      (fderiv ℝ (fun y => v (p j) y (s j)) (position x j)).comp (positionCLM j) := by
    exact (((hv (p j) (s j)).differentiable (by simp) (position x j)).hasFDerivAt.comp x
      (positionCLM j).hasFDerivAt).fderiv
  unfold tensorOrbital
  rw [fderiv_finsetProd (fun j _ => hd j), sum_apply]
  simp only [smul_apply, smul_eq_mul, he, ContinuousLinearMap.comp_apply,
    positionCLM_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j hj hji
    simp only [ite_eq_right hji, map_zero, mul_zero]
  · simp

lemma slaterConfiguration_fderiv {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (s : Spins n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (slaterConfiguration v s) x (EuclideanSpace.single (i,b) 1) =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        slotDeterminant (fun a (sx : Fin 2 × Space) => v a sx.2 sx.1)
          (fun a sx => fderiv ℝ (fun y => v a y sx.1) sx.2 (EuclideanSpace.single b 1)) i
          (fun j => (s j, position x j)) := by
  have ht (p : Equiv.Perm (Fin n)) : DifferentiableAt ℝ (tensorOrbital v p s) x :=
    (tensorOrbital_contDiff v hv p s).differentiable (by simp) x
  rw [slaterConfiguration_expansion, fderiv_const_mul (DifferentiableAt.fun_sum (fun p _ =>
      (ht p).const_mul _)), fderiv_fun_sum (fun p _ => (ht p).const_mul _)]
  simp only [smul_apply, smul_eq_mul, sum_apply,
    fderiv_const_mul (ht _), tensorOrbital_fderiv v hv]
  unfold slotDeterminant
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [slotTensor_factor]

noncomputable def cubeGradient {n : ℕ} (ψ : H1Vector n) (a : Fin n × Fin 3)
    (z : Fin n → Fin 2 × (Fin 3 → ℝ)) : ℂ :=
  ψ.gradient ((spinCubeEquiv n) z).1 a (WithLp.toLp 2 ((spinCubeEquiv n) z).2)

lemma H1Vector.gradient_spinSpace_memLp {n : ℕ} (ψ : H1Vector n) (a : Fin n × Fin 3) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.gradient sx.1 a (WithLp.toLp 2 sx.2)) 2 (Measure.count.prod volume) := by
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ => tensorPair_memLp (hi s)
    ((ψ.partial_L2 s a).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma cubeGradient_full_norm {n : ℕ} (ψ : H1Vector n) (a : Fin n × Fin 3) :
    (∫ z, ‖cubeGradient ψ a z‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) =
      ∑ s, ∫ x, ‖ψ.gradient s a x‖^2 := by
  unfold cubeGradient
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => ‖ψ.gradient sx.1 a (WithLp.toLp 2 sx.2)‖^2)]
  rw [integral_prod _ (ψ.gradient_spinSpace_memLp a).norm.integrable_sq, integral_count]
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.gradient s a x‖^2)

lemma slaterState_cubeGradient {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (i : Fin n) (b : Fin 3) (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    cubeGradient (slaterState v hv hC) (i,b) z =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        slotDeterminant (fun a => flatSpinOrbital (v a))
          (fun a => flatSpinOrbital (fun x s =>
            fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1))) i z := by
  change fderiv ℝ (slaterConfiguration v _) _ (EuclideanSpace.single (i,b) 1) = _
  rw [slaterConfiguration_fderiv v hv]
  rfl

lemma slaterState_kinetic {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x : Space, star (v i x s) * v j x s) =
      if i = j then (1:ℂ) else 0) :
    kinetic (slaterState v hv hC) = (1/2:ℝ) * ∑ i, ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
  have hV (i : Fin n) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume :=
    (hv i s).continuous.memLp_of_hasCompactSupport (hC i s)
  have hD (i : Fin n) (s : Fin 2) (b : Fin 3) :
      MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2 volume :=
    (((hv i s).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hC i s).fderiv_apply ℝ _)
  have hO (i j : Fin n) : (∫ a, star (flatSpinOrbital (v i) a) * flatSpinOrbital (v j) a
      ∂spinSpaceMeasure) = if i = j then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
    exact ho i j
  have hb (b : Fin 3) : (∑ i, ∑ s, ∫ x, ‖(slaterState v hv hC).gradient s (i,b) x‖^2) =
      ∑ i, ∑ s, ∫ x : Space,
        ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
    simp_rw [← cubeGradient_full_norm, slaterState_cubeGradient]
    have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le, integral_const_mul]
    rw [← Finset.mul_sum, slotDeterminant_total_norm_sq _ _
      (fun i => flatSpinOrbital_memLp (v i) (hV i))
      (fun i => flatSpinOrbital_memLp _ (fun s => hD i s b)) hO,
      ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    apply Finset.sum_congr rfl
    intro i _
    have h := flatSpinOrbital_inner
      (fun x s => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1))
      (fun x s => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1))
      (fun s => hD i s b) (fun s => hD i s b)
    have hz (z : ℂ) : star z * z = (↑(‖z‖^2) : ℂ) := by
      rw [mul_comm, Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z
    simp_rw [hz, integral_complex_ofReal] at h
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_sum] using h)
  unfold kinetic
  congr 1
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ b : Fin 3, ∑ i, ∑ s, ∫ x, ‖(slaterState v hv hC).gradient s (i,b) x‖^2 := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ i, ∑ b : Fin 3, ∑ s, ∫ x, ‖(slaterState v hv hC).gradient s (i,b) x‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      simp_rw [hb]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
