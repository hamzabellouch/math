import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalFormalAdjoint
open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D E F : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def multiply (a : D → E →L[ℝ] F) (ha : a.HasTemperateGrowth) :
    𝓢(D,E) →L[ℝ] 𝓢(D,F) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ F) ha

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma multiply_apply (a : D → E →L[ℝ] F) (ha : a.HasTemperateGrowth)
    (u : 𝓢(D,E)) (x : D) : multiply a ha u x = a x (u x) := rfl

def adjointCoefficient (a : 𝓢(D,E →L[ℝ] F)) : 𝓢(D,F →L[ℝ] E) :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap) a

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
@[simp] lemma adjointCoefficient_apply (a : 𝓢(D,E →L[ℝ] F)) (x : D) :
    adjointCoefficient a x = (a x).adjoint := rfl

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma multiply_pairing (a : 𝓢(D,E →L[ℝ] F)) (u : 𝓢(D,E)) (v : 𝓢(D,F)) (x : D) :
    ⟪multiply a a.hasTemperateGrowth u x, v x⟫ =
      ⟪u x, multiply (adjointCoefficient a) (adjointCoefficient a).hasTemperateGrowth v x⟫ :=
  (ContinuousLinearMap.adjoint_inner_right (a x) (u x) (v x)).symm

lemma directional_formal_adjoint (a : 𝓢(D,E →L[ℝ] F)) (e : D)
    (u : 𝓢(D,E)) (v : 𝓢(D,F)) :
    (∫ x, ⟪multiply a a.hasTemperateGrowth (∂_{e} u) x, v x⟫) =
      -∫ x, ⟪u x, (∂_{e} (multiply (adjointCoefficient a)
        (adjointCoefficient a).hasTemperateGrowth v)) x⟫ := by
  simp_rw [multiply_pairing]
  have h := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
    u (multiply (adjointCoefficient a) (adjointCoefficient a).hasTemperateGrowth v)
    (innerSL ℝ) e (μ := volume)
  change (∫ x, ⟪u x, (∂_{e} (multiply (adjointCoefficient a)
    (adjointCoefficient a).hasTemperateGrowth v)) x⟫) =
      -∫ x, ⟪(∂_{e} u) x, multiply (adjointCoefficient a)
        (adjointCoefficient a).hasTemperateGrowth v x⟫ at h
  linarith

variable {ι : Type*} [Fintype ι]

def firstOrder (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F)) (b : 𝓢(D,E →L[ℝ] F)) :
    𝓢(D,E) →L[ℝ] 𝓢(D,F) :=
  (∑ i, multiply (a i) (a i).hasTemperateGrowth ∘L
    lineDerivOpCLM ℝ 𝓢(D,E) (e i)) + multiply b b.hasTemperateGrowth

def formalAdjoint (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F)) (b : 𝓢(D,E →L[ℝ] F)) :
    𝓢(D,F) →L[ℝ] 𝓢(D,E) :=
  -(∑ i, lineDerivOpCLM ℝ 𝓢(D,E) (e i) ∘L multiply (adjointCoefficient (a i))
    (adjointCoefficient (a i)).hasTemperateGrowth) +
    multiply (adjointCoefficient b) (adjointCoefficient b).hasTemperateGrowth

omit [CompleteSpace E] in
lemma inner_integrable (u v : 𝓢(D,E)) : Integrable (fun x => ⟪u x,v x⟫) :=
  (SchwartzMap.bilinLeftCLM (innerSL ℝ) v.hasTemperateGrowth u).integrable

lemma firstOrder_pairing (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F)) (b : 𝓢(D,E →L[ℝ] F))
    (u : 𝓢(D,E)) (v : 𝓢(D,F)) :
    (∫ x, ⟪firstOrder e a b u x, v x⟫) = ∫ x, ⟪u x, formalAdjoint e a b v x⟫ := by
  simp only [firstOrder, formalAdjoint, _root_.add_apply,
    _root_.neg_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_add_right, inner_sum, sum_inner,
    inner_neg_right]
  rw [integral_add, integral_add]
  · rw [integral_neg, integral_finsetSum, integral_finsetSum]
    · simp only [lineDerivOpCLM_apply]
      rw [show (∑ i, ∫ x, ⟪multiply (a i) (a i).hasTemperateGrowth (∂_{e i} u) x, v x⟫) =
          -∑ i, ∫ x, ⟪u x, (∂_{e i} (multiply (adjointCoefficient (a i))
            (adjointCoefficient (a i)).hasTemperateGrowth v)) x⟫ by
        simp only [directional_formal_adjoint, Finset.sum_neg_distrib]]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall (multiply_pairing b u v))
    · intro i _
      exact inner_integrable _ _
    · intro i _
      exact inner_integrable _ _
  · exact (integrable_finsetSum Finset.univ (fun _ _ => inner_integrable _ _)).neg
  · exact inner_integrable _ _
  · exact integrable_finsetSum Finset.univ (fun _ _ => inner_integrable _ _)
  · exact inner_integrable _ _

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] [CompleteSpace F] in

lemma lineDeriv_multiply (a : 𝓢(D,E →L[ℝ] F)) (u : 𝓢(D,E)) (e : D) :
    ∂_{e} (multiply a a.hasTemperateGrowth u) =
      multiply (∂_{e} a : 𝓢(D,E →L[ℝ] F)) (∂_{e} a).hasTemperateGrowth u +
        multiply a a.hasTemperateGrowth (∂_{e} u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, multiply_apply, _root_.add_apply]
  change fderiv ℝ (fun y => a y (u y)) x e = _
  rw [fderiv_clm_apply a.differentiableAt u.differentiableAt]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in

lemma formalAdjoint_expanded (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (v : 𝓢(D,F)) :
    formalAdjoint e a b v =
      -(∑ i, multiply (∂_{e i} (adjointCoefficient (a i)) : 𝓢(D,F →L[ℝ] E))
          (∂_{e i} (adjointCoefficient (a i))).hasTemperateGrowth v +
        ∑ i, multiply (adjointCoefficient (a i))
          (adjointCoefficient (a i)).hasTemperateGrowth (∂_{e i} v)) +
        multiply (adjointCoefficient b) (adjointCoefficient b).hasTemperateGrowth v := by
  simp only [formalAdjoint, _root_.add_apply, _root_.neg_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply, lineDeriv_multiply,
    Finset.sum_add_distrib]

def weightedCoefficient (ρ : D → ℝ) (a : 𝓢(D,E →L[ℝ] F)) : 𝓢(D,E →L[ℝ] F) :=
  SchwartzMap.smulLeftCLM (E →L[ℝ] F) ρ a

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] [CompleteSpace F] in
lemma weightedCoefficient_apply (ρ : D → ℝ) (hρ : ρ.HasTemperateGrowth)
    (a : 𝓢(D,E →L[ℝ] F)) (x : D) : weightedCoefficient ρ a x = ρ x • a x :=
  SchwartzMap.smulLeftCLM_apply_apply hρ a x

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] [CompleteSpace F] in
lemma weighted_firstOrder (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (ρ : D → ℝ) (hρ : ρ.HasTemperateGrowth)
    (u : 𝓢(D,E)) (x : D) :
    firstOrder e (fun i => weightedCoefficient ρ (a i)) (weightedCoefficient ρ b) u x =
      ρ x • firstOrder e a b u x := by
  simp only [firstOrder, _root_.add_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, multiply_apply, weightedCoefficient_apply ρ hρ,
    _root_.smul_apply, smul_add, Finset.smul_sum]

def weightedFormalAdjoint (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (ρ : D → ℝ) : 𝓢(D,F) →L[ℝ] 𝓢(D,E) :=
  SchwartzMap.smulLeftCLM E (fun x => (ρ x)⁻¹) ∘L
    formalAdjoint e (fun i => weightedCoefficient ρ (a i)) (weightedCoefficient ρ b)

lemma weighted_firstOrder_pairing (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F))
    (b : 𝓢(D,E →L[ℝ] F)) (ρ : D → ℝ) (hρ : ρ.HasTemperateGrowth)
    (hiρ : (fun x => (ρ x)⁻¹).HasTemperateGrowth) (hρn : ∀ x, ρ x ≠ 0)
    (u : 𝓢(D,E)) (v : 𝓢(D,F)) :
    (∫ x, ρ x * ⟪firstOrder e a b u x, v x⟫) =
      ∫ x, ρ x * ⟪u x, weightedFormalAdjoint e a b ρ v x⟫ := by
  have h := firstOrder_pairing e (fun i => weightedCoefficient ρ (a i))
    (weightedCoefficient ρ b) u v
  simp only [weighted_firstOrder e a b ρ hρ, real_inner_smul_left] at h
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_)))
  simp only [weightedFormalAdjoint, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hiρ, real_inner_smul_right]
  rw [← mul_assoc, mul_inv_cancel₀ (hρn x), one_mul]

end TamingCompatibility.LocalFormalAdjoint

end

end OAI
