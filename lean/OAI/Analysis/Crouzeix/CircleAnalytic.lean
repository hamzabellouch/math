import Mathlib
import OAI.Analysis.Crouzeix.CauchyProjection
import OAI.Analysis.Crouzeix.CircleCoordinate
import OAI.Analysis.Crouzeix.SeparateHolomorphic

namespace OAI

/-! Circle Analytic. -/

noncomputable section

open Set Metric Filter Topology Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

local instance circleAnalyticFactZeroLtOne : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma integral_circleMeasure_eq_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : CircleSpace → E) :
    (∫ t, f t ∂circleMeasure) = ∫ t in (0 : ℝ)..1, f (t : CircleSpace) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]

lemma differentiableOn_parameter_circleIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {V : Set ℂ} (hV : IsOpen V)
    {f : ℂ → CircleSpace → E}
    (hf : ContinuousOn (Function.uncurry f) (V ×ˢ univ))
    (hd : ∀ t, DifferentiableOn ℂ (fun z => f z t) V) :
    DifferentiableOn ℂ (fun z => ∫ t, f z t ∂circleMeasure) V := by
  simp_rw [integral_circleMeasure_eq_interval]
  apply differentiableOn_parameter_intervalIntegral hV
  · exact hf.comp (f := fun p : ℂ × ℝ => (p.1,(p.2 : CircleSpace)))
      (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  · exact fun t _ => hd (t : CircleSpace)

@[simp] lemma circleCoordinate_pow (n : ℕ) (t : CircleSpace) :
    (circleCoordinate t)^n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]; rfl

@[simp] lemma circleCoordinate_inverse_pow (n : ℕ) (t : CircleSpace) :
    ((circleCoordinate t)⁻¹)^n = fourier (-(n : ℤ)) t := by
  rw [Complex.inv_eq_conj (norm_circleCoordinate t), ← map_pow, circleCoordinate_pow, fourier_neg]

lemma fourierCoeff_inverse_holomorphic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (n : ℕ) :
    fourierCoeff (fun t : CircleSpace => f (circleCoordinate t)⁻¹) (n : ℤ) =
      if n = 0 then f 0 else 0 := by
  change (∫ t : CircleSpace, fourier (-(n : ℤ)) t • f (circleCoordinate t)⁻¹ ∂circleMeasure) = _
  simp_rw [← circleCoordinate_inverse_pow]
  rw [integral_holomorphic_inverse_circleCoordinate (f := fun u => u^n • f u)
    ((differentiableOn_id.pow n).smul hf)]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, zero_pow hn]

lemma repr_boundaryField {k : ℕ} (F : C(CircleSpace, Coeff k))
    (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr (boundaryField F) a =
      fourierCoeff (fun t => F t a.2.1 a.2.2) a.1 := by
  rw [matrixFourierBasis_repr]
  apply congrFun (fourierCoeff_congr_ae ?_) a.1
  filter_upwards [lpEntry_apply_ae a.2 (boundaryField F), boundaryField_apply_ae F] with t he hf
  rw [he, hf]
  rfl

lemma fourierProj_boundaryField_inverse_zero {k : ℕ} (F : C(CircleSpace, Coeff k))
    {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    fourierProjC k 0 (boundaryField F) = 0 ∧ fourierProjC k 1 (boundaryField F) = 0 := by
  classical
  have hr (a : ℤ × (Fin k × Fin k)) (ha : 0 ≤ a.1) :
      (matrixFourierBasis k).repr (boundaryField F) a = 0 := by
    rcases a with ⟨n,i,j⟩
    obtain ⟨m,rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [repr_boundaryField]
    simp_rw [hF]
    rw [fourierCoeff_inverse_holomorphic (hf i j)]
    split_ifs <;> simp [h0]
  constructor
  · apply (matrixFourierBasis k).repr.injective
    ext a
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 0 a.1 then _ else 0) = 0
    split_ifs with ha
    · exact hr a (le_of_eq ((frequencyPart_zero a.1).mp ha).symm)
    · rfl
  · apply (matrixFourierBasis k).repr.injective
    ext a
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 1 a.1 then _ else 0) = 0
    split_ifs with ha
    · exact hr a ((frequencyPart_pos a.1).mp ha).le
    · rfl

lemma fourierProj_boundaryField_inverse_neg {k : ℕ} (F : C(CircleSpace, Coeff k))
    {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    fourierProjC k 2 (boundaryField F) = boundaryField F := by
  have hh := congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L (boundaryField F))
    (fourierProjC_total k)
  have hz := fourierProj_boundaryField_inverse_zero F hf h0 hF
  simpa only [add_apply, hz.1, hz.2, zero_add,
    ContinuousLinearMap.id_apply] using hh

lemma boundaryCauchy_inverse_zero {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k)
    (F : C(CircleSpace, Coeff k)) {f : ℂ → Coeff k}
    (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    boundaryCauchy M (boundaryField F) = 0 := by
  have hz := fourierProj_boundaryField_inverse_zero F hf h0 hF
  change fourierProjC k 0 (boundaryField F) + fourierProjC k 1 (boundaryField F) +
    fourierProjC k 2 (M (fourierProjC k 1 (boundaryField F))) = 0
  simp only [hz.1, hz.2, map_zero, add_zero]

open scoped Classical in

lemma fourierProj_matrixFourier {k : ℕ} (i : Fin 3) (a : ℤ × (Fin k × Fin k)) :
    fourierProjC k i (matrixFourier a) = if frequencyPart i a.1 then matrixFourier a else 0 := by
  classical
  apply (matrixFourierBasis k).repr.injective
  ext b
  rw [repr_fourierProjC]
  by_cases hba : b = a
  · subst b
    split_ifs <;> simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
  · have hz : (matrixFourierBasis k).repr (matrixFourier a) b = 0 := by
      rw [← matrixFourierBasis_apply, HilbertBasis.repr_self]
      simp [hba]
    split_ifs <;> simp only [hz, map_zero, lp.coeFn_zero, Pi.zero_apply]

end CrouzeixHilbert.Boundary

end

end OAI
