import Mathlib
import OAI.Probability.SKBarriers.Calculus.CoordinateSigns

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def hierarchyJointMoment {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (U L : S → ParameterSpace n →L[ℝ] ℝ) (a : ℕ) : ℝ :=
  ∑ s, ∫ z, (L s z)^a * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s z-
    hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) ∂fiberMeasure n 0

theorem hierarchy_gauge_linear_variance
    {S : Type} [Fintype S] [Nonempty S] (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    (hU₀ : ∀ s, U s (parameterAxis n) = 0)
    (hL₀ : ∀ s, L s (parameterAxis n) = 0)
    {A : ℝ} (hA : 0 ≤ A) (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    (s₀ : S) (b : S → Fin n → Bool) (p : S → Equiv.Perm S)
    (hp : ∀ s, p s s = s₀)
    (hUg : ∀ s r z, U r (coordinateSign n (b s) z) = U (p s r) z)
    (hLg : ∀ s z, L s (coordinateSign n (b s) z) = L s₀ z) :
    hierarchyJointMoment n m U L 2 / hierarchyJointMoment n m U L 0 -
      (hierarchyJointMoment n m U L 1 / hierarchyJointMoment n m U L 0)^2 ≤ A := by
  let I (a : ℕ) := ∫ z, (L s₀ z)^a * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s₀ z-
    hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) ∂fiberMeasure n 0
  have he (a : ℕ) (s : S) :
      (∫ z, (L s z)^a * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s z-
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) ∂fiberMeasure n 0) = I a := by
    have hh := fixed_spin_gauge_integral n m (fun _ : S => 0) U (b s) (p s)
      (fun _ => rfl) (hUg s) s (fun z => (L s z)^a) (fun z => (L s₀ z)^a)
      (fun z => congrArg (fun x : ℝ => x^a) (hLg s z))
    simpa only [hp] using hh
  have hsum (a : ℕ) : hierarchyJointMoment n m U L a = (Fintype.card S : ℝ)*I a := by
    unfold hierarchyJointMoment
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [hsum,mul_div_mul_left _ _ hc]
  have hBL := hierarchy_fixed_spin_linear_variance n m hm hmu hmono (fun _ : S => 0) U hU₀ s₀
    (L s₀) (hL₀ s₀) hA (hL s₀)
  have hV (z : ParameterSpace n) :
      -((1/2 : ℝ)*coordinateSquare n z-U s₀ z+
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) =
      -(1/2 : ℝ)*coordinateSquare n z+U s₀ z-
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z := by ring
  simpa only [I,pow_zero,one_mul,pow_one,hV] using hBL

def coordinateProjection : (n : ℕ) → Fin n → ParameterSpace n →L[ℝ] ℝ
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (ContinuousLinearMap.snd ℝ (ParameterSpace n) ℝ)
      (fun j => (coordinateProjection n j).comp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)) i

@[simp] theorem coordinateProjection_last (n : ℕ) (z : ParameterSpace (n+1)) :
    coordinateProjection (n+1) (Fin.last n) z = z.2 := by simp [coordinateProjection]

@[simp] theorem coordinateProjection_castSucc (n : ℕ) (i : Fin n) (z : ParameterSpace (n+1)) :
    coordinateProjection (n+1) i.castSucc z = coordinateProjection n i z.1 := by
  simp [coordinateProjection]

theorem coordinateSquare_eq_sum (n : ℕ) (z : ParameterSpace n) :
    coordinateSquare n z = ∑ i, (coordinateProjection n i z)^2 := by
  induction n with
  | zero => simp [coordinateSquare]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [coordinateProjection,Fin.lastCases_last,Fin.lastCases_castSucc,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      coordinateSquare]
    rw [ih z.1]

theorem coordinateProjection_axis (n : ℕ) (i : Fin n) :
    coordinateProjection n i (parameterAxis n) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateProjection,parameterAxis]
    · simpa only [coordinateProjection,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',parameterAxis] using ih j

theorem coordinateProjection_sign (n : ℕ) (b : Fin n → Bool) (i : Fin n) (z : ParameterSpace n) :
    coordinateProjection n i (coordinateSign n b z) = scalarSign (b i) (coordinateProjection n i z) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateProjection,coordinateSign]
    · simpa only [coordinateProjection,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',coordinateSign] using
        ih (fun i => b i.castSucc) j z.1

def coordinateLinear (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n →L[ℝ] ℝ :=
  ∑ i, a i • coordinateProjection n i

theorem coordinateLinear_apply (n : ℕ) (a : Fin n → ℝ) (z : ParameterSpace n) :
    coordinateLinear n a z = ∑ i, a i*coordinateProjection n i z := by
  simp [coordinateLinear]

theorem coordinateLinear_axis (n : ℕ) (a : Fin n → ℝ) :
    coordinateLinear n a (parameterAxis n) = 0 := by
  simp [coordinateLinear_apply,coordinateProjection_axis]

theorem coordinateLinear_sq_le (n : ℕ) (a : Fin n → ℝ) (z : ParameterSpace n) :
    (coordinateLinear n a z)^2 ≤ (∑ i, (a i)^2)*coordinateSquare n z := by
  rw [coordinateLinear_apply,coordinateSquare_eq_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun i => coordinateProjection n i z)

end SK.Analytic

end
end
end
end
end
end

end OAI
