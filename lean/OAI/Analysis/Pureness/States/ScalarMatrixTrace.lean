import OAI.Analysis.Pureness.States.ScalarMatrixEmbedding
import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricSize

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def TracialState.toPositiveQuasitrace (τ : TracialState A) : PositiveQuasitrace A where
  toFun a := (τ.functional a.1).re
  nonneg a := (Complex.le_def.mp (τ.functional.map_nonneg a.2)).1
  map_zero := by simp [Positive.zero]
  map_add_commute a b _ := by simp [Positive.add, map_add]
  map_smul r a := by
    change (τ.functional ((r : ℝ) • a.1)).re = _
    rw [τ.functional.map_smul_of_tower]
    simp
  polar x := congrArg Complex.re (τ.tracial (star x) x)
  monotone a b hab := (Complex.le_def.mp (τ.functional.monotone hab)).1

lemma TracialState.toPositiveQuasitrace_unit (τ : TracialState A) :
    τ.toPositiveQuasitrace ⟨1,zero_le_one⟩ = 1 := by
  change (τ.functional 1).re = 1
  rw [τ.normalized]; rfl

lemma TracialState.toPositiveQuasitrace_add (τ : TracialState A) (a b : Positive A) :
    τ.toPositiveQuasitrace (Positive.add a b) = τ.toPositiveQuasitrace a+τ.toPositiveQuasitrace b := by
  change (τ.functional (a.1+b.1)).re = _
  rw [map_add,Complex.add_re]; rfl

lemma TracialState.toPositiveQuasitrace_sqrt_add (τ : TracialState A) (a b : Positive A) :
    Real.sqrt (τ.toPositiveQuasitrace (Positive.add a b)) ≤
      Real.sqrt (τ.toPositiveQuasitrace a)+Real.sqrt (τ.toPositiveQuasitrace b) := by
  rw [τ.toPositiveQuasitrace_add]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (add_nonneg (τ.toPositiveQuasitrace.nonneg a) (τ.toPositiveQuasitrace.nonneg b))]
  nlinarith [Real.sq_sqrt (τ.toPositiveQuasitrace.nonneg a),
    Real.sq_sqrt (τ.toPositiveQuasitrace.nonneg b),Real.sqrt_nonneg (τ.toPositiveQuasitrace a),
    Real.sqrt_nonneg (τ.toPositiveQuasitrace b)]

lemma TracialState.toPositiveQuasitrace_metricSize_add (τ : TracialState A) (x y : A) :
    τ.toPositiveQuasitrace.metricSize (x+y) ≤
      τ.toPositiveQuasitrace.metricSize x+τ.toPositiveQuasitrace.metricSize y := by
  let T := τ.toPositiveQuasitrace
  have hw (r : ℝ) (hr : r ≠ 0) : T (Positive.starMul (x+y)) ≤
      (Real.sqrt ((1+r*r)*T (Positive.starMul x))+
        Real.sqrt ((1+r⁻¹*r⁻¹)*T (Positive.starMul y)))^2 := by
    let u : ℝ≥0 := ⟨1+r*r,by nlinarith [sq_nonneg r]⟩
    let v : ℝ≥0 := ⟨1+r⁻¹*r⁻¹,by nlinarith [sq_nonneg r⁻¹]⟩
    have ho : Positive.starMul (x+y) ≤ Positive.add
        (Positive.smul u (Positive.starMul x)) (Positive.smul v (Positive.starMul y)) :=
      star_square_add_le_weighted x y r hr
    have hs := τ.toPositiveQuasitrace_sqrt_add
      (Positive.smul u (Positive.starMul x)) (Positive.smul v (Positive.starMul y))
    change Real.sqrt (T _) ≤ Real.sqrt (T _)+Real.sqrt (T _) at hs
    rw [T.map_smul,T.map_smul] at hs
    exact (T.monotone ho).trans (by
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hs
      rwa [Real.sq_sqrt (T.nonneg _)] at hsq)
  have hc := weighted_scalar_cube_bound (T (Positive.starMul x)) (T (Positive.starMul y))
    (T (Positive.starMul (x+y))) (T.nonneg _) (T.nonneg _) hw
  have h : T.metricSize (x+y)^3 ≤ (T.metricSize x+T.metricSize y)^3 := by
    rw [T.metricSize_cube]
    exact hc
  exact (pow_le_pow_iff_left₀ (T.metricSize_nonneg _)
    (add_nonneg (T.metricSize_nonneg _) (T.metricSize_nonneg _)) (by decide : 3 ≠ 0)).mp h

def complexScalarTracialState : TracialState ℂ where
  functional := { LinearMap.id with monotone' := fun _ _ h => h }
  normalized := rfl
  tracial := mul_comm

def scalarMatrixTracialState (n : ℕ) : TracialState (FinMatrix ℂ (n+1)) :=
  matrixTracialState complexScalarTracialState

def scalarMatrixPositiveTrace (n : ℕ) : PositiveQuasitrace (FinMatrix ℂ (n+1)) :=
  (scalarMatrixTracialState n).toPositiveQuasitrace

lemma scalarMatrixPositiveTrace_unit (n : ℕ) : scalarMatrixPositiveTrace n ⟨1,zero_le_one⟩ = 1 :=
  (scalarMatrixTracialState n).toPositiveQuasitrace_unit

lemma scalarMatrixPositiveTrace_complex (n : ℕ) (z : FinMatrix ℂ (n+1)) :
    (scalarMatrixPositiveTrace n).complexValue z =
      (n+1 : ℂ)⁻¹ * Matrix.trace (CStarMatrix.ofMatrix.symm z) := by
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    positiveQuasitrace_scalarMatrix_normalized (scalarMatrixPositiveTrace n) (0 : Fin (n+1))
      (scalarMatrixPositiveTrace_unit n) z

lemma scalarMatrixPositiveTrace_metricSize_add (n : ℕ) (x y : FinMatrix ℂ (n+1)) :
    (scalarMatrixPositiveTrace n).metricSize (x+y) ≤
      (scalarMatrixPositiveTrace n).metricSize x+(scalarMatrixPositiveTrace n).metricSize y :=
  (scalarMatrixTracialState n).toPositiveQuasitrace_metricSize_add x y

lemma scalarMatrixPositiveTrace_sqrt_add (n : ℕ) (a b : Positive (FinMatrix ℂ (n+1))) :
    Real.sqrt (scalarMatrixPositiveTrace n (Positive.add a b)) ≤
      Real.sqrt (scalarMatrixPositiveTrace n a)+Real.sqrt (scalarMatrixPositiveTrace n b) :=
  (scalarMatrixTracialState n).toPositiveQuasitrace_sqrt_add a b
end CuntzPureness

end

end OAI
