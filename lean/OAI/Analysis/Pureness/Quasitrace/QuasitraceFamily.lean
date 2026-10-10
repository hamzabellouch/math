import OAI.Analysis.Pureness.Quasitrace.QuasitraceNaturality
import OAI.Analysis.Pureness.Quasitrace.QuasitraceNonUnitalRestriction

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule IsMulCommutative

structure ComplexQuasitrace (D : Type*) [CStarAlgebra D] where
  toFun : D → ℂ
  polar : ∀ x, toFun (star x*x) = toFun (x*star x)
  square_nonneg : ∀ x, 0 ≤ toFun (star x*x)
  real_add_I : ∀ a b : selfAdjoint D, toFun (a.1+Complex.I • b.1) = toFun a.1+Complex.I*toFun b.1
  abelian_linear : ∀ (S : NonUnitalStarSubalgebra ℂ D) [IsMulCommutative S],
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = toFun x.1

instance {D : Type*} [CStarAlgebra D] : CoeFun (ComplexQuasitrace D) (fun _ => D → ℂ) :=
  ⟨ComplexQuasitrace.toFun⟩

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def PositiveQuasitrace.toComplex (T : PositiveQuasitrace D) : ComplexQuasitrace D where
  toFun := T.complexValue
  polar := T.complexValue_polar
  square_nonneg := T.complexValue_square_nonneg
  real_add_I := T.complexValue_real_add_I
  abelian_linear S _ := ⟨T.nonUnitalSubalgebraComplexLinear S,T.nonUnitalSubalgebraComplexLinear_eq S⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure CompatibleFiniteQuasitrace (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  level : ∀ n, ComplexQuasitrace (FinMatrix A n)
  inclusion : ∀ {n m} (h : n ≤ m) (x : FinMatrix A n), level m (matrixInclusion h x) = level n x

def finiteSpectralQuasitraceFamily
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) : CompatibleFiniteQuasitrace A where
  level n := (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n).toComplex
  inclusion := by
    intro n m h x
    change (finiteSpectralPositiveQuasitrace d hd hlsc hfinite m).complexValue (matrixInclusion h x) =
      (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n).complexValue x
    exact PositiveQuasitrace.complexValue_map
      (finiteSpectralPositiveQuasitrace d hd hlsc hfinite m)
      (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n) (matrixInclusion h)
      (finiteSpectralPositiveQuasitrace_inclusion d hd hlsc hfinite h) x

lemma finiteSpectralQuasitraceFamily_positive
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) (M : Positive (FinMatrix A n)) :
    (finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n M.1 = ((finiteSpectralIntegral d n M).toReal : ℂ) :=
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n).complexValue_positive M

theorem finiteSpectralQuasitraceFamily_root_rank
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) (M : Positive (FinMatrix A n)) :
    Filter.Tendsto (fun k => ENNReal.ofReal (((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n
      (Positive.power (Positive.rootExponent k) M).1).re)) Filter.atTop
      (nhds (d (finitePositiveClass n M))) := by
  simp only [finiteSpectralQuasitraceFamily_positive,Complex.ofReal_re]
  exact finiteSpectralPositiveQuasitrace_root_rank d hd hlsc hfinite n M
end CuntzPureness

end

end OAI
