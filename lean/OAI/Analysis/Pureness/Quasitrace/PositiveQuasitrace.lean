import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralCommuting
import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralRootLimit
import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralContinuity
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder

structure PositiveQuasitrace (D : Type*) [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] where
  toFun : Positive D → ℝ
  nonneg : ∀ a, 0 ≤ toFun a
  map_zero : toFun Positive.zero = 0
  map_add_commute : ∀ a b, Commute a.1 b.1 → toFun (Positive.add a b) = toFun a+toFun b
  map_smul : ∀ (r : ℝ≥0) a, toFun (Positive.smul r a) = (r : ℝ)*toFun a
  polar : ∀ x : D, toFun (Positive.starMul x) = toFun (Positive.mulStar x)
  monotone : Monotone toFun

instance {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] :
    CoeFun (PositiveQuasitrace D) (fun _ => Positive D → ℝ) := ⟨PositiveQuasitrace.toFun⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteSpectralPositiveQuasitrace
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) : PositiveQuasitrace (FinMatrix A n) where
  toFun M := (finiteSpectralIntegral d n M).toReal
  nonneg _ := ENNReal.toReal_nonneg
  map_zero := by rw [finiteSpectralIntegral_zero,ENNReal.toReal_zero]
  map_add_commute M N h := by
    rw [finiteSpectralIntegral_add_commute d hd hlsc hfinite n M N h,
      ENNReal.toReal_add (finiteSpectralIntegral_ne_top d hd n M (hfinite _))
        (finiteSpectralIntegral_ne_top d hd n N (hfinite _))]
  map_smul r M := by rw [finiteSpectralIntegral_smul d hd,ENNReal.toReal_mul,ENNReal.coe_toReal]
  polar x := congrArg ENNReal.toReal (finiteSpectralIntegral_polar d n x)
  monotone := fun M N h => (ENNReal.toReal_le_toReal
    (finiteSpectralIntegral_ne_top d hd n M (hfinite _))
    (finiteSpectralIntegral_ne_top d hd n N (hfinite _))).mpr (finiteSpectralIntegral_monotone d hd n h)

lemma finiteSpectralPositiveQuasitrace_inclusion
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) {n m : ℕ} (h : n ≤ m) (M : Positive (FinMatrix A n)) :
    finiteSpectralPositiveQuasitrace d hd hlsc hfinite m (Positive.map (matrixInclusion h) M) =
      finiteSpectralPositiveQuasitrace d hd hlsc hfinite n M :=
  congrArg ENNReal.toReal (finiteSpectralIntegral_inclusion d h M)

lemma finiteSpectralPositiveQuasitrace_root_rank
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) (M : Positive (FinMatrix A n)) :
    Filter.Tendsto (fun k => ENNReal.ofReal (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
      (Positive.power (Positive.rootExponent k) M))) Filter.atTop
      (nhds (d (finitePositiveClass n M))) := by
  have he (k : ℕ) : ENNReal.ofReal (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
      (Positive.power (Positive.rootExponent k) M)) = finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M) :=
    ENNReal.ofReal_toReal (finiteSpectralIntegral_ne_top d hd n _ (hfinite _))
  simp only [he]
  exact finiteSpectralIntegral_roots_tendsto d hd hlsc n M
end CuntzPureness

end

end OAI
