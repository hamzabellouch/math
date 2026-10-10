import OAI.Algebra.AuslanderReiten.Bar.TCasimirAugmentation
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleDetector

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def simpleActionAt (s : S) : R →ₗ[k] S :=
  ((Algebra.lsmul k k S).toLinearMap).flip s

@[simp] theorem simpleActionAt_apply (s : S) (a : R) : simpleActionAt q s a = a • s := rfl

def evaluateAtSimple (s : S) : R ⊗[k] R →ₗ[k] R ⊗[k] S :=
  TensorProduct.map (LinearMap.id : R →ₗ[k] R) (simpleActionAt q s)

theorem twistedCasimir_evaluation (H : kˣ) (hq1 : 1 + q ≠ 0) (s : S) :
    evaluateAtSimple q s (twistedCasimir q H) = ((H : k) • upper q .f) ⊗ₜ[k] s := by
  simp only [evaluateAtSimple, twistedCasimir, map_sum, TensorProduct.map_tmul,
    LinearMap.id_apply, simpleActionAt_apply, CocycleData.vector_smul_simple q hq1]
  rw [Finset.sum_eq_single (true, .f)]
  · have ht := CocycleData.twist_vector q H (true, .f)
    simp only [TIndex.weight, reduceIte, pow_one, vector] at ht
    simpa [TIndex.star, vector] using! congrArg (fun a : R => a ⊗ₜ[k] s) ht
  · intro i _ hi
    have hn : TIndex.star i ≠ (false, Letter.f) := by
      intro he
      have hh := congrArg TIndex.star he
      simp only [star_star] at hh
      exact hi hh
    simp [hn]
  · simp

def evaluatedDetector : R ⊗[k] S →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (coefficient q (true, .f)) (Resolution.simpleCoordinate q))

@[simp] theorem evaluatedDetector_tmul (a : R) (s : S) :
    evaluatedDetector q (a ⊗ₜ[k] s) = coefficient q (true, .f) a * Resolution.simpleCoordinate q s := by
  simp [evaluatedDetector]

theorem twistedCasimir_evaluation_ne_zero (H : kˣ) (hq1 : 1 + q ≠ 0) :
    evaluateAtSimple q (CocycleData.simpleGenerator q) (twistedCasimir q H) ≠ 0 := by
  rw [twistedCasimir_evaluation q H hq1]
  intro hz
  have hh := congrArg (evaluatedDetector q) hz
  simp at hh

end ArExplicit.T

end

end OAI
