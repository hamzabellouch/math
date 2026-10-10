import OAI.Analysis.Pureness.Quasitrace.QuasitraceFunctionCarrier
import OAI.Analysis.Pureness.Quasitrace.TwoQuasitraceBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev QuasitraceCoordinates (A : Type*) [CStarAlgebra A] :=
  (A → ℂ) × (FinMatrix A 2 → ℂ)

def TwoQuasitrace.coordinates (T : TwoQuasitrace A) : QuasitraceCoordinates A :=
  (T.base.toFun, T.matrix.toFun)

def normalizedQuasitraceCarrier : Set (QuasitraceCoordinates A) :=
  {p | p.1 ∈ complexQuasitraceCarrier ∧ p.2 ∈ complexQuasitraceCarrier ∧
    p.1 1 = 1 ∧ ∀ x : A, p.1 x = p.2 (firstMatrixCorner x)}

lemma TwoQuasitrace.coordinates_mem (T : TwoQuasitrace A) (hT : T.base 1 = 1) :
    T.coordinates ∈ normalizedQuasitraceCarrier :=
  ⟨T.base.mem_carrier, T.matrix.mem_carrier, hT, T.extension⟩

def twoQuasitraceFromCoordinates (p : QuasitraceCoordinates A)
    (hp : p ∈ normalizedQuasitraceCarrier) : TwoQuasitrace A where
  base := complexQuasitraceFromCarrier p.1 hp.1
  matrix := complexQuasitraceFromCarrier p.2 hp.2.1
  extension := hp.2.2.2

lemma twoQuasitraceFromCoordinates_unit (p : QuasitraceCoordinates A)
    (hp : p ∈ normalizedQuasitraceCarrier) :
    (twoQuasitraceFromCoordinates p hp).base 1 = 1 := hp.2.2.1

lemma range_normalized_quasitrace_coordinates :
    {p | ∃ T : TwoQuasitrace A, T.base 1 = 1 ∧ T.coordinates = p} =
      normalizedQuasitraceCarrier := by
  ext p
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact T.coordinates_mem hT
  · intro hp
    exact ⟨twoQuasitraceFromCoordinates p hp, hp.2.2.1, rfl⟩

lemma isClosed_normalizedQuasitraceCarrier :
    IsClosed (normalizedQuasitraceCarrier (A := A)) := by
  exact (isClosed_complexQuasitraceCarrier.preimage continuous_fst).inter
    ((isClosed_complexQuasitraceCarrier.preimage continuous_snd).inter
      ((isClosed_eq ((continuous_apply 1).comp continuous_fst) continuous_const).inter
        (isClosed_forall_pointwise _ fun x => isClosed_eq
          ((continuous_apply x).comp continuous_fst)
          ((continuous_apply (firstMatrixCorner x)).comp continuous_snd))))

lemma convex_normalizedQuasitraceCarrier :
    Convex ℝ (normalizedQuasitraceCarrier (A := A)) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_complexQuasitraceCarrier hp.1 hq.1 ha hb hab,
    convex_complexQuasitraceCarrier hp.2.1 hq.2.1 ha hb hab, ?_, ?_⟩
  · change (a : ℂ) * p.1 1 + (b : ℂ) * q.1 1 = 1
    rw [hp.2.2.1, hq.2.2.1, mul_one, mul_one, ← Complex.ofReal_add, hab, Complex.ofReal_one]
  · intro x
    change (a : ℂ) * p.1 x + (b : ℂ) * q.1 x =
      (a : ℂ) * p.2 (firstMatrixCorner x) + (b : ℂ) * q.2 (firstMatrixCorner x)
    rw [hp.2.2.2, hq.2.2.2]

theorem isCompact_normalizedQuasitraceCarrier :
    IsCompact (normalizedQuasitraceCarrier (A := A)) := by
  have hbase : IsCompact {f : A → ℂ | ∀ x, f x ∈ Metric.closedBall 0 (8 * ‖x‖)} :=
    isCompact_pi_infinite fun x => isCompact_closedBall 0 (8 * ‖x‖)
  have hmatrix : IsCompact {f : FinMatrix A 2 → ℂ | ∀ x, f x ∈ Metric.closedBall 0 (16 * ‖x‖)} :=
    isCompact_pi_infinite fun x => isCompact_closedBall 0 (16 * ‖x‖)
  apply (hbase.prod hmatrix).of_isClosed_subset isClosed_normalizedQuasitraceCarrier
  intro p hp
  let T := twoQuasitraceFromCoordinates p hp
  constructor
  · intro x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact T.normalized_base_bound hp.2.2.1 x
  · intro x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact T.normalized_matrix_bound hp.2.2.1 x
end CuntzPureness

end

end OAI
