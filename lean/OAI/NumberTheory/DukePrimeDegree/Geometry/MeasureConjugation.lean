import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizerKernelCovariance

namespace OAI

/-!
# Conjugation of the actual measure stabilizer

Right translation conjugates stabilizers in the opposite direction.
These identities apply to arbitrary measures and do not assume that the
translating element preserves the measure.
-/

noncomputable section
open MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

lemma map_rightAction_mul {n : ℕ} (μ : Measure (X n)) (a b : G n) :
    (μ.map (fun x => rightAction x a)).map (fun x => rightAction x b) =
      μ.map (fun x => rightAction x (a * b)) := by
  rw [Measure.map_map (continuous_rightAction b).measurable
    (continuous_rightAction a).measurable]
  congr 1
  funext x
  exact rightAction_mul x a b

lemma map_rightAction_injective {n : ℕ} (a : G n) :
    Function.Injective (fun μ : Measure (X n) => μ.map (fun x => rightAction x a)) := by
  intro μ ν h
  have he := congrArg (fun ρ : Measure (X n) =>
    ρ.map (fun x => rightAction x a⁻¹)) h
  simpa only [map_rightAction_mul, mul_inv_cancel, rightAction_one,
    Measure.map_id'] using he

lemma mem_invariantRightSubgroup_map_iff {n : ℕ}
    (μ : Measure (X n)) (a g : G n) :
    g ∈ invariantRightSubgroup (μ.map (fun x => rightAction x a)) ↔
      a * g * a⁻¹ ∈ invariantRightSubgroup μ := by
  change (μ.map (fun x => rightAction x a)).map (fun x => rightAction x g) =
    μ.map (fun x => rightAction x a) ↔
    μ.map (fun x => rightAction x (a * g * a⁻¹)) = μ
  constructor
  · intro h
    have he := congrArg (fun ρ : Measure (X n) =>
      ρ.map (fun x => rightAction x a⁻¹)) h
    simpa only [map_rightAction_mul, mul_inv_cancel, rightAction_one,
      Measure.map_id'] using he
  · intro h
    apply map_rightAction_injective a⁻¹
    simpa only [map_rightAction_mul, mul_inv_cancel, rightAction_one,
      Measure.map_id'] using h

end DukePrimeDegree

end

end OAI
