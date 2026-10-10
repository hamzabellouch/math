import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

/-! The actual interval traversal used to compare circle embeddings with
interval-loop formulations of the Jordan--Schoenflies theorem. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def standardCircleTraversal (t : ℝ) : Circle := Circle.exp (2 * Real.pi * t)

lemma continuous_standardCircleTraversal : Continuous standardCircleTraversal :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

lemma standardCircleTraversal_closes : standardCircleTraversal 0 = standardCircleTraversal 1 := by
  simp [standardCircleTraversal]

lemma standardCircleTraversal_injOn : InjOn standardCircleTraversal (Ico 0 1) := by
  intro s hs t ht he
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  have hs' : 2 * Real.pi * s ∈ Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hp.le hs.1, by nlinarith [ht.1, hs.2]⟩
  have ht' : 2 * Real.pi * t ∈ Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hp.le ht.1, by nlinarith [ht.2]⟩
  have heq := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hs' ht' he
  nlinarith

lemma standardCircleTraversal_image : standardCircleTraversal '' Icc 0 1 = univ := by
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  have hcover : Circle.exp '' Icc 0 (2 * Real.pi) = univ := by
    simpa only [zero_add, Circle.exp_surjective.range_eq] using
      Circle.periodic_exp.image_Icc hp 0
  apply eq_univ_of_forall
  intro z
  have hz : z ∈ Circle.exp '' Icc 0 (2 * Real.pi) := by rw [hcover]; trivial
  obtain ⟨a, ha, he⟩ := hz
  refine ⟨a / (2 * Real.pi), ⟨div_nonneg ha.1 hp.le, (div_le_one hp).2 ha.2⟩, ?_⟩
  have heq : 2 * Real.pi * (a / (2 * Real.pi)) = a := by field_simp
  simpa only [standardCircleTraversal, heq] using he

end CircleDomainRigidity

end

end OAI
