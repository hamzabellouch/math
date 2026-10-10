import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

namespace CannonAtomic

attribute [local instance] Classical.propDecidable

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def dirac (p : X) : FiniteMeasure X := ⟨Measure.dirac p,inferInstance⟩

def atomic (p : ι → X) (w : ι → ℝ) (M : ℝ) (_hM : 0 ≤ M) : FiniteMeasure X :=
  ∑ i, Real.toNNReal (M*(w i)^2) • dirac (p i)

lemma dirac_apply (p : X) (S : Set X) (hS : MeasurableSet S) :
    (dirac p S : ℝ) = if p ∈ S then 1 else 0 := by
  classical
  rw [dirac, FiniteMeasure.mk_apply]
  rw [Measure.dirac_apply' p hS]
  by_cases hp : p ∈ S <;> simp [hp]

lemma sum_apply {κ : Type*} (F : κ → FiniteMeasure X) (s : Finset κ) (S : Set X) :
    ((∑ i ∈ s, F i) S : ℝ) = ∑ i ∈ s, (F i S : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, FiniteMeasure.coeFn_add, Pi.add_apply,
      NNReal.coe_add, ih]

theorem atomic_apply (p : ι → X) (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (S : Set X) (hS : MeasurableSet S) :
    (atomic p w M hM S : ℝ) = M*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2) := by
  classical
  rw [atomic, sum_apply]
  rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteMeasure.smul_apply]
  change ((Real.toNNReal (M*w i^2) * dirac (p i) S : NNReal) : ℝ) = _
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hM (sq_nonneg _)),
    dirac_apply _ S hS]
  split_ifs <;> simp

lemma atomic_mass (p : ι → X) (w : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    ((atomic p w M hM).mass : ℝ) = M*(∑ i, (w i)^2) := by
  simpa only [FiniteMeasure.mass, mem_univ, Finset.filter_true] using
    atomic_apply p w M hM univ MeasurableSet.univ

theorem mass_bound (p : ι → X) (w : ι → ℝ) (M : ℝ) (hM : 0 < M)
    (C : ℝ) (henergy : (∑ i, (w i)^2) ≤ C/M) :
    ((atomic p w M hM.le).mass : ℝ) ≤ C := by
  rw [atomic_mass]
  exact (mul_le_mul_of_nonneg_left henergy hM.le).trans_eq (by field_simp)

end CannonAtomic

end
end
end
end
end
end
end
end
end

end OAI
