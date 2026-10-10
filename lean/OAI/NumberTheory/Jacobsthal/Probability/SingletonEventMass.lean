import OAI.NumberTheory.Jacobsthal.Estimates.HarmonicConditioning
import OAI.NumberTheory.Jacobsthal.Partitions.TwoSingletonBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices SingletonBinSelection SingletonBinSum CanonicalSubsetBox ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem singleton_event_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hi : m i = 1)
    (E : (Fin n → Finset ℕ) → Prop) :
    (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) =
      ∑ f ∈ selections P (eraseMultiplicity m i),(selectionProduct f : ℝ)⁻¹*
        harmonicMass ((P i).filter (fun p => E (fillSelection f i p))) := by
  have he := singleton_weighted_sum P m i hi (fun f => if E f then (1 : ℝ) else 0)
  have hl : (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) =
      ∑ f ∈ selections P m,(selectionProduct f : ℝ)⁻¹*(if E f then (1 : ℝ) else 0) := by
    simp only [Finset.sum_filter,mul_ite,mul_one,mul_zero]
  rw [hl,he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _hf
  rw [harmonicMass,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

theorem singleton_total_mass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hi : m i = 1) :
    selectionMass P m = harmonicMass (P i)*selectionMass P (eraseMultiplicity m i) := by
  have he := singleton_event_sum P m i hi (fun _ => True)
  simp only [Finset.filter_true] at he
  change selectionMass P m = _ at he
  rw [he,← Finset.sum_mul]
  change selectionMass P (eraseMultiplicity m i)*harmonicMass (P i) = _
  ring

theorem singleton_event_mass_bound {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hi : m i = 1)
    (E : (Fin n → Finset ℕ) → Prop) (rho : ℝ)
    (h : ∀ f ∈ selections P (eraseMultiplicity m i),
      harmonicMass ((P i).filter (fun p => E (fillSelection f i p))) ≤ rho*harmonicMass (P i)) :
    (∑ f ∈ (selections P m).filter E,(selectionProduct f : ℝ)⁻¹) ≤ rho*selectionMass P m := by
  rw [singleton_event_sum P m i hi E]
  calc
    _ ≤ ∑ f ∈ selections P (eraseMultiplicity m i),(selectionProduct f : ℝ)⁻¹*(rho*harmonicMass (P i)) := by
      apply Finset.sum_le_sum
      intro f hf
      exact mul_le_mul_of_nonneg_left (h f hf) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = rho*selectionMass P m := by
      rw [← Finset.sum_mul,singleton_total_mass P m i hi]
      change selectionMass P (eraseMultiplicity m i)*(rho*harmonicMass (P i)) = _
      ring

end ErdosVarianceWeighted

end

end Erdos970

end OAI
