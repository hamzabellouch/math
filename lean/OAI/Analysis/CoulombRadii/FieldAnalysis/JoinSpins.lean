import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.BlockIndex

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
def joinSpins (m k : ℕ) : Spins m × Spins k ≃ Spins (m+k) where
  toFun := fun s => Fin.addCases s.1 s.2
  invFun := fun s => (s ∘ Fin.castAdd k, s ∘ Fin.natAdd m)
  left_inv := by
    intro s
    ext i <;> simp
  right_inv := by
    intro s
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Function.comp_def]

lemma joinSpins_left (m k : ℕ) (s : Spins m) (t : Spins k) :
    (joinSpins m k (s,t)) ∘ Fin.castAdd k = s := by
  funext i
  simp [joinSpins, Function.comp_def]
lemma joinSpins_right (m k : ℕ) (s : Spins m) (t : Spins k) :
    (joinSpins m k (s,t)) ∘ Fin.natAdd m = t := by
  funext i
  simp [joinSpins, Function.comp_def]

lemma sum_joinSpins {m k : ℕ} (F : Spins (m+k) → ℝ) :
    (∑ s, F s) = ∑ s : Spins m, ∑ t : Spins k, F (joinSpins m k (s,t)) := by
  rw [← Equiv.sum_comp (joinSpins m k), Fintype.sum_prod_type]

lemma sum_configurationBlocks {m k : ℕ} (F : Fin (m+k) × Fin 3 → ℝ) :
    (∑ a, F a) = (∑ a : Fin m × Fin 3, F (Fin.castAdd k a.1,a.2)) +
      (∑ a : Fin k × Fin 3, F (Fin.natAdd m a.1,a.2)) := by
  simp only [Fintype.sum_prod_type]
  exact Fin.sum_univ_add _

lemma tensorValue_square_integral {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) :
    (∫ x, ‖tensorValue u v s x‖^2) =
      (∫ x, ‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, ‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
  rw [← (joinConfiguration_measurePreserving m k).integral_comp'
    (fun x => ‖tensorValue u v s x‖^2)]
  change (∫ z : Configuration m × Configuration k,
    ‖tensorValue u v s (joinConfiguration m k z)‖^2 ∂(volume.prod volume)) = _
  simp_rw [tensorValue_join, norm_mul, mul_pow]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Configuration m => ‖u.value (s ∘ Fin.castAdd k) x‖^2)
    (fun y : Configuration k => ‖v.value (s ∘ Fin.natAdd m) y‖^2)

lemma tensorGradient_square_integral_left {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin m × Fin 3) :
    (∫ x, ‖tensorGradient u v s (Fin.castAdd k a.1,a.2) x‖^2) =
      (∫ x, ‖u.gradient (s ∘ Fin.castAdd k) a x‖^2)*
        (∫ y, ‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
  rw [← (joinConfiguration_measurePreserving m k).integral_comp'
    (fun x => ‖tensorGradient u v s (Fin.castAdd k a.1,a.2) x‖^2)]
  change (∫ z : Configuration m × Configuration k,
    ‖tensorGradient u v s (Fin.castAdd k a.1,a.2) (joinConfiguration m k z)‖^2
      ∂(volume.prod volume)) = _
  simp_rw [tensorGradient_join_left, norm_mul, mul_pow]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Configuration m => ‖u.gradient (s ∘ Fin.castAdd k) a x‖^2)
    (fun y : Configuration k => ‖v.value (s ∘ Fin.natAdd m) y‖^2)

lemma tensorGradient_square_integral_right {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin k × Fin 3) :
    (∫ x, ‖tensorGradient u v s (Fin.natAdd m a.1,a.2) x‖^2) =
      (∫ x, ‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, ‖v.gradient (s ∘ Fin.natAdd m) a y‖^2) := by
  rw [← (joinConfiguration_measurePreserving m k).integral_comp'
    (fun x => ‖tensorGradient u v s (Fin.natAdd m a.1,a.2) x‖^2)]
  change (∫ z : Configuration m × Configuration k,
    ‖tensorGradient u v s (Fin.natAdd m a.1,a.2) (joinConfiguration m k z)‖^2
      ∂(volume.prod volume)) = _
  simp_rw [tensorGradient_join_right, norm_mul, mul_pow]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Configuration m => ‖u.value (s ∘ Fin.castAdd k) x‖^2)
    (fun y : Configuration k => ‖v.gradient (s ∘ Fin.natAdd m) a y‖^2)

lemma mass_tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    mass (u.tensor v) = mass u*mass v := by
  change (∑ s, ∫ x, ‖tensorValue u v s x‖^2) = _
  simp_rw [tensorValue_square_integral]
  rw [sum_joinSpins]
  simp only [joinSpins_left, joinSpins_right, mass, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma kinetic_tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    kinetic (u.tensor v) = kinetic u*mass v+mass u*kinetic v := by
  change (1/2:ℝ)*(∑ s, ∑ a, ∫ x, ‖tensorGradient u v s a x‖^2) = _
  simp_rw [sum_configurationBlocks, tensorGradient_square_integral_left,
    tensorGradient_square_integral_right]
  rw [sum_joinSpins]
  simp only [joinSpins_left, joinSpins_right]
  simp only [mass, kinetic, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.sum_mul_sum]
  ring
end Coulomb

open scoped Classical
namespace Coulomb
def blockHom (m k : ℕ) :
    (Equiv.Perm (Fin m) × Equiv.Perm (Fin k)) →* Equiv.Perm (Fin (m+k)) :=
  ((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).permCongrHom).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin m) (Fin k))

def blockGroup (m k : ℕ) : Subgroup (Equiv.Perm (Fin (m+k))) := (blockHom m k).range

lemma blockHom_left {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k)) (i : Fin m) :
    blockHom m k (p,q) (Fin.castAdd k i) = Fin.castAdd k (p i) := by
  change finSumFinEquiv ((Equiv.sumCongr p q) (finSumFinEquiv.symm (Fin.castAdd k i))) = _
  simp [← finSumFinEquiv_apply_left]

lemma blockHom_right {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k)) (i : Fin k) :
    blockHom m k (p,q) (Fin.natAdd m i) = Fin.natAdd m (q i) := by
  change finSumFinEquiv ((Equiv.sumCongr p q) (finSumFinEquiv.symm (Fin.natAdd m i))) = _
  simp [← finSumFinEquiv_apply_right]

lemma blockHom_sign {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k)) :
    (blockHom m k (p,q)).sign = p.sign*q.sign := by
  change (finSumFinEquiv.permCongr (Equiv.sumCongr p q)).sign = _
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

lemma blockHom_injective (m k : ℕ) : Function.Injective (blockHom m k) :=
  (finSumFinEquiv.permCongrHom.injective).comp Equiv.Perm.sumCongrHom_injective

lemma card_blockGroup (m k : ℕ) :
    Fintype.card (blockGroup m k) = Nat.factorial m*Nat.factorial k := by
  rw [show Fintype.card (blockGroup m k) =
      Fintype.card (Equiv.Perm (Fin m) × Equiv.Perm (Fin k)) from
    Fintype.card_eq.mpr ⟨(Equiv.ofInjective (blockHom m k) (blockHom_injective m k)).symm⟩]
  simp [Fintype.card_prod, Fintype.card_perm]

lemma mem_blockGroup_of_no_crossing {m k : ℕ} (r : Equiv.Perm (Fin (m+k)))
    (hr : ∀ i : Fin m, ∃ j : Fin m, r (Fin.castAdd k i) = Fin.castAdd k j) :
    r ∈ blockGroup m k := by
  let t : Equiv.Perm (Fin m ⊕ Fin k) := finSumFinEquiv.symm.permCongr r
  have ht : Set.MapsTo t (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    rcases hr i with ⟨j,hj⟩
    refine ⟨j, ?_⟩
    change Sum.inl j = finSumFinEquiv.symm (r (finSumFinEquiv (Sum.inl i)))
    rw [finSumFinEquiv_apply_left, hj]
    simp [← finSumFinEquiv_apply_left]
  rcases Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ht with ⟨pq,hpq⟩
  refine ⟨pq, ?_⟩
  apply finSumFinEquiv.symm.permCongr.injective
  change finSumFinEquiv.symm.permCongr
    (finSumFinEquiv.permCongr (Equiv.Perm.sumCongrHom (Fin m) (Fin k) pq)) = _
  rw [← Equiv.permCongr_symm, Equiv.symm_apply_apply]
  exact hpq

lemma exists_crossing_of_not_mem {m k : ℕ} (r : Equiv.Perm (Fin (m+k)))
    (hr : r ∉ blockGroup m k) :
    ∃ i : Fin m, ∃ j : Fin k, r (Fin.castAdd k i) = Fin.natAdd m j := by
  have hn : ¬ ∀ i : Fin m, ∃ j : Fin m, r (Fin.castAdd k i) = Fin.castAdd k j :=
    fun h => hr (mem_blockGroup_of_no_crossing r h)
  push Not at hn
  rcases hn with ⟨i,hi⟩
  refine ⟨i, ?_⟩
  have hcases := Fin.addCases (motive := fun z : Fin (m+k) =>
    (∃ j : Fin k, z = Fin.natAdd m j) ∨ ∃ j : Fin m, z = Fin.castAdd k j)
    (fun j => Or.inr ⟨j,rfl⟩) (fun j => Or.inl ⟨j,rfl⟩) (r (Fin.castAdd k i))
  rcases hcases with h|⟨j,hj⟩
  · exact h
  · exact (hi j hj).elim
end Coulomb

end

end OAI
