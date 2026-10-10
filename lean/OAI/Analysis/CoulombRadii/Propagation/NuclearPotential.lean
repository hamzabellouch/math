import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add
import OAI.Analysis.CoulombRadii.FieldAnalysis.WedgeMultiplicity

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
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical

namespace Coulomb
def nuclearPotential {M n : ℕ} (S : Nuclei M) (x : Configuration n) : ℝ :=
  ∑ i, attraction S (position x i)
def pairPotential {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then coulombKernel (position x i-position x j) else 0

lemma nuclearPotential_permute {M n : ℕ} (S : Nuclei M) (p : Equiv.Perm (Fin n))
    (x : Configuration n) : nuclearPotential S (permute p x) = nuclearPotential S x := by
  simp only [nuclearPotential, position_permute]
  exact Equiv.sum_comp p (fun i => attraction S (position x i))

lemma coulombKernel_sub_comm (x y : Space) : coulombKernel (x-y) = coulombKernel (y-x) := by
  simp only [coulombKernel, norm_sub_rev]

lemma twice_pairPotential {n : ℕ} (x : Configuration n) :
    2*pairPotential x = ∑ i : Fin n, ∑ j : Fin n, coulombKernel (position x i-position x j) := by
  have H (i j : Fin n) : coulombKernel (position x i-position x j) =
      (if i < j then coulombKernel (position x i-position x j) else 0)+
      (if j < i then coulombKernel (position x j-position x i) else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [coulombKernel]
    · simp [h, not_lt_of_ge h.le, coulombKernel_sub_comm]
  have hs : pairPotential x = ∑ i : Fin n, ∑ j : Fin n,
      if j < i then coulombKernel (position x j-position x i) else 0 := by
    unfold pairPotential
    rw [Finset.sum_comm]
  calc
    2*pairPotential x = pairPotential x+pairPotential x := by ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then coulombKernel (position x i-position x j) else 0)+
         (if j < i then coulombKernel (position x j-position x i) else 0)) := by
      simp only [Finset.sum_add_distrib]
      change pairPotential x+pairPotential x = pairPotential x+_
      rw [hs]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (H i j).symm

lemma pairPotential_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    pairPotential (permute p x) = pairPotential x := by
  apply (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0))
  rw [twice_pairPotential, twice_pairPotential]
  simp_rw [position_permute]
  rw [Equiv.sum_comp p (fun i => ∑ j, coulombKernel (position x i-position x (p j)))]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp p (fun j => coulombKernel (position x i-position x j))

lemma nuclearEnergy_wedge_tensor {M m k : ℕ} (S : Nuclei M)
    (u : H1Vector m) (v : H1Vector k) (hu : Antisymmetric u) (hv : Antisymmetric v)
    (A B : Set Space) (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hAB : Disjoint A B) : nuclearEnergy S (u.wedge v) = nuclearEnergy S (u.tensor v) :=
  potentialEnergy_wedge u v hu hv A B hsu hsv hAB (nuclearPotential S)
    (nuclearPotential_permute S) ((u.tensor v).nuclear_integrable S)

lemma pairEnergy_wedge_tensor {m k : ℕ}
    (u : H1Vector m) (v : H1Vector k) (hu : Antisymmetric u) (hv : Antisymmetric v)
    (A B : Set Space) (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hAB : Disjoint A B) : pairEnergy (u.wedge v) = pairEnergy (u.tensor v) :=
  potentialEnergy_wedge u v hu hv A B hsu hsv hAB pairPotential
    pairPotential_permute (u.tensor v).pair_integrable

lemma nuclearPotential_join {M m k : ℕ} (S : Nuclei M)
    (x : Configuration m) (y : Configuration k) :
    nuclearPotential S (joinConfiguration m k (x,y)) = nuclearPotential S x+nuclearPotential S y := by
  simp [nuclearPotential, Fin.sum_univ_add, position_join_left, position_join_right]

def crossPotential {m k : ℕ} (x : Configuration m) (y : Configuration k) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin k, coulombKernel (position x i-position y j)

lemma pairPotential_join {m k : ℕ} (x : Configuration m) (y : Configuration k) :
    pairPotential (joinConfiguration m k (x,y)) = pairPotential x+pairPotential y+crossPotential x y := by
  have hll (i j : Fin m) : Fin.castAdd k i < Fin.castAdd k j ↔ i < j := Iff.rfl
  have hlr (i : Fin m) (j : Fin k) : Fin.castAdd k i < Fin.natAdd m j := by
    change i.val < m+j.val
    omega
  have hrl (i : Fin k) (j : Fin m) : ¬Fin.natAdd m i < Fin.castAdd k j := by
    change ¬m+i.val < j.val
    omega
  simp only [pairPotential, Fin.sum_univ_add,position_join_left,position_join_right,
    hll,Fin.natAdd_lt_natAdd_iff,hlr,hrl,
    ite_true,ite_false,Finset.sum_const_zero,add_zero,Finset.sum_add_distrib]
  unfold crossPotential
  ring
end Coulomb

end

end OAI
