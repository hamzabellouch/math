import OAI.Analysis.Laughlin.Charge.Sectors
import OAI.Analysis.Laughlin.Pair.NormalOrder

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

theorem annihilate_norm_sum (Q : ℕ) (n : ℤ) (x : Space Q) (hx : FockDegree Q n x) :
    (∑ i : Fin (Q+1), occupationNormSq Q (annihilate i x)) =
      (n : ℝ)*occupationNormSq Q x := by
  simp_rw [annihilate_normSq]
  rw [Finset.sum_comm]
  unfold occupationNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hs : (∑ i : Fin (Q+1), if i ∈ A then ‖(occupationBasis Q).repr x A‖^2 else 0) =
      (A.card : ℝ)*‖(occupationBasis Q).repr x A‖^2 := by
    rw [← Finset.sum_filter]
    simp
  rw [hs]
  by_cases hcard : (A.card : ℤ)=n
  · rw [← hcard]
    norm_cast
  · rw [hx A hcard]
    simp

theorem sourcePairEnd_annihilate (Q p : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    sourcePairEnd Q p (annihilate i x)=annihilate i (sourcePairEnd Q p x) :=
  LinearMap.congr_fun (pairEnd_annihilate_commute Q _ i) x

theorem annihilate_energy_sum (Q : ℕ) (n : ℤ) (x : Space Q) (hx : FockDegree Q n x) :
    (∑ i : Fin (Q+1), sourceFockEnergy Q (annihilate i x)) =
      ((n : ℝ)-2)*sourceFockEnergy Q x := by
  unfold sourceFockEnergy
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [sourcePairEnd_annihilate]
  have hd : FockDegree Q (n-2) (sourcePairEnd Q p x) := fockDegree_pair hx _
  simpa using annihilate_norm_sum Q (n-2) (sourcePairEnd Q p x) hd

theorem annihilator_mem_sector (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ particleSector Q (n+1)) (i : Fin (Q+1)) :
    annihilator Q i x ∈ particleSector Q n := by
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective x
  have hv : FockDegree Q (n+1) v := by
    intro A hA
    exact hx A (by exact_mod_cast hA)
  simp only [annihilator,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  intro A hA
  change (occupationBasis Q).repr (annihilate i v) A=0
  exact fockDegree_annihilate hv i A (by omega)

theorem annihilator_norm_sum (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ particleSector Q n) :
    (∑ i : Fin (Q+1), ‖annihilator Q i x‖^2)=(n : ℝ)*‖x‖^2 := by
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective x
  have hv : FockDegree Q n v := by
    intro A hA
    exact hx A (by exact_mod_cast hA)
  simp only [annihilator,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply,occupationEuclidean_norm]
  simpa using annihilate_norm_sum Q n v hv

theorem annihilator_energy_sum (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ particleSector Q (n+1)) :
    (∑ i : Fin (Q+1), energy Q (annihilator Q i x))=((n : ℝ)-1)*energy Q x := by
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective x
  have hv : FockDegree Q (n+1) v := by
    intro A hA
    exact hx A (by exact_mod_cast hA)
  simp only [annihilator,energy,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  have h := annihilate_energy_sum Q (n+1) v hv
  push_cast at h
  convert h using 1
  congr 1
  ring

end Laughlin.Charge

end OAI
