import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionTuples
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacementAlgebra

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeProgression PrimeCellReplacement
open scoped BigOperators

def assignedJointComplexTestSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) : ℂ :=
  ∑ p : AssignedPrimeTuple N lo hi η j,
    (∏ i, (((Z i * ((p i).val : ℝ))⁻¹ : ℝ) : ℂ)) *
      jointUnitTest F (fun i => ((p i).val : ZMod M))

theorem assignedJointComplexTestSum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) :
    assignedJointComplexTestSum N M lo hi η Z j F =
      ∑ u : ι → (ZMod M)ˣ,
        (∏ i, (assignedResidueMass (N i) M (u i) (lo i) (hi i) (η i) (Z i) (j i) : ℂ)) * F u := by
  classical
  have hpart := finite_product_prior_partition
    (fun i (p : {p : ℕ // p ∈ assignedPrimeSupport (N i) (lo i) (hi i) (η i) (j i)}) =>
      (p.val : ZMod M))
    (fun i (p : {p : ℕ // p ∈ assignedPrimeSupport (N i) (lo i) (hi i) (η i) (j i)}) =>
      (((Z i * (p.val : ℝ))⁻¹ : ℝ) : ℂ)) F
  change assignedJointComplexTestSum N M lo hi η Z j F = _ at hpart
  rw [hpart]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  apply Finset.prod_congr rfl
  intro i hi'
  rw [Finset.sum_coe_sort (assignedPrimeSupport (N i) (lo i) (hi i) (η i) (j i))
    (fun p : ℕ => if (u i : ZMod M) = (p : ZMod M) then
      (((Z i * (p : ℝ))⁻¹ : ℝ) : ℂ) else 0)]
  simp only [assignedResidueMass, Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases he : (p : ZMod M) = (u i : ZMod M)
  · simp [he]
  · simp [he, Ne.symm he]

theorem assignedJointComplexTestSum_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (main E : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) {ε B : ℝ} (hε : 0 ≤ ε) (hB : 1 ≤ B)
    (hE : ∀ i, E i ≤ ε) (hbound : ∀ i, |main i| + E i ≤ B)
    (hmass : ∀ i (u : (ZMod M)ˣ),
      |assignedResidueMass (N i) M u (lo i) (hi i) (η i) (Z i) (j i) - main i| ≤ E i) :
    ‖assignedJointComplexTestSum N M lo hi η Z j F -
      (∏ i, (main i : ℂ)) * ∑ u : ι → (ZMod M)ˣ, F u‖ ≤
      Fintype.card ι * ε * B ^ Fintype.card ι * ∑ u : ι → (ZMod M)ˣ, ‖F u‖ := by
  classical
  have hμ : ∀ i (u : (ZMod M)ˣ),
      ‖(assignedResidueMass (N i) M u (lo i) (hi i) (η i) (Z i) (j i) : ℂ)‖ ≤ B := by
    intro i u
    have ht := abs_add_le
      (assignedResidueMass (N i) M u (lo i) (hi i) (η i) (Z i) (j i) - main i) (main i)
    rw [sub_add_cancel] at ht
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith [hmass i u, hbound i]
  have hν : ∀ i (u : (ZMod M)ˣ), ‖(main i : ℂ)‖ ≤ B := by
    intro i u
    have he0 : 0 ≤ E i := (abs_nonneg _).trans (hmass i 1)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith [hbound i]
  have he : ∀ i (u : (ZMod M)ˣ),
      ‖(assignedResidueMass (N i) M u (lo i) (hi i) (η i) (Z i) (j i) : ℂ) - (main i : ℂ)‖ ≤ ε := by
    intro i u
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      (hmass i u).trans (hE i)
  have h := joint_product_test_error
    (fun i (u : (ZMod M)ˣ) =>
      (assignedResidueMass (N i) M u (lo i) (hi i) (η i) (Z i) (j i) : ℂ))
    (fun i (_ : (ZMod M)ˣ) => (main i : ℂ)) F hε hB hμ hν he
  rw [assignedJointComplexTestSum_eq]
  simpa only [Finset.mul_sum] using h

theorem exists_assigned_joint_primeCell_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) (M : ℕ) [NeZero M]
        (lo hi η Z : ι → ℝ),
        (∀ i, L₀ ≤ lo i ∧ lo i ≤ hi i ∧ 0 < η i ∧ η i ≤ 1 ∧
          ⌊Real.exp (hi i)⌋₊ ≤ N i ∧ 0 < Z i ∧
          (M : ℝ) ≤ Real.exp (d * (lo i) ^ (1 / 3 : ℝ))) →
        ∀ (j : GridBoxIndex lo hi η) (ε B : ℝ), 0 ≤ ε → 1 ≤ B →
          (∀ i, (K / Z i) * Real.exp (-d * (gridPoint (lo i) (hi i) (η i) (j i).val) ^ (1 / 3 : ℝ)) +
            (Z i*Real.exp (gridPoint (lo i) (hi i) (η i) (j i).val))⁻¹ ≤ ε) →
          (∀ i, |harmonicIntegral M (gridPoint (lo i) (hi i) (η i) (j i).val)
            (gridPoint (lo i) (hi i) (η i) ((j i).val+1)) / Z i| +
            ((K / Z i) * Real.exp (-d * (gridPoint (lo i) (hi i) (η i) (j i).val) ^ (1 / 3 : ℝ)) +
            (Z i*Real.exp (gridPoint (lo i) (hi i) (η i) (j i).val))⁻¹) ≤ B) →
          ∀ F : (ι → (ZMod M)ˣ) → ℂ,
            ‖assignedJointComplexTestSum N M lo hi η Z j F -
              (∏ i, ((harmonicIntegral M (gridPoint (lo i) (hi i) (η i) (j i).val)
                (gridPoint (lo i) (hi i) (η i) ((j i).val+1)) / Z i : ℝ) : ℂ)) *
                ∑ u : ι → (ZMod M)ˣ, F u‖ ≤
              Fintype.card ι * ε * B ^ Fintype.card ι *
                ∑ u : ι → (ZMod M)ˣ, ‖F u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,h⟩ := exists_assigned_residueMass_error_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro ι _ _ N M _ lo hi η Z hcell j ε B hε hB hE hbound F
  apply assignedJointComplexTestSum_error N M lo hi η Z j
    (fun i => harmonicIntegral M (gridPoint (lo i) (hi i) (η i) (j i).val)
      (gridPoint (lo i) (hi i) (η i) ((j i).val+1)) / Z i)
    (fun i => (K / Z i) * Real.exp (-d * (gridPoint (lo i) (hi i) (η i) (j i).val) ^ (1 / 3 : ℝ)) +
      (Z i*Real.exp (gridPoint (lo i) (hi i) (η i) (j i).val))⁻¹) F hε hB hE hbound
  intro i u
  obtain ⟨hlo,hlohi,hη,hη1,hN,hZ,hmod⟩ := hcell i
  exact h (lo i) (hi i) (η i) hlo hlohi hη hη1 (N i) M (Z i) hN hZ hmod (j i) u u.isUnit

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
