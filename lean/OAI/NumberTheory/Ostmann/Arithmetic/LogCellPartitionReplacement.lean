import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionBoundary

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeProgression PrimeCellReplacement

theorem exists_assigned_residueMass_error_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi η : ℝ,
      L₀ ≤ lo → lo ≤ hi → 0 < η → η ≤ 1 → ∀ (N M : ℕ) [NeZero M] (Z : ℝ),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < Z → (M:ℝ) ≤ Real.exp (d*lo^(1/3:ℝ)) →
      ∀ j : Fin (gridCount lo hi η), ∀ a : ZMod M, IsUnit a →
      |assignedResidueMass N M a lo hi η Z j -
        harmonicIntegral M (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))/Z| ≤
        (K/Z)*Real.exp (-d*(gridPoint lo hi η j.val)^(1/3:ℝ)) +
          (Z*Real.exp (gridPoint lo hi η j.val))⁻¹ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_residueMass_error_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro lo hi η hlo horder hη hη1 N M _ Z hN hZ hmod j a ha
  have hl := gridPoint_mem (η:=η) horder j.isLt.le
  have hu := gridPoint_mem (η:=η) horder (show j.val+1≤gridCount lo hi η by omega)
  have hcell : gridPoint lo hi η j.val ≤ gridPoint lo hi η (j.val+1) :=
    gridPoint_mono horder (Nat.le_succ _)
  have hlen : gridPoint lo hi η (j.val+1)-gridPoint lo hi η j.val ≤ 1 := by
    rw [gridPoint_width]
    exact (gridStep_le horder hη).trans hη1
  have hcut : ⌊Real.exp (gridPoint lo hi η (j.val+1))⌋₊ ≤ N :=
    (Nat.floor_mono (Real.exp_le_exp.mpr hu.2)).trans hN
  have hmod' : (M:ℝ) ≤ Real.exp (d*(gridPoint lo hi η j.val)^(1/3:ℝ)) := by
    apply hmod.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith : 0≤lo) hl.1 (by norm_num)) hd.le
  have hc := hAP (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))
    (hlo.trans hl.1) hcell hlen N M a Z hcut (NeZero.pos M) ha hZ hmod'
  have hb := residueMass_assigned_error N M a lo hi η j hZ
  calc
    _ ≤ |assignedResidueMass N M a lo hi η Z j -
          residueMass N M a (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) Z| +
        |residueMass N M a (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) Z -
          harmonicIntegral M (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))/Z| :=
      abs_sub_le _ _ _
    _ ≤ (Z*Real.exp (gridPoint lo hi η j.val))⁻¹ +
        (K/Z)*Real.exp (-d*(gridPoint lo hi η j.val)^(1/3:ℝ)) :=
      add_le_add (by simpa only [abs_sub_comm] using hb) hc
    _ = _ := by ring

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
