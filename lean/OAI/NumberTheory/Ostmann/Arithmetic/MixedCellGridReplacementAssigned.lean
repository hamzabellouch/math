import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeProgression PrimeCellReplacement PrimeCellFreezing MixedCellJointReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedGridIntegerError (loI hiI ηI G Bφ Dφ : ℝ)
    (j : Fin (gridCount loI hiI ηI)) : ℝ :=
  Real.exp (-G)*(6*Bφ+2*Dφ*(gridPoint loI hiI ηI (j.val+1)-gridPoint loI hiI ηI j.val))

def mixedGridError (M : ℕ) (loI hiI ηI G Bφ Dφ : ℝ) (φ : ℝ → ℝ)
    (ε B : ℝ) (j : Fin (gridCount loI hiI ηI)) : ℝ :=
  (mixedGridIntegerError loI hiI ηI G Bφ Dφ j +
    (|IntegerCell.integerDensityMass M (gridPoint loI hiI ηI j.val)
        (gridPoint loI hiI ηI (j.val+1)) G φ|+
      mixedGridIntegerError loI hiI ηI G Bφ Dφ j)*(Fintype.card ι:ℝ)*ε)*B^Fintype.card ι

theorem exists_assigned_mixedCell_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
        (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
        (loI hiI ηI G Bφ Dφ : ℝ) (φ ψ : ℝ → ℝ) (lo hi η Z : ι → ℝ),
        loI ≤ hiI → ⌊Real.exp hiI⌋₊ ≤ NI →
        (∀ t, HasDerivAt φ (ψ t) t) → Continuous ψ →
        (∀ t ∈ Set.Icc loI hiI, |φ (t-G)| ≤ Bφ) →
        (∀ t ∈ Set.Icc loI hiI, |ψ (t-G)| ≤ Dφ) →
        (∀ i, L₀ ≤ lo i ∧ lo i ≤ hi i ∧ 0 < η i ∧ η i ≤ 1 ∧
          ⌊Real.exp (hi i)⌋₊ ≤ N i ∧ 0 < Z i ∧
          (M:ℝ) ≤ Real.exp (d*(lo i)^(1/3:ℝ))) →
        ∀ (j : MixedGridIndex loI hiI ηI lo hi η) (ε B : ℝ), 0 ≤ ε → 1 ≤ B →
          (∀ i, (K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
            (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹ ≤ ε) →
          (∀ i, |harmonicIntegral M (boxLower lo hi η j.2 i) (boxUpper lo hi η j.2 i)/Z i|+
            ((K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
              (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹) ≤ B) →
        ∀ F : ZMod M → (ι → (ZMod M)ˣ) → ℂ,
          ‖mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F-
            (mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val)
              (gridPoint loI hiI ηI (j.1.val+1)) G φ
              (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z:ℂ)*
              (∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ, F r u)‖ ≤
          mixedGridError (ι:=ι) M loI hiI ηI G Bφ Dφ φ ε B j.1*
            (∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ, ‖F r u‖) := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hprime⟩ := exists_assigned_joint_primeCell_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro ι _ _ NI N M _ loI hiI ηI G Bφ Dφ φ ψ lo hi η Z
    hI hNI hφ hψ hBφ hDφ hcell j ε B hε hB hE hbound F
  classical
  have hBφ0 : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ loI ⟨le_rfl,hI⟩)
  have hDφ0 : 0 ≤ Dφ := (abs_nonneg _).trans (hDφ loI ⟨le_rfl,hI⟩)
  have hl := gridPoint_mem (η:=ηI) hI j.1.isLt.le
  have hu := gridPoint_mem (η:=ηI) hI (show j.1.val+1 ≤ gridCount loI hiI ηI by omega)
  have horderI := gridPoint_mono (η:=ηI) hI (Nat.le_succ j.1.val)
  have hsub : Set.Icc (gridPoint loI hiI ηI j.1.val)
      (gridPoint loI hiI ηI (j.1.val+1)) ⊆ Set.Icc loI hiI :=
    fun _ ht => ⟨hl.1.trans ht.1,ht.2.trans hu.2⟩
  have hEI : 0 ≤ mixedGridIntegerError loI hiI ηI G Bφ Dφ j.1 := by
    unfold mixedGridIntegerError
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (mul_nonneg (by norm_num) hBφ0)
        (mul_nonneg (mul_nonneg (by norm_num) hDφ0) (sub_nonneg.mpr horderI)))
  have hInteger (r : ZMod M) := assignedIntegerResidueMass_error NI M r loI hiI ηI G φ ψ j.1 Bφ Dφ
    hI hBφ0 ((Nat.floor_mono (Real.exp_le_exp.mpr hu.2)).trans hNI) hφ hψ
    (fun t ht => hBφ t (hsub ht)) (fun t ht => hDφ t (hsub ht))
  have hProd : ‖∏ i, ((harmonicIntegral M (boxLower lo hi η j.2 i)
      (boxUpper lo hi η j.2 i)/Z i:ℝ):ℂ)‖ ≤ B^Fintype.card ι := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : ι, B := by
        apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        intro i _
        have hZi := (hcell i).2.2.2.2.2.1
        have hEi : 0 ≤ (K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
            (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹ := by positivity
        simp only [Complex.norm_real,Real.norm_eq_abs]
        linarith [hbound i]
      _ = _ := by simp
  have hJoint (r : ZMod M) := hprime ι N M lo hi η Z hcell j.2 ε B hε hB hE hbound (F r)
  have hh := mixed_sum_error
    (fun r : ZMod M => assignedIntegerResidueMass NI M r loI hiI ηI G φ j.1)
    (IntegerCell.integerDensityMass M (gridPoint loI hiI ηI j.1.val)
      (gridPoint loI hiI ηI (j.1.val+1)) G φ)
    (fun r => assignedJointComplexTestSum N M lo hi η Z j.2 (F r))
    (∏ i, ((harmonicIntegral M (boxLower lo hi η j.2 i) (boxUpper lo hi η j.2 i)/Z i:ℝ):ℂ)) F
    hEI (show 0 ≤ (Fintype.card ι:ℝ)*ε*B^Fintype.card ι by positivity)
    (show 0 ≤ B^Fintype.card ι by positivity) hInteger hProd hJoint
  rw [← mixedAssignedTestSum_eq_integer] at hh
  rw [mixedPrincipalMass,MixedCellIntegralFreezing.residue_mixedLogMass_eq M _ _ _ _ _ _ _
    horderI (box_order lo hi η (fun i => (hcell i).2.1) j.2)]
  simp only [Complex.ofReal_mul,Complex.ofReal_prod]
  convert hh using 1
  dsimp [mixedGridError]
  ring

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
