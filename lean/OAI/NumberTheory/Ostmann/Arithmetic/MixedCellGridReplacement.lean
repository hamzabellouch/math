import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementAssigned
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementSmooth

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeProgression PrimeCellReplacement PrimeCellFreezing MixedCellIntegralFreezing Characters.RationalHistory

theorem exists_mixed_grid_smooth_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
        (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
        (loI hiI ηI G Bφ Dφ : ℝ) (φ ψ : ℝ → ℝ) (lo hi η Z : ι → ℝ),
        loI ≤ hiI → 0 < ηI → ⌊Real.exp hiI⌋₊ ≤ NI →
        (∀ t, HasDerivAt φ (ψ t) t) → Continuous ψ →
        (∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G)) →
        (∀ t ∈ Set.Icc loI hiI, |φ (t-G)| ≤ Bφ) →
        (∀ t ∈ Set.Icc loI hiI, |ψ (t-G)| ≤ Dφ) →
        (∀ i, L₀ ≤ lo i ∧ lo i ≤ hi i ∧ 0 < η i ∧ η i ≤ 1 ∧
          ⌊Real.exp (hi i)⌋₊ ≤ N i ∧ 0 < Z i ∧
          (M:ℝ) ≤ Real.exp (d*(lo i)^(1/3:ℝ))) →
        ∀ ε B error : ℝ, 0 ≤ ε → 1 ≤ B → 0 ≤ error →
          (∀ (j : MixedGridIndex loI hiI ηI lo hi η) i,
            (K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
              (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹ ≤ ε) →
          (∀ (j : MixedGridIndex loI hiI ηI lo hi η) i,
            |harmonicIntegral M (boxLower lo hi η j.2 i) (boxUpper lo hi η j.2 i)/Z i|+
              ((K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
                (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹) ≤ B) →
          (∀ j : MixedGridIndex loI hiI ηI lo hi η,
            mixedGridError (ι:=ι) M loI hiI ηI G Bφ Dφ φ ε B j.1 ≤ error) →
        ∀ (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) (f : (Option ι → ℝ) → ℂ) (D mesh A : ℝ),
          0 ≤ D → 0 ≤ mesh → ηI ≤ mesh → (∀ i, η i ≤ mesh) →
          (∀ z∈logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
            DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i))) z) →
          (∀ z∈logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),∀ i,
            ‖deriv (fun t => f (Expr.logCurve (fun i => Real.exp (z i)) i t)) 0‖ ≤ D) →
          (∀ z∈logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
            ‖f (fun i => Real.exp (z i))‖ ≤ A) →
          ‖mixedSmoothTestSum NI N M loI hiI G φ lo hi Z F f-
            mixedPrincipalIntegral M loI hiI G φ lo hi Z f*
              ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,F r u‖ ≤
            (2*(((Fintype.card ι:ℝ)+1)*D*mesh)*mixedPrincipalMass M loI hiI G φ lo hi Z+
              (((Fintype.card ι:ℝ)+1)*D*mesh+A)*
                (Fintype.card (MixedGridIndex loI hiI ηI lo hi η)*error))*
              ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_assigned_mixedCell_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro ι _ _ NI N M _ loI hiI ηI G Bφ Dφ φ ψ lo hi η Z
    hI hηI hNI hφ hψ hφ0 hBφ hDφ hcell ε B error hε hB herror hE hbound herrorBound
    F f D mesh A hD hm hmeshI hmesh hf hderiv hA
  classical
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt
  have horder : ∀ i, lo i ≤ hi i := fun i => (hcell i).2.1
  have hlo : ∀ i, 0 < lo i := fun i => lt_of_lt_of_le (by linarith) (hcell i).1
  have hη : ∀ i, 0 < η i := fun i => (hcell i).2.2.1
  have hZ : ∀ i, 0 < Z i := fun i => (hcell i).2.2.2.2.2.1
  let v : ℝ := ((Fintype.card ι:ℝ)+1)*D*mesh
  let T : ℝ := ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖
  let mass : MixedGridIndex loI hiI ηI lo hi η → ℝ := fun j =>
    mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
      G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlocal (j : MixedGridIndex loI hiI ηI lo hi η) :
      ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-
        mixedPrincipalIntegral M (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
          G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z f*
          ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,F r u‖ ≤ (v*(2*mass j+error)+A*error)*T := by
    have hl := gridPoint_mem (η:=ηI) hI j.1.isLt.le
    have hu := gridPoint_mem (η:=ηI) hI (show j.1.val+1 ≤ gridCount loI hiI ηI by omega)
    have hsubI : Set.Icc (gridPoint loI hiI ηI j.1.val)
        (gridPoint loI hiI ηI (j.1.val+1)) ⊆ Set.Icc loI hiI :=
      fun _ ht => ⟨hl.1.trans ht.1,ht.2.trans hu.2⟩
    have hsub : logRectangle
        (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
        (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2)) ⊆
        logRectangle (Option.elim' loI lo) (Option.elim' hiI hi) := by
      intro z hz i hi'
      cases i with
      | none => exact hsubI (hz none (Set.mem_univ _))
      | some i =>
        exact ⟨(boxLower_ge lo hi η horder j.2 i).trans (hz (some i) (Set.mem_univ _)).1,
          (hz (some i) (Set.mem_univ _)).2.trans (boxUpper_le lo hi η horder j.2 i)⟩
    let base : ℝ × (ι → ℝ) := (gridPoint loI hiI ηI j.1.val,boxLower lo hi η j.2)
    have hbase : base∈mixedLogRectangle
        (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
        (boxLower lo hi η j.2) (boxUpper lo hi η j.2) :=
      ⟨⟨le_rfl,gridPoint_mono hI (Nat.le_succ _)⟩,
        fun i _ => ⟨le_rfl,box_order lo hi η horder j.2 i⟩⟩
    have hb := mixed_assigned_smooth_replacement_of_errors (error:=error)
      NI N loI hiI ηI G φ lo hi η Z j hφc (fun t ht => hφ0 t (hsubI ht)) hZ
      (fun i => (hlo i).trans_le (boxLower_ge lo hi η horder j.2 i)) F f hD hm
      ((gridPoint_width loI hiI ηI j.1.val).trans_le ((gridStep_le hI hηI).trans hmeshI))
      (fun i => (box_width_le lo hi η horder hη j.2 i).trans (hmesh i))
      (fun z hz => hf z (hsub hz)) (fun z hz => hderiv z (hsub hz)) hbase
    have he := hAP ι NI N M loI hiI ηI G Bφ Dφ φ ψ lo hi η Z
      hI hNI hφ hψ hBφ hDφ hcell j ε B hε hB (hE j) (hbound j) F
    have heAbs := hAP ι NI N M loI hiI ηI G Bφ Dφ φ ψ lo hi η Z
      hI hNI hφ hψ hBφ hDφ hcell j ε B hε hB (hE j) (hbound j) (fun r u => (‖F r u‖:ℂ))
    have he' := he.trans (mul_le_mul_of_nonneg_right (herrorBound j) hT0)
    have heAbs' : ‖mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j (fun r u => (‖F r u‖:ℂ))-
        (mass j:ℂ)*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,(‖F r u‖:ℂ)‖ ≤ error*T := by
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_norm] at heAbs
      exact heAbs.trans (mul_le_mul_of_nonneg_right (herrorBound j) hT0)
    have hAbase : ‖f (optionCoordinates (mixedExp base))‖ ≤ A := by
      simpa only [optionCoordinates_mixedExp] using
        hA _ (hsub ((optionCoordinates_mem_logRectangle _ _ _ _).mpr hbase))
    exact (hb he' heAbs').trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hAbase herror)) hT0)
  have hsum : (∑ j : MixedGridIndex loI hiI ηI lo hi η,(v*(2*mass j+error)+A*error)) =
      2*v*mixedPrincipalMass M loI hiI G φ lo hi Z+
        (v+A)*(Fintype.card (MixedGridIndex loI hiI ηI lo hi η)*error) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp only [← mul_assoc,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [show (∑ j : MixedGridIndex loI hiI ηI lo hi η,mass j)=mixedPrincipalMass M loI hiI G φ lo hi Z from
      (mixedPrincipalMass_eq_sum_boxes M loI hiI ηI G φ lo hi η Z hI horder hφc hlo).symm]
    ring
  rw [mixedSmoothTestSum_eq_sum_assigned NI N loI hiI ηI G φ lo hi η Z hI horder F f,
    mixedPrincipalIntegral_eq_sum_boxes M loI hiI ηI G φ lo hi η Z hI horder hφc hlo f
      (fun z hz => (hf z hz).continuousAt.continuousWithinAt),Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-
          mixedPrincipalIntegral M (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
            G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z f*
            ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,F r u‖ := norm_sum_le _ _
    _ ≤ ∑ j : MixedGridIndex loI hiI ηI lo hi η,(v*(2*mass j+error)+A*error)*T :=
      Finset.sum_le_sum fun j _ => hlocal j
    _ = _ := by rw [← Finset.sum_mul,hsum]

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
