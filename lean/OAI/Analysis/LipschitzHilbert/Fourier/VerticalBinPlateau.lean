import OAI.Analysis.LipschitzHilbert.Fourier.FiniteVerticalBins

namespace OAI

/-! A fixed enlarged vertical cutoff equals one on every bin profile.
The finite bin partition is exact throughout the prescribed annulus. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def verticalBinPlateauReal (x : ℝ) : ℝ :=
  Real.smoothTransition (x+2)*Real.smoothTransition (2-x)

theorem verticalBinPlateauReal_zero (x : ℝ) (hx : x≤-2 ∨ 2≤x) : verticalBinPlateauReal x=0 := by
  rcases hx with hx | hx
  · simp [verticalBinPlateauReal,Real.smoothTransition.zero_of_nonpos (show x+2≤0 by linarith)]
  · simp [verticalBinPlateauReal,Real.smoothTransition.zero_of_nonpos (show 2-x≤0 by linarith)]

def verticalBinPlateau : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => (verticalBinPlateauReal x : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
    intro x hx
    have hxx : x≤-2 ∨ 2≤x := by
      by_cases h : -2≤x
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hx2 => hx ⟨h,hx2⟩)))
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
    simp only [f,verticalBinPlateauReal_zero x hxx,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    change ContDiff ℝ (↑(⊤:ℕ∞)) verticalBinPlateauReal
    unfold verticalBinPlateauReal
    fun_prop)

theorem verticalBinPlateau_one (x : ℝ) (hx : |x|≤1) : verticalBinPlateau x=1 := by
  have hb := abs_le.mp hx
  change (verticalBinPlateauReal x:ℂ)=1
  simp [verticalBinPlateauReal,Real.smoothTransition.one_of_one_le (show 1≤x+2 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤2-x by linarith)]

theorem verticalBinPlateau_support (x : ℝ) (hx : verticalBinPlateau x≠0) : |x|≤2 := by
  by_contra h
  have ha : 2 < |x| := lt_of_not_ge h
  have hxx : x≤-2 ∨ 2≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at ha
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at ha
      exact Or.inr ha.le
  exact hx (by change (verticalBinPlateauReal x:ℂ)=0; rw [verticalBinPlateauReal_zero x hxx]; rfl)

theorem verticalBinPlateau_mul_profile (x : ℝ) :
    verticalBinPlateau x*verticalBinProfile x=verticalBinProfile x := by
  by_cases hx : verticalBinProfile x=0
  · simp only [hx,mul_zero]
  · rw [verticalBinPlateau_one x (verticalBinProfile_support x hx),one_mul]

theorem positiveBand_bin_partition (w W c C eta : ℝ) (hw : 0<w) (hW : 0<W) (hc : 0<c)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      (verticalBinWindow ⌈C*W/w⌉₊ W n eta)^2)=1 := by
  apply verticalBinWindow_sum_sq _ w W c C eta hw hW hlo hhi
  have he : 0<eta := pos_of_mul_pos_right (hc.trans_le hlo) hw.le
  rw [abs_of_pos (mul_pos hW he)]
  apply le_trans _ (Nat.le_ceil _)
  apply (le_div_iff₀ hw).mpr
  nlinarith [mul_le_mul_of_nonneg_left hhi hW.le]

end LipschitzHilbert.PacketRepresentation

end

end OAI
