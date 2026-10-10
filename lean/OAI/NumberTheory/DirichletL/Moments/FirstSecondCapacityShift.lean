import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityLedger
import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm CenteredMomentSectorLocalization
local notation "O"=>ActualEisensteinCubic.O

lemma nominal_capacity_shift_identity (A m q c d R E j g w wo g₂ t₂ c₂ V:ℝ):
    let K₀:=2*A-c-d+R+E-m;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+wo+t₂+V;
    (A-c-w-c₂)-(m'+q')-(A-(m+q))=
      g+w-(d+K₀-j)-wo+g₂-t₂-c₂ := by dsimp;ring

lemma main_capacity_gain (D₀ c σ δ:ℝ)(hc:0≤c)(hδ:0≤δ)(hD: -δ≤D₀):
    mainGain D₀ c σ-D₀≤6*(σ/3)+δ := by
  have hh:max (D₀-c) 0≤D₀+δ:=max_le (by linarith) (by linarith)
  unfold mainGain
  linarith

lemma error_capacity_gain (D₀ c σ δ Z:ℝ)(p:O)(k:ℕ)
    (hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)(hD: -δ≤D₀)
    (hk:k=1 ∨ k=6 ∨ k=7)
    (hl:σ/6≤Real.logb Z (normValue p)):
    errorGain D₀ c σ Z p k+errorRemoval p Z k-D₀-errorMoving p Z k≤
      6*errorRemoval p Z k+δ := by
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hm:0≤errorMoving p Z k ∧ errorMoving p Z k≤errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl
    all_goals norm_num [errorMoving,errorRemoval]
    all_goals first | exact hp | constructor <;> linarith
  have hw:0≤errorRemoval p Z k:=hm.1.trans hm.2
  have he:σ+errorRemoval p Z k-errorMoving p Z k≤6*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:max (D₀-c-2*errorRemoval p Z k+errorMoving p Z k) 0≤D₀+δ:=
    max_le (by linarith) (by linarith)
  unfold errorGain
  linarith

theorem main_nominal_capacity_shift (A m q c d R E j σ δ g₂ t₂ c₂ V:ℝ)
    (hc:0≤c)(hδ:0≤δ)(hD: -δ≤d+(2*A-c-d+R+E-m)-j)
    (hcommon:g₂-t₂≤c₂):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let g:=mainGain D₀ c σ;
    let m':=2*(A-c)-j-g-g₂-V;
    let q':=q+R+E+t₂+V;
    (A-c-c₂)-(m'+q')≤A-(m+q)+6*(σ/3)+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (mainGain (d+(2*A-c-d+R+E-m)-j) c σ) 0 0 g₂ t₂ c₂ V
  have hg:=main_capacity_gain _ c σ δ hc hδ hD
  dsimp only at hi ⊢
  simp only [sub_zero,add_zero] at hi
  linarith

theorem error_nominal_capacity_shift (A m q c d R E j σ δ Z g₂ t₂ c₂ V:ℝ)
    (p:O)(k:ℕ)(hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)
    (hD: -δ≤d+(2*A-c-d+R+E-m)-j)(hcommon:g₂-t₂≤c₂)
    (hk:k=1 ∨ k=6 ∨ k=7)(hl:σ/6≤Real.logb Z (normValue p)):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let w:=errorRemoval p Z k;
    let wo:=errorMoving p Z k;
    let g:=errorGain D₀ c σ Z p k;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+2*wo+t₂+V;
    (A-c-w-c₂)-(m'+q')≤A-(m+q)+6*w+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (errorGain (d+(2*A-c-d+R+E-m)-j) c σ Z p k)
    (errorRemoval p Z k) (errorMoving p Z k) g₂ t₂ c₂ V
  have hg:=error_capacity_gain _ c σ δ Z p k hc hσ hδ hD hk hl
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hwo:0≤errorMoving p Z k:=by
    unfold errorMoving
    split_ifs <;> linarith
  dsimp only at hi ⊢
  linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
