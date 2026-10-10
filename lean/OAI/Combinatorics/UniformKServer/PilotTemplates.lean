import Mathlib
import OAI.Combinatorics.UniformKServer.PilotEdits
import OAI.Combinatorics.UniformKServer.TierPilot

namespace OAI

                                     
section

/-! Actual admissible pilot templates; no drift/pilot premise is added to the
partition construction. The constants are independent of the finite law. -/
noncomputable section
namespace UniformKServer.PilotEdits
open PilotCompact

def smallGamma (σ L : ℝ) : ℝ := min (σ/64) (1/(1+L))

theorem smallGamma_pos (σ L : ℝ) (hσ : 0<σ) (hL : 0≤L) : 0<smallGamma σ L := by
  unfold smallGamma
  apply lt_min <;> positivity

def scaleShift (σ R L : ℝ) : ℕ := ⌈100*R/smallGamma σ L⌉₊

theorem shift_valid (σ R L : ℝ) (hσ : 0<σ) (hL : 0≤L) :
    100*R ≤ smallGamma σ L*(2:ℝ)^scaleShift σ R L := by
  have hg := smallGamma_pos σ L hσ hL
  have hc := Nat.le_ceil (100*R/smallGamma σ L)
  have hp : (scaleShift σ R L:ℝ)≤(2:ℝ)^scaleShift σ R L := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self) : scaleShift σ R L≤(2:ℕ)^scaleShift σ R L)
  have ht : 100*R/smallGamma σ L≤(2:ℝ)^scaleShift σ R L := hc.trans hp
  simpa only [mul_comm] using (div_le_iff₀ hg).mp ht

def template (σ R L : ℝ) (hσ : 0<σ) (hσ1 : σ≤1) (hR : 256≤R) (hL : 0≤L) : Template where
  sigma := σ
  R := R
  gamma := smallGamma σ L
  delta := 1/4112
  L := L
  shift := scaleShift σ R L
  sigma_pos := hσ
  sigma_le_one := hσ1
  R_large := hR
  L_nonneg := hL
  gamma_pos := smallGamma_pos σ L hσ hL
  gamma_sigma := min_le_left _ _
  gamma_L := min_le_right _ _
  delta_pos := by norm_num
  delta_small := le_rfl
  shift_large := shift_valid σ R L hσ hL

def heavyTemplate : Template := template 1 512 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def shortTemplate (P : TierPilot.Parameters) : Template :=
  template P.sigma 204800 8 P.sigma_pos P.sigma_le_one (by norm_num) (by norm_num)

theorem rate_nonneg (T : Template) : 0≤rate T := by
  have hσ := T.sigma_pos
  have hγ := T.gamma_pos
  have hδ := T.delta_pos
  have hL := T.L_nonneg
  unfold rate driftConstant localSlopeConstant
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  positivity

end UniformKServer.PilotEdits

end


end

end OAI
