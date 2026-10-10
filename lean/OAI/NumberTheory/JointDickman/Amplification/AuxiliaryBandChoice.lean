import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryBandCount

namespace OAI

/-! # Choosing the small power band with an arbitrarily small missing density -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem exists_auxiliary_power_band {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ β < d ∧
      ∀ᶠ N : ℕ in atTop,
        (((Ioc N (2*N)).filter fun n =>
          mrtPrimeAvoids (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)) n).card:ℝ)/N ≤ ε := by
  obtain ⟨C,M,hC,_hM,hbound⟩ := auxiliary_power_missing_count
  let R := max 1 (3*C/ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hmain : C/R ≤ ε/3 := by
    apply (div_le_iff₀ hR0).mpr
    have hh := (div_le_iff₀ hε).mp (show 3*C/ε ≤ R from le_max_right _ _)
    nlinarith
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt
    (3*Real.exp (2*(Real.log R+M))/ε) (by norm_num : (1:ℝ)<2)
  have htail : Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1) ≤ ε/3 := by
    have hp : (2:ℝ)^r ≤ 2^(2*r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hh := (div_lt_iff₀ hε).mp (hr.trans_le hp)
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^(2*r+1))).mpr
    nlinarith
  let β := min (d/2) (1/(8*((r:ℝ)+1)))
  have hβ : 0 < β := lt_min (by positivity) (by positivity)
  have hβd : β < d := (min_le_left _ _).trans_lt (by linarith)
  have hsmall : β*(4*r:ℕ)<1 := by
    have hb := min_le_right (d/2) (1/(8*((r:ℝ)+1)))
    change β ≤ _ at hb
    have hh := (le_div_iff₀ (by positivity : 0<8*((r:ℝ)+1))).mp hb
    push_cast
    nlinarith [show (0:ℝ)≤r by positivity]
  refine ⟨β/R,β,div_pos hβ hR0,div_le_self hβ.le hR,hβd,?_⟩
  filter_upwards [hbound R β hR hβ r hsmall (ε/3) (by positivity)] with N hN
  linarith

end JointDickman

end OAI
