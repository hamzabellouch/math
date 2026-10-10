import OAI.NumberTheory.SiegelZeros.Characters.UnconditionalPrimeBias
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ParameterChoices
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.SequenceParameters
import OAI.NumberTheory.SiegelZeros.Selection.EventualSelection

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W50

open Filter
open scoped Topology
open WeightedTorusJets WeightedTorusJets.W02 WeightedTorusJets.W48

theorem uniform_exclusion_of_actual_cutoff
    (hgeometry : ∀ (H N : ℕ), 2 ≤ H → H ≤ N → 18818 ≤ N →
      ∀ (d : ℤ) (a : ℂ), Squarefree d → d ≠ 1 → d ≠ 2 →
        ∀ ha : a ^ 2 = (d : ℂ), ActualCutoffSpanning H N d a ha) :
    UniformSiegelZeroExclusion := by
  classical
  by_contra failure
  obtain ⟨C, hC, hC4, hmassAll⟩ := W63.exists_good_mass_for_actual_zeros_normalized
  let H : ℕ := 86713344
  have hH : 2 ≤ H := by norm_num [H]
  obtain ⟨γ, hγ, hallow⟩ := ParameterChoices.choose_exponent_quotient C hC.le
  obtain ⟨CH, hCH, hmass⟩ := hmassAll H hH
  obtain ⟨z, hindex, hsmall, hq, hgap, hne, hHN, hqR, hN, hU, hratio⟩ :=
    genuine_contrary_sequence_with_parameters failure γ hγ H
  apply false_of_eventual_exists_pivot_master H (by simp [H]) γ C CH
    hγ hCH hallow (fun i => ((z i).q : ℕ)) (fun i => (z i).gap) hq hgap
  filter_upwards [hne, hN.eventually_ge_atTop (max H 18818),
    hU.eventually_ge_atTop 3] with i hi8 hiN hiU
  let : NeZero ((z i).q : ℕ) := ⟨(z i).q.ne_zero⟩
  have hiHN : H ≤ auxiliaryN γ ((z i).q : ℝ) := (le_max_left _ _).trans hiN
  have hiLarge : 18818 ≤ auxiliaryN γ ((z i).q : ℝ) :=
    (le_max_right _ _).trans hiN
  have himass := hmass ((z i).q : ℕ) (z i).q_ge_three (z i).χ
    (z i).primitive (z i).nonprincipal (z i).real_character
    (z i).β (auxiliaryU γ ((z i).q : ℝ)) (z i).beta_pos (z i).beta_lt_one
    (z i).zero hiU
  apply exists_actual_character_pivot_master (z i).q_ge_three hi8 (z i).χ
    (z i).primitive (z i).real_character (z i).nonprincipal
    H hH hiHN hiLarge C CH (z i).gap hC4
    (hgeometry H (auxiliaryN γ ((z i).q : ℝ)) hH hiHN hiLarge)
  simpa only [GenuineZero.gap, auxiliaryU, mul_div_assoc, mul_assoc] using himass

end SiegelZerosAwei.W50

end

end SiegelZeros

end OAI
