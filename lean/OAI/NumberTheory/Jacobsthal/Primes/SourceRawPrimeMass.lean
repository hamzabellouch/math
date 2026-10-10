import OAI.NumberTheory.Jacobsthal.Estimates.SourceGuardedHardCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosInverseCells
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_raw_hard_prime_mass (alpha aStar eps tau Cmin : ℝ) (F : ℕ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
      ∀ Q : Finset ℚ,Q.card ≤ F →
        harmonicMass (rawHardPrimeUnion Q z R theta a qf Cs eps) ≤ tau*harmonicMass (primeBin R theta) := by
  let sigma := tau/(2*((F : ℝ)+1))
  have hsigma : 0 < sigma := by dsimp [sigma];positivity
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hcount⟩ :=
    source_guarded_hard_count alpha aStar eps sigma Cmin halpha ha heps hsigma
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hcount xi hxi hxib,eventually_gt_atTop (1 : ℝ)] with z hz hz1
  intro R theta a qf hq hRlo hthetal hthetau hQLarge hgeometry Q hQ
  have hR : 0 < R := (Real.rpow_pos_of_pos (by linarith : 0 < z) alpha).trans_le hRlo
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  have htheta1 : theta ≤ 1 := hthetau.trans (hxib.trans hxi01)
  have hcard := rawHardPrimeUnion_card Q z R theta a qf Cs eps sigma
    (fun r _ => hz R theta a qf hq hRlo hthetal hthetau hQLarge hgeometry r)
  have hm := harmonic_transfer_two (rawHardPrimeUnion Q z R theta a qf Cs eps) (primeBin R theta)
    (rawHardPrimeUnion_subset Q z R theta a qf Cs eps) R theta (sigma*(Q.card : ℝ)) hR htheta htheta1
    (by positivity) (fun p hp => ((mem_primeBin hR.le htheta p).mp hp).2) hcard
  have hbudget : 2*(sigma*(Q.card : ℝ)) ≤ tau := by
    have hQr : (Q.card : ℝ) ≤ (F : ℝ)+1 := by
      have hh : (Q.card : ℝ) ≤ F := by exact_mod_cast hQ
      linarith
    have hh := mul_le_mul_of_nonneg_left hQr (show 0 ≤ 2*sigma by positivity)
    have he : (2*sigma)*((F : ℝ)+1) = tau := by dsimp [sigma];field_simp
    nlinarith
  exact hm.trans (mul_le_mul_of_nonneg_right hbudget (harmonicMass_nonneg _))

end ErdosVarianceWeighted

end

end Erdos970

end OAI
