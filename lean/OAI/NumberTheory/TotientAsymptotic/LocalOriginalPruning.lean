import OAI.NumberTheory.TotientAsymptotic.LocalOriginalExceptions

namespace OAI

/-! The two direct exceptions and the surviving comparison case cover
the actual original-head bad candidates. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem local_original_count_of_regular {c : ℝ} (hc : 0 < c)
    (d q : ℕ) (hd : 0 < d) (hqpos : 0 < q) (hq : q.totient=d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∀ F : ℕ → ℕ,let R := localOriginalBad x c d L H
        Set.InjOn F (R : Set ℕ) →
        (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
          largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
        ((localWitnessRegular R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ)) →
      ((localOriginalBad x c d L H).card:ℝ) ≤
        x/Real.log x*(rho^(m x)+2*(B x)^(-4:ℝ)) := by
  filter_upwards [local_original_exception_data hc d q hd hqpos hq L] with H hH
  filter_upwards [hH] with x hx
  intro hregular
  obtain ⟨F,hinj,hF,hn,hs⟩ := hx
  have hr := hregular F hinj hF
  have hpart : ((localOriginalBad x c d L H).card:ℝ) ≤
      ((localWitnessNonnormal (localOriginalBad x c d L H) F (m x)).card:ℝ)+
      ((localWitnessSquare (localOriginalBad x c d L H) F (m x)).card:ℝ)+
      ((localWitnessRegular (localOriginalBad x c d L H) F (m x)).card:ℝ) := by
    exact_mod_cast local_residual_card_partition (localOriginalBad x c d L H) F (m x)
  nlinarith only [hpart,hn,hs,hr]

end TotientAsymptotic

end

end OAI
