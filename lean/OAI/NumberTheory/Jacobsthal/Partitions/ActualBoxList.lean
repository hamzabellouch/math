import OAI.NumberTheory.Jacobsthal.Estimates.LiteralSourceList
import OAI.NumberTheory.Jacobsthal.Sieve.ActualCofactorArithmetic

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxApplication
open NumberTheoryLean ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost ErdosInverseAlignment
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem actual_box_list_card (Clen aStar alpha xi cp : ℝ) (hClen : 0 ≤ Clen)
    (ha : 0 < aStar) (halpha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hcp : 0 < cp) :
    ∀ᶠ z : ℝ in atTop,∀ (m : Fin (binCount (sourceW z) z xi) → ℕ)
      (i j : Fin (binCount (sourceW z) z xi)),
      ((∑ k,m k : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
      ∀ a : ℕ → ℕ,
      z^alpha ≤ lower (sourceW z) z xi i →
      lower (sourceW z) z xi i ≤ z^((1 : ℝ)/100) →
      (∀ q ∈ cofactorChoices (actualBins z xi) m,∀ p ∈ actualBins z xi i,∀ u ∈ actualBins z xi j,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
      (sourceRationalList (actualBins z xi i) (fun p => (a p : ℤ)) (cofactorScale z xi m)
        (lower (sourceW z) z xi i) (sourceZ z) cp).card ≤ ⌈2/cp^2⌉₊ := by
  filter_upwards [uniform_literal_source_list Clen (xi/4) alpha cp hClen (by positivity) halpha hcp,
    source_span_geometry,source_cofactor_cell_data Clen xi 1 hClen hxi hxi1 zero_lt_one,
    source_sample_population xi 1 0 hxi hxi1,sourceW_tendsto_atTop.eventually_ge_atTop 2]
    with z hlist hspan hcof hpop hW
  intro m i j hm a hRlo hRhi hchild
  have hthetaLow := effectiveWidth_ge_quarter hspan.1 hspan.2.1 hxi hxi1 (hspan.2.2 xi hxi hxi1)
  have hthetaHigh := effectiveWidth_le hspan.1 hspan.2.1 hxi
  have hP := (hpop (lower (sourceW z) z xi i) (effectiveWidth (sourceW z) z xi)
    (bin_source_bounds hspan.1 hspan.2.1 hxi i).1 hthetaLow hthetaHigh).1
  have hU := (hpop (lower (sourceW z) z xi j) (effectiveWidth (sourceW z) z xi)
    (bin_source_bounds hspan.1 hspan.2.1 hxi j).1 hthetaLow hthetaHigh).1
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hP
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hU
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (hcof m hm).2.1
  have hqpos := ((hcof m hm).2.2.2 q hq).1
  have hpp := (bin_prime_in_source hspan.1 hspan.2.1 hxi i hp).1
  have hup := (bin_prime_in_source hspan.1 hspan.2.1 hxi j hu).1
  have hpq := parent_product_le_of_child_log (sourceY z) p q u (sourceW z) aStar
    hpp.pos hqpos hup.one_lt.le (by linarith) ha (hchild q hq p hp u hu)
  have hrange := actual_source_cofactor_inflation hspan.1 hspan.2.1 hxi Clen m hm q hq
  exact hlist.2 (cofactorScale z xi m) (lower (sourceW z) z xi i) (p : ℝ) (q : ℝ)
    (effectiveWidth (sourceW z) z xi) (fun p => (a p : ℤ))
    (by exact_mod_cast hpp.one_lt.le) (by exact_mod_cast hqpos) hpq hrange.1 hrange.2
    hRlo hRhi hthetaLow (hthetaHigh.trans hxi1)

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
