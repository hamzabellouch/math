import OAI.NumberTheory.TotientAsymptotic.CofactorExceptions
import OAI.NumberTheory.TotientAsymptotic.ElementaryExceptions

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

lemma uncovered_values_subset {H : ℕ} (hPH : P H<H) (hP : 1≤P H) :
    ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
      uncoveredValues x H t ⊆
        (preimageExceptionValues x (extractedStructureCondition x (P H)) ∪ smallValues x) ∪
          (largeOmegaValues x ∪ cofactorExceptionValues x H) := by
  filter_upwards [canonical_tuple_coverage_eventually hPH hP,extracted_head_large,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hcover hhead hm
  intro t ht v hv
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hvt,hvφ⟩ := Finset.mem_filter.mp hv
  have hvpos := (Finset.mem_Icc.mp hvt).1
  have ht0 : 0≤t := by
    by_contra h
    have hz := Nat.floor_of_nonpos (lt_of_not_ge h).le
    have hh := (Finset.mem_Icc.mp hvt).2
    rw [hz] at hh
    omega
  have hvtR : (v : ℝ)≤t := (Nat.le_floor_iff ht0).mp (Finset.mem_Icc.mp hvt).2
  have hvx : v ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr
    ⟨hvpos,(Finset.mem_Icc.mp hvt).2.trans (Nat.floor_mono ht)⟩
  by_cases he : v ∈ preimageExceptionValues x (extractedStructureCondition x (P H))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  by_cases hsmall : v ∈ smallValues x
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hsmall)
  by_cases hω : v ∈ largeOmegaValues x
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hω)
  have hn := ell_spec hvφ
  have hs := (outside_preimageExceptions_iff hvx).mp he (ell v) hn.1 hn.2
  have hlow : x^(19/20 : ℝ) ≤ (v : ℝ) := by
    apply le_of_not_gt
    intro h
    exact hsmall (Finset.mem_Icc.mpr ⟨hvpos,Nat.le_floor h.le⟩)
  have hΩ : (v.primeFactorsList.length : ℝ) ≤ 20*B x := by
    apply le_of_not_gt
    intro h
    exact hω (Finset.mem_filter.mpr ⟨hvx,h⟩)
  have hL : 0<L x H := by unfold L; omega
  have hp := hhead H (ell v) hL hn.1 hs (hn.2.symm ▸ hlow) (hn.2.symm ▸ hΩ)
  by_cases ha : Real.exp (2*bandScale x (L x H))<Real.log (fordCofactor (ell v) (L x H+1))
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hvx,hvφ⟩,ell v,hn.1,hn.2,hs,hp,ha⟩))
  · exfalso
    apply hout
    rw [← hn.2]
    exact hcover t (ell v) hn.1 hs hp (le_of_not_gt ha)
      (hn.2.symm ▸ hvtR)

end TotientAsymptotic

end

end OAI
