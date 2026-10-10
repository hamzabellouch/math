import OAI.NumberTheory.Jacobsthal.Paths.FiniteBoxWordMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FirstGapCrossing
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ErdosSearchCount
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem first_gap_crossing {w ell S : ℝ} (hell : 0 ≤ ell) (z : Node)
    (hs : Valid z.side z.ratio) (ps : List ℕ) (ha : allowed w ell S z ps)
    (H : ℝ) (hstart : H < z.gap) (hend : (terminal w z ps).gap ≤ H) :
    ∃ pre p tail,ps=pre++p::tail ∧ H < (terminal w z pre).gap ∧
      (terminal w z (pre++[p])).gap ≤ H ∧ H/3 < (terminal w z (pre++[p])).gap := by
  induction ps generalizing z with
  | nil => exact False.elim (not_lt_of_ge hend hstart)
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (allowed_cons w ell S z p ps).mp ha
    by_cases hc : (step w z p).gap ≤ H
    · have hh := child_gap_third hell hs hp
      exact ⟨[],p,ps,rfl,hstart,hc,by change H/3 < (step w z p).gap; linarith⟩
    · obtain ⟨pre,q,tail,he,hpre,hend,hlo⟩ := ih (step w z p) (child_valid hs hp) ht (lt_of_not_ge hc) hend
      refine ⟨p::pre,q,tail,by rw [List.cons_append,he],hpre,?_,?_⟩
      · simpa only [List.cons_append,terminal_cons] using hend
      · simpa only [List.cons_append,terminal_cons] using hlo
end NumberTheoryLean.FirstGapCrossing



namespace NumberTheoryLean.SourceFirstCrossing
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership FirstGapCrossing
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem source_first_above {w ell S B theta : ℝ} (hB : 0 < B) (htheta : theta ≤ 1/2)
    (z : Node) (hs : 199/100 ≤ z.ratio) (hc : Consistent z) (hcut : z.cutoff=B)
    {p : ℕ} (hp : p ∈ nodeChildren w ell S z) : theta*B < (step w z p).gap := by
  have hcap := (Finset.mem_filter.mp hp).2.2.1
  have hx : primeExponent w p ≤ B := by
    change capGuard z.closed z.cutoff (primeExponent w p) at hcap
    rw [hcut] at hcap
    cases h : z.closed <;> simp [capGuard,h] at hcap
    · exact hcap.le
    · exact hcap
  have hgap : z.gap=z.ratio*B := by
    have he : B=z.gap/z.ratio := hcut.symm.trans hc
    have hh := (eq_div_iff (by linarith : z.ratio ≠ 0)).mp he
    nlinarith
  change theta*B < z.gap-primeExponent w p
  rw [hgap]
  nlinarith

theorem source_gap_crossing {w ell S B theta : ℝ} (hell : 0 ≤ ell) (hB : 0 < B)
    (htheta : theta ≤ 1/2) (z : Node) (hs : Valid z.side z.ratio)
    (h199 : 199/100 ≤ z.ratio) (hc : Consistent z) (hcut : z.cutoff=B)
    (ps : List ℕ) (ha : allowed w ell S z ps) (hend : (terminal w z ps).gap ≤ theta*B) :
    ∃ pre p tail,pre ≠ [] ∧ ps=pre++p::tail ∧ theta*B < (terminal w z pre).gap ∧
      (terminal w z (pre++[p])).gap ≤ theta*B ∧ theta*B/3 < (terminal w z (pre++[p])).gap := by
  have hg : z.gap=z.ratio*B := (SourceNodeCoordinates.node_gap_eq hs hc hcut).trans (mul_comm _ _)
  have hstart : theta*B < z.gap := by rw [hg]; nlinarith
  obtain ⟨pre,p,tail,he,hpre,hhi,hlo⟩ := first_gap_crossing hell z hs ps ha (theta*B) hstart hend
  refine ⟨pre,p,tail,?_,he,hpre,hhi,hlo⟩
  intro hn
  subst pre
  simp only [List.nil_append] at he hhi
  have hp := ((allowed_cons w ell S z p tail).mp (he ▸ ha)).1
  exact (not_lt_of_ge hhi) (source_first_above hB htheta z h199 hc hcut hp)
end NumberTheoryLean.SourceFirstCrossing


end Erdos970

end OAI
