import Mathlib
import OAI.Probability.SKValue.Equations.ForcedGenerator
import OAI.Probability.SKValue.Evolution.HigherPDE

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
lemma BoundedJoint.at_continuous {T:ℝ} {F:ℝ → ℝ → ℝ} (h:BoundedJoint T F) (x:ℝ):
    ContinuousOn (fun t ↦ F t x) (Icc (0:ℝ) T) :=
  h.continuous.comp (continuousOn_id.prodMk continuousOn_const)
    ((mapsTo_id _).prodMk (mapsTo_univ (fun _ ↦ x) _))
lemma BoundedJoint.slice {T:ℝ} {F:ℝ → ℝ → ℝ} (h:BoundedJoint T F) {t:ℝ}
    (ht:t∈Icc (0:ℝ) T):Continuous (F t) := by
  obtain ⟨L,hl⟩:=h.spatial
  exact (hl t ht).continuous
lemma SmoothEvolution.polynomial_forced {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hT:0≤T) (hi:IntervalIntegrable γ volume 0 T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) (hn:∀t∈Icc (0:ℝ) T,0≤γ t)
    (hu:∀t∈Icc (0:ℝ) T,∀x,|deriv (V t) x|≤1) (e:JetExpr):
    ∃ K L:ℝ,ForcedTest T γ (fun t ↦ deriv (V t)) (polyJet V e)
      (polyJet V e.timeB) (polyJet V e.timeP) K L := by
  obtain ⟨A,hA,ha⟩:=(h.polyJet_joint e).bounded
  obtain ⟨B,hB,hb⟩:=(h.polyJet_joint (e.spatialIter 1)).bounded
  obtain ⟨C,hC,hc⟩:=(h.polyJet_joint (e.spatialIter 2)).bounded
  obtain ⟨D,hD,hd⟩:=(h.polyJet_joint (e.spatialIter 3)).bounded
  obtain ⟨E,hE,he⟩:=(h.polyJet_joint e.timeB).bounded
  obtain ⟨F,hF,hf⟩:=(h.polyJet_joint e.timeP).bounded
  obtain ⟨L,hL,hl⟩:=(h.polyJet_joint e.timeB).joint
  obtain ⟨M,hM,hm'⟩:=(h.polyJet_joint e.timeP).joint
  refine ⟨A+B+C+D+E+F,L+M,⟨by positivity,by positivity,hn,hm,?_,hu,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro t ht;exact ((h.slices t ht).jets.smooth.continuous).measurable
  · intro t ht;exact (h.polyJet_smooth e ht).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t ht x;linarith [ha t ht x]
  · intro t ht x
    have hh:=hb t ht x
    rw [←h.polyJet_iterated e ht 1,iteratedDeriv_one] at hh
    linarith
  · intro t ht x
    have hh:=hc t ht x
    rw [←h.polyJet_iterated e ht 2] at hh
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hh
    linarith
  · intro t ht x
    have hh:=hd t ht x
    rw [←h.polyJet_iterated e ht 3] at hh
    linarith
  · intro t ht;exact ((h.polyJet_joint e.timeB).slice ht).measurable
  · intro t ht;exact ((h.polyJet_joint e.timeP).slice ht).measurable
  · intro t ht x;linarith [he t ht x]
  · intro t ht x;linarith [hf t ht x]
  · intro t ht s hs x y
    exact (hl t ht s hs x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (by positivity))
  · intro t ht s hs x y
    exact (hm' t ht s hs x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL) (by positivity))
  · intro y
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using (h.polyJet_joint e.timeB).at_continuous y
  · intro y
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hT] using (h.polyJet_joint e.timeP).at_continuous y
  · intro a ha b hb x;exact h.polyJet_pde hi hm ha hb e x
end SKValue

end

end OAI
