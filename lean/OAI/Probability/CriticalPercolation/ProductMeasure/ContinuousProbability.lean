import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BoundaryCount

namespace OAI

section
section CurrentModule5
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*} [Fintype E]

lemma continuous_probability (F : Set E → Prop) :
    Continuous (fun p : ℝ => probability p F) := by
  unfold probability expect
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  exact continuous_iff_continuousAt.mpr (fun p => (hasDerivAt_density p ω).continuousAt)

lemma probability_monotoneOn (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) :
    MonotoneOn (fun p : ℝ => probability p F) (Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (continuous_probability F).continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_probability hp F hF).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_probability hp F hF).deriv]
    exact Finset.sum_nonneg fun e _ => probability_nonneg ⟨hp.1.le,hp.2.le⟩ _

variable (G : BondGraph V E)

omit [Fintype E] in
lemma boundary_event_mono (o : V) (R : Set V) (e : E) {ω ω' : Set E}
    (h : ω ⊆ ω') :
    boundaryReach G R (delete (G.openGraph ω) R) o e →
      boundaryReach G R (delete (G.openGraph ω') R) o e := by
  rintro ⟨x,y,he,hx,hy,hox⟩
  have hdel : delete (G.openGraph ω) R ≤ delete (G.openGraph ω') R := by
    intro a b hh
    exact ⟨G.openGraph_mono h hh.1,hh.2⟩
  exact ⟨x,y,he,hx,hy,hox.mono hdel⟩

lemma boundaryFlux_eq_sum (p : ℝ) (o : V) (R : Set V) :
    boundaryFlux G p o R = p * ∑ e, probability p
      (fun ω => boundaryReach G R (delete (G.openGraph ω) R) o e) := by
  simp only [boundaryFlux,boundaryCount,expect_sum,probability]

lemma boundaryFlux_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (o : V) (R : Set V) :
    0 ≤ boundaryFlux G p o R := by
  rw [boundaryFlux_eq_sum]
  exact mul_nonneg hp.1 (Finset.sum_nonneg fun e _ => probability_nonneg hp _)

lemma boundaryFlux_monotoneOn (o : V) (R : Set V) :
    MonotoneOn (fun p : ℝ => boundaryFlux G p o R) (Icc 0 1) := by
  intro p hp q hq hpq
  simp only [boundaryFlux_eq_sum]
  apply mul_le_mul hpq _ (Finset.sum_nonneg fun e _ => probability_nonneg hp _) hq.1
  apply Finset.sum_le_sum
  intro e _
  exact probability_monotoneOn _ (fun _ _ h => boundary_event_mono G o R e h) hp hq hpq

theorem uniform_escape_lower_bound {p q : ℝ} (hp : p ∈ Ioo 0 1)
    (hpq : p < q) (hq : q < 1) (o : V) (T : Set V)
    (hflux : ∀ R : Set V, T ⊆ R → o ∉ R → 1 ≤ boundaryFlux G p o R) :
    (q-p)/(1+q-p) ≤ probability q (reachesTarget G o T) := by
  let F := reachesTarget G o T
  have hF : ∀ s t, s ⊆ t → F s → F t := fun _ _ h => reachesTarget_mono G o T h
  have hq0 : 0 < q := hp.1.trans hpq
  obtain ⟨c,hc,hderiv⟩ := exists_deriv_eq_slope
    (fun r => probability r F) hpq (continuous_probability F).continuousOn
    (fun r hr => (hasDerivAt_probability ⟨hp.1.trans hr.1,hr.2.trans hq⟩ F hF
      ).differentiableAt.differentiableWithinAt)
  have hc01 : c ∈ Ioo 0 1 := ⟨hp.1.trans hc.1,hc.2.trans hq⟩
  have hd := differential_inequality G hc01 o T (a := 1) (fun R hTR ho =>
    (hflux R hTR ho).trans (boundaryFlux_monotoneOn G o R
      ⟨hp.1.le,hp.2.le⟩ ⟨hc01.1.le,hc01.2.le⟩ hc.1.le))
  have hmono := probability_monotoneOn F hF ⟨hc01.1.le,hc01.2.le⟩
    ⟨hq0.le,hq.le⟩ hc.2.le
  have hdnonneg : 0 ≤ deriv (fun r => probability r F) c := by
    rw [(hasDerivAt_probability hc01 F hF).deriv]
    exact Finset.sum_nonneg fun e _ => probability_nonneg ⟨hc01.1.le,hc01.2.le⟩ _
  have hfactor : c*(1-c) ≤ 1 := by nlinarith [sq_nonneg c]
  have hds : c*(1-c)*deriv (fun r => probability r F) c ≤
      deriv (fun r => probability r F) c := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hdnonneg
  have hlow : 1-probability q F ≤ deriv (fun r => probability r F) c := by
    change 1*(1-probability c F) ≤ _ at hd
    linarith
  have hdiff := mul_le_mul_of_nonneg_right hlow (sub_pos.mpr hpq).le
  have heq := (eq_div_iff (sub_pos.mpr hpq).ne').mp hderiv
  have hnonneg := probability_nonneg ⟨hp.1.le,hp.2.le⟩ F
  apply (div_le_iff₀ (by linarith : 0 < 1+q-p)).mpr
  change q-p ≤ probability q F * (1+q-p)
  nlinarith

end CriticalPercolation.Sharpness
end
end CurrentModule5

end

end OAI
