import OAI.NumberTheory.Jacobsthal.Paths.RawPhysicalHit

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

noncomputable def lastRawCycle : (a : ℕ) → (w : List Bool) → (b : Bool) →
    RawCycleWordTrace a (w++[b]).length → Σ t : ℕ, RawReturnTrace t
  | a, [], _b, r => ⟨a,packRawReturnTrace a r.1 r.2.1⟩
  | a, _c::w, b, r => lastRawCycle (a+2*(r.1+1)) w b r.2.2

lemma lastRawCycle_measurable (w : List Bool) : ∀ a b, Measurable (lastRawCycle a w b) := by
  induction w with
  | nil =>
    intro a b
    apply measurable_sigma_family
    intro n
    exact (measurableSigmaMk a).comp ((rawReturnTrace_mk_measurable a n).comp measurable_fst)
  | cons c w ih =>
    intro a b
    apply measurable_sigma_family
    intro n
    exact (ih (a+2*(n+1)) b).comp measurable_snd

lemma lastRawCycle_anchor_ge (w : List Bool) : ∀ a b r, a ≤ (lastRawCycle a w b r).1 := by
  induction w with
  | nil => intro a b r; exact le_rfl
  | cons c w ih =>
    intro a b r
    exact (by omega : a ≤ a+2*(r.1+1)).trans (ih _ b r.2.2)

lemma lastRawCycle_record (w : List Bool) : ∀ a b r,
    lastCycleRecord w b (rawCycleWordSignature a (w++[b]).length r)=
      rawReturnInputSignature (lastRawCycle a w b r).1 (lastRawCycle a w b r).2 := by
  induction w with
  | nil => intro a b r; rfl
  | cons c w ih => intro a b r; exact ih _ b r.2.2

noncomputable def rawEvenFinalCycle (a : ℕ) (r : RawEvenMarkedHitTrace a) : Σ t : ℕ, RawReturnTrace t :=
  let e := (a+1)+2*r.1
  let t := r.2.2
  lastRawCycle e (List.ofFn t.2.1) true t.2.2

lemma rawEvenFinalCycle_measurable (a : ℕ) : Measurable (rawEvenFinalCycle a) := by
  apply measurable_sigma_family
  intro k
  have hm : Measurable (fun t : RawMarkedHitTrace ((a+1)+2*k) =>
      lastRawCycle ((a+1)+2*k) (List.ofFn t.2.1) true t.2.2) := by
    apply measurable_sigma_family
    intro n
    apply measurable_sigma_family
    intro f
    exact lastRawCycle_measurable (List.ofFn f) _ true
  exact hm.comp measurable_snd

lemma rawEvenFinalCycle_anchor_gt (a : ℕ) (r : RawEvenMarkedHitTrace a) :
    a < (rawEvenFinalCycle a r).1 := by
  have h := lastRawCycle_anchor_ge (List.ofFn r.2.2.2.1) ((a+1)+2*r.1) true r.2.2.2.2
  exact lt_of_lt_of_le (by omega : a < (a+1)+2*r.1) h

lemma rawEvenFinalCycle_record (a : ℕ) (r : RawEvenMarkedHitTrace a) :
    rawEvenHitRecord a r=rawReturnInputSignature (rawEvenFinalCycle a r).1 (rawEvenFinalCycle a r).2 :=
  lastRawCycle_record (List.ofFn r.2.2.2.1) ((a+1)+2*r.1) true r.2.2.2.2

theorem rawEvenHit_actual_visit (a : ℕ) (v H : ℝ) (h0 : RawHistory a) :
    ∀ᵐ r ∂rawEvenMarkedHitKernel a v H h0,
      ∃ (t n : ℕ) (h : RawHistory (t+2*(n+1))) (tau : EvenState),
        rawEvenFinalCycle a r=⟨t,⟨n,h⟩⟩ ∧ a < t ∧
        209/100 ≤ tau.1 ∧ tau.1 ≤ 213/100 ∧
        h ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩=
          (Sum.inl tau,(h ⟨t,Finset.mem_Iic.mpr (by omega)⟩).2+cost tau.1) ∧
        (h ⟨t,Finset.mem_Iic.mpr (by omega)⟩).2 ∈ Icc v (v+H) := by
  filter_upwards [rawEvenHit_ae_physical a v H h0] with r hr
  obtain ⟨tau,ht0,ht1,hFirst⟩ := physicalMarkedRecord_witness hr.1
  have hRecord := rawEvenFinalCycle_record a r
  have hAnchor := rawEvenFinalCycle_anchor_gt a r
  rcases he : rawEvenFinalCycle a r with ⟨t,n,h⟩
  rw [he] at hRecord hAnchor
  refine ⟨t,n,h,tau,rfl,hAnchor,ht0,ht1,?_,?_⟩
  · rw [hRecord] at hFirst
    exact hFirst
  · have hw := hr.2
    rw [hRecord] at hw
    exact hw

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

lemma gapAt_add_cost (r T t : ℝ) (ht : 0 < t) :
    gapAt r (T+cost t)=nextGap (gapAt r T) t := by
  rw [nextGap_eq_cost ht]
  unfold gapAt
  rw [neg_add,Real.exp_add]
  ring

theorem physical_record_slack {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    {c : CycleInputSignature} (hc : c ∈ physicalMarkedRecord)
    (hW : c.1 ∈ Icc (Real.log (r/b1)) (Real.log (r/b1)+Real.log (b1/(10*b0)))) :
    ∃ tau : EvenState, 209/100 ≤ tau.1 ∧ tau.1 ≤ 213/100 ∧
      recordFirst c=(Sum.inl tau,c.1+cost tau.1) ∧
      10*b0 ≤ gapAt r c.1 ∧ gapAt r c.1 ≤ b1 ∧
      10*b0/(313/100) ≤ nextExponent (gapAt r c.1) tau.1 ∧
      nextExponent (gapAt r c.1) tau.1 ≤ b1/(309/100) ∧
      2*b0 ≤ nextExponent (gapAt r c.1) tau.1 ∧
      nextExponent (gapAt r c.1) tau.1 ≤ b1/2 ∧
      6*b0 < gapAt r (recordFirst c).2 ∧
      gapAt r (recordFirst c).2 / nextExponent (gapAt r c.1) tau.1=tau.1 := by
  obtain ⟨tau,ht0,ht1,hF⟩ := physicalMarkedRecord_witness hc
  have hg := (marked_cost_window hr hb0 hb1 c.1).mpr hW
  have hs := marked_draw_slack hb0 hg.1 hg.2 ht0 ht1
  refine ⟨tau,ht0,ht1,hF,hg.1,hg.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,?_,?_⟩
  · rw [hF,gapAt_add_cost r c.1 tau.1 (by linarith)]
    exact hs.2.2.2.2.1
  · rw [hF,gapAt_add_cost r c.1 tau.1 (by linarith)]
    exact hs.2.2.2.2.2

theorem rawEvenHit_ae_geometric {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (a : ℕ) (h : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h,
      ∃ tau : EvenState, 209/100 ≤ tau.1 ∧ tau.1 ≤ 213/100 ∧
        recordFirst (rawEvenHitRecord a z)=(Sum.inl tau,(rawEvenHitRecord a z).1+cost tau.1) ∧
        10*b0 ≤ gapAt r (rawEvenHitRecord a z).1 ∧ gapAt r (rawEvenHitRecord a z).1 ≤ b1 ∧
        10*b0/(313/100) ≤ nextExponent (gapAt r (rawEvenHitRecord a z).1) tau.1 ∧
        nextExponent (gapAt r (rawEvenHitRecord a z).1) tau.1 ≤ b1/(309/100) ∧
        2*b0 ≤ nextExponent (gapAt r (rawEvenHitRecord a z).1) tau.1 ∧
        nextExponent (gapAt r (rawEvenHitRecord a z).1) tau.1 ≤ b1/2 ∧
        6*b0 < gapAt r (recordFirst (rawEvenHitRecord a z)).2 ∧
        gapAt r (recordFirst (rawEvenHitRecord a z)).2 /
          nextExponent (gapAt r (rawEvenHitRecord a z).1) tau.1=tau.1 := by
  filter_upwards [rawEvenHit_ae_physical a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h] with z hz
  exact physical_record_slack hr hb0 hb1 hz.1 hz.2

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
