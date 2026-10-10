import OAI.NumberTheory.Jacobsthal.Paths.CanonicalWordPrefix

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

theorem rawWord_first_prefix_law (w : List Bool) : ∀ a b (past : RawHistory a) (z : OddCost),
    rawLast a past=embedOdd z →
    (rawMarkedWordKernel a (w++[b]) past).map (wordFirstPrefix a w b)=canonicalWordFirstPrefix a w b past := by
  induction w with
  | nil =>
    intro a b past z hz
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (wordFirstPrefix_measurable a [] b)]
    change (∫⁻ t : RawCycleWordTrace a [b].length, F (wordFirstPrefix a [] b t)
      ∂rawMarkedWordKernel a [b] past)=_
    rw [rawMarkedWord_cons_lintegral a b [] past (F := fun t => F (wordFirstPrefix a [] b t))
      (hF.comp (wordFirstPrefix_measurable a [] b))]
    change (∫⁻ r : RawReturnTrace a, ∫⁻ _t, F (@Sigma.mk ℕ RawHistory (a+1) (rawReturnFirstPrefix a r))
      ∂Measure.dirac r.2 ∂rawBranchReturnKernel a b past)=_
    simp only [lintegral_const,measure_univ,mul_one]
    have hG : Measurable (fun h : RawHistory (a+1) => F (@Sigma.mk ℕ RawHistory (a+1) h)) :=
      hF.comp (measurableSigmaMk (a+1))
    rw [← lintegral_map (g := rawReturnFirstPrefix a) hG (rawReturnFirstPrefix_measurable a),
      rawBranchReturn_first_prefix a b past z hz,canonicalWordFirstPrefix,
      Kernel.map_apply _ (measurableSigmaMk (a+1)),lintegral_map hF (measurableSigmaMk (a+1)),Kernel.restrict_apply]
  | cons c w ih =>
    intro a b past z hz
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (wordFirstPrefix_measurable a (c::w) b)]
    change (∫⁻ t : RawCycleWordTrace a (c::(w++[b])).length, F (wordFirstPrefix a (c::w) b t)
      ∂rawMarkedWordKernel a (c::(w++[b])) past)=_
    rw [rawMarkedWord_cons_lintegral a c (w++[b]) past (F := fun t => F (wordFirstPrefix a (c::w) b t))
      (hF.comp (wordFirstPrefix_measurable a (c::w) b)),canonicalWordFirstPrefix,
      Kernel.lintegral_comp _ _ _ hF]
    apply lintegral_congr_ae
    filter_upwards [rawBranchReturn_endpoint_supported a c past] with r hr
    change (∫⁻ t, F (wordFirstPrefix (a+2*(r.1+1)) w b t)
      ∂rawMarkedWordKernel (a+2*(r.1+1)) (w++[b]) r.2)=
        ∫⁻ q, F q ∂canonicalWordFirstPrefix (a+2*(r.1+1)) w b r.2
    rw [← lintegral_map (g := wordFirstPrefix (a+2*(r.1+1)) w b) hF (wordFirstPrefix_measurable _ w b),
      ih _ b r.2 (decodeReturnedOdd (rawReturnSignature a r).2.2) hr]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

noncomputable def pairHitTest (a k b : ℕ) (hab : a+2*k+1 ≤ b) (v H : ℝ) : Set (RawHistory b) :=
  {h | h ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩ ∈ regenerationSet ∧
    firstArrivalMark (h ⟨a+2*k+1,Finset.mem_Iic.mpr hab⟩)=true ∧
    (h ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩).2 ∈ Icc v (v+H)}

lemma pairHitTest_measurable (a k b : ℕ) (hab : a+2*k+1 ≤ b) (v H : ℝ) :
    MeasurableSet (pairHitTest a k b hab v H) :=
  (regenerationSet_measurable.preimage (measurable_pi_apply _)).inter
    (((firstArrivalMark_measurable.comp (measurable_pi_apply _)) (measurableSet_singleton true)).inter
      (measurableSet_Icc.preimage (measurable_snd.comp (measurable_pi_apply _))))

lemma pairHitTest_prefix {a k b c : ℕ} (hab : a+2*k+1 ≤ b) (hbc : b ≤ c) (v H : ℝ) :
    rawPrefix hbc ⁻¹' pairHitTest a k b hab v H=pairHitTest a k c (hab.trans hbc) v H := rfl

noncomputable def noPairHits (a m b : ℕ) (hab : a+2*m ≤ b) (v H : ℝ) : Set (RawHistory b) :=
  {h | ∀ k : Fin m, h ∉ pairHitTest a k.1 b (by have hk:=k.2; omega) v H}

lemma noPairHits_measurable (a m b : ℕ) (hab : a+2*m ≤ b) (v H : ℝ) :
    MeasurableSet (noPairHits a m b hab v H) := by
  unfold noPairHits
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (pairHitTest_measurable a k.1 b (by have hk:=k.2; omega) v H).compl

lemma noPairHits_prefix {a m b c : ℕ} (hab : a+2*m ≤ b) (hbc : b ≤ c) (v H : ℝ) :
    rawPrefix hbc ⁻¹' noPairHits a m b hab v H=noPairHits a m c (hab.trans hbc) v H := rfl

lemma noPairHits_zero (a b : ℕ) (hab : a+2*0 ≤ b) (v H : ℝ) :
    noPairHits a 0 b hab v H=univ := by
  ext h
  simp [noPairHits]

lemma noPairHits_succ (a n b : ℕ) (hab : a+2*(n+1) ≤ b) (v H : ℝ) :
    noPairHits a (n+1) b hab v H =
      noPairHits a n b (by omega) v H ∩ (pairHitTest a n b (by omega) v H)ᶜ := by
  ext h
  change (∀ k : Fin (n+1), h ∉ pairHitTest a k.1 b _ v H) ↔
    (∀ k : Fin n, h ∉ pairHitTest a k.1 b _ v H) ∧ h ∉ pairHitTest a n b _ v H
  constructor
  · intro hh
    exact ⟨fun k => hh k.castSucc,hh (Fin.last n)⟩
  · rintro ⟨hh,hn⟩ k
    by_cases hk : k.1 < n
    · exact hh ⟨k.1,hk⟩
    · have he : k.1=n := by have := k.2; omega
      have hkLast : k=Fin.last n := Fin.ext he
      subst k
      exact hn

noncomputable def firstPairHitEvent (a n b : ℕ) (hab : a+2*n+1 ≤ b) (v H : ℝ) : Set (RawHistory b) :=
  noPairHits a n b (by omega) v H ∩ pairHitTest a n b hab v H

lemma firstPairHitEvent_measurable (a n b : ℕ) (hab : a+2*n+1 ≤ b) (v H : ℝ) :
    MeasurableSet (firstPairHitEvent a n b hab v H) :=
  (noPairHits_measurable a n b (by omega) v H).inter (pairHitTest_measurable a n b hab v H)

lemma firstPairHitEvent_prefix {a n b c : ℕ} (hab : a+2*n+1 ≤ b) (hbc : b ≤ c) (v H : ℝ) :
    rawPrefix hbc ⁻¹' firstPairHitEvent a n b hab v H=firstPairHitEvent a n c (hab.trans hbc) v H := rfl

lemma firstPairHitEvent_disjoint {a n m b : ℕ} (hn : a+2*n+1 ≤ b) (hm : a+2*m+1 ≤ b)
    (hnm : n ≠ m) (v H : ℝ) : Disjoint (firstPairHitEvent a n b hn v H) (firstPairHitEvent a m b hm v H) := by
  apply disjoint_left.mpr
  intro h hN hM
  obtain hlt | hgt := lt_or_gt_of_ne hnm
  · exact (hM.1 ⟨n,hlt⟩) hN.2
  · exact (hN.1 ⟨m,hgt⟩) hM.2

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
