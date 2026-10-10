import OAI.Probability.FreeIsing.Ising.CanonicalArtanh

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingCopyCanonicalStops
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

lemma projection_measurable_past (j : Bool) (t : ℝ≥0) :
    Measurable[ContinuousCopyBrownian.joinedFiltration t, filtration d t]
      (projection (d := d) j) := by
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration t
  rw [filtration_eq_comap_past, measurable_comap_iff]
  apply Measurable.of_eval
  intro v
  apply Measurable.of_eval
  intro s
  cases j
  · exact ((IsingConditionalCopyBounds.progressive_rightObservation v).stronglyAdapted s).mono
      (ContinuousCopyBrownian.joinedFiltration.mono s.2) |>.measurable
  · exact ((IsingConditionalCopyBounds.progressive_leftObservation v).stronglyAdapted s).mono
      (ContinuousCopyBrownian.joinedFiltration.mono s.2) |>.measurable

lemma measurable_rightCont_of_past
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ} {φ : Ω → Ξ}
    (hφ : ∀ t, Measurable[F t, G t] φ) (t : ℝ≥0) :
    Measurable[F.rightCont t, G.rightCont t] φ := by
  intro s hs
  change MeasurableSet[G.rightCont t] s at hs
  rw [G.rightCont_eq t] at hs
  rw [F.rightCont_eq t]
  simp only [MeasurableSpace.measurableSet_iInf] at hs ⊢
  intro u htu
  exact hφ u (hs u htu)

lemma projection_measurable_rightCont (j : Bool) (t : ℝ≥0) :
    Measurable[ContinuousCopyBrownian.joinedFiltration.rightCont t,
      (filtration d).rightCont t] (projection (d := d) j) :=
  measurable_rightCont_of_past (projection_measurable_past j) t

def projectedCanonicalExit (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (n : ℕ) (q : Joint d) : WithTop ℝ≥0 :=
  canonicalPosteriorExit beta v n (projection j q)

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma projectedCanonicalExit_localizing (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (j : Bool) :
    IsLocalizingSequence ContinuousCopyBrownian.joinedFiltration.rightCont
      (projectedCanonicalExit beta v j) (copies beta μ) := by
  have h := canonicalPosteriorExit_localizing hd hμ hb hcrit v
  have hp := (copyProjection_measurePreserving beta μ j).quasiMeasurePreserving
  exact {
    isStoppingTime := fun n t => projection_measurable_rightCont j t (h.isStoppingTime n t)
    mono := hp.ae h.mono
    tendsto_top := hp.ae h.tendsto_top }

def combinedCanonicalExit (beta : ℝ) (v : TreeVertex d)
    (n : ℕ) (q : Joint d) : WithTop ℝ≥0 :=
  min (min (projectedCanonicalExit beta v true n q)
    (projectedCanonicalExit beta v false n q)) (commonPosteriorExit beta v n q)

lemma combinedCanonicalExit_le_projected (v : TreeVertex d) (j : Bool)
    (n : ℕ) (q : Joint d) :
    combinedCanonicalExit beta v n q ≤ projectedCanonicalExit beta v j n q := by
  cases j
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_left _ _).trans (min_le_left _ _)

lemma combinedCanonicalExit_le_common (v : TreeVertex d) (n : ℕ) (q : Joint d) :
    combinedCanonicalExit beta v n q ≤ commonPosteriorExit beta v n q :=
  min_le_right _ _

lemma combinedCanonicalExit_localizing (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) :
    IsLocalizingSequence ContinuousCopyBrownian.joinedFiltration.rightCont
      (combinedCanonicalExit beta v) (copies beta μ) :=
  ((projectedCanonicalExit_localizing hd hμ hb hcrit v true).min
    (projectedCanonicalExit_localizing hd hμ hb hcrit v false)).min
      (isLocalizingSequence_commonPosteriorExit hd hμ hb hcrit v)

lemma ae_eventually_le_combinedCanonicalExit (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (T : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop,
      (T : WithTop ℝ≥0) ≤ combinedCanonicalExit beta v n q := by
  filter_upwards [(combinedCanonicalExit_localizing hd hμ hb hcrit v).tendsto_top] with q hq
  exact ((WithTop.tendsto_nhds_top_iff _).mp hq T).mono (fun _ hn => hn.le)

end Problem367.IsingCopyCanonicalStops

end

end OAI
