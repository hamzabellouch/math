import OAI.Analysis.CircleDomains.Probability.HitFusionCaps
import OAI.Analysis.CircleDomains.Probability.FusionTrajectory

namespace OAI

/-! The law on the nested tree and its continuous limiting mixture. Every
scheduled configuration bound survives all subsequent refinements. -/

open Set Filter MeasureTheory ProbabilityTheory Preorder
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity
namespace HitFusionData

variable {X Z : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MetricSpace Z] [SecondCountableTopology Z]
  {law : Z → ProbabilityMeasure C(PathTime, X)} {C : ℝ}
  (T : HitFusionData (law := law) (C := C))

def step (l : List ℕ) : ProbabilityMeasure ℕ :=
  finiteChoiceLaw (T.splitAt l).count (T.splitAt l).weight (T.splitAt l).weight_nonneg (T.splitAt l).weight_sum

def childCap {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ) (p : HitConfiguration X n r) : ℝ :=
  sSup ((fun z => weightedConfigurationHits law z p) '' (T.node (a :: l)).carrier)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem childCap_bddAbove {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) :
    BddAbove ((fun z => weightedConfigurationHits law z p) '' (T.node (a :: l)).carrier) :=
  ⟨n, by rintro _ ⟨z, _, rfl⟩; exact weightedConfigurationHits_le_card law z p⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem le_childCap {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) {z : Z} (hz : z ∈ (T.node (a :: l)).carrier) :
    weightedConfigurationHits law z p ≤ T.childCap l a p :=
  le_csSup (T.childCap_bddAbove l a p) ⟨z, hz, rfl⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem childCap_nonneg {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) : 0 ≤ T.childCap l a p := by
  obtain ⟨z, hz⟩ := (T.node (a :: l)).nonempty
  exact (weightedConfigurationHits_nonneg law z p).trans (T.le_childCap l a p hz)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem childCap_le_card {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) : T.childCap l a p ≤ n := by
  apply csSup_le ((T.node (a :: l)).nonempty.image _)
  rintro _ ⟨z, _, rfl⟩
  exact weightedConfigurationHits_le_card law z p

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem integral_childCap_le (l : List ℕ)
    (p : HitConfiguration X (T.sizes l.length) (T.separations l.length)) :
    ∫ a, T.childCap l a p ∂(T.step l : Measure ℕ) ≤ C + T.error := by
  rw [step, integral_finiteChoiceLaw]
  exact (T.splitAt l).weighted_hitCap_le p

variable [CompleteSpace Z]

def endpoint (x : ℕ → ℕ) : Z := T.scheme.limit (FusionTrajectory.branch x)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem continuous_endpoint : Continuous T.endpoint :=
  T.scheme.continuous_limit.comp (by unfold FusionTrajectory.branch; fun_prop)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, X)] [SecondCountableTopology Z] in
theorem endpoint_mem (x : ℕ → ℕ) (n : ℕ) :
    T.endpoint x ∈ (T.node (PiNat.res (FusionTrajectory.branch x) n)).carrier :=
  T.scheme.limit_mem _ _

def addressLaw : ProbabilityMeasure (ℕ → ℕ) :=
  ⟨FusionTrajectory.measure T.step, inferInstance⟩

omit [SecondCountableTopology Z] in
theorem integral_endpoint_hits_le (hlaw : Continuous law) (d : ℕ)
    (p : HitConfiguration X (T.sizes d) (T.separations d)) :
    ∫ x, weightedConfigurationHits law (T.endpoint x) p
      ∂(T.addressLaw : Measure (ℕ → ℕ)) ≤ C + T.error := by
  let g : List ℕ → ℕ → ℝ := fun l a => T.childCap l a p
  have hg : ∀ l a, |g l a| ≤ T.sizes d := fun l a => by
    rw [abs_of_nonneg (T.childCap_nonneg l a p)]
    exact T.childCap_le_card l a p
  have hgm : Measurable (fun x : ℕ → ℕ =>
      g (PiNat.res (FusionTrajectory.branch x) d) (x (d + 1))) := by
    have hm : Measurable (fun q : FusionTrajectory.History d × ℕ =>
        g (FusionTrajectory.history d q.1) q.2) := measurable_of_countable _
    have hc : Measurable (fun x : ℕ → ℕ => (frestrictLe d x, x (d + 1))) :=
      (measurable_frestrictLe d).prodMk (measurable_pi_apply (d + 1))
    simpa only [Function.comp_def, FusionTrajectory.history_restrict] using hm.comp hc
  have hgi : Integrable
      (fun x => g (PiNat.res (FusionTrajectory.branch x) d) (x (d + 1)))
      (T.addressLaw : Measure (ℕ → ℕ)) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (T.sizes d) ?_
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hg _ _
  have hfi : Integrable (fun x => weightedConfigurationHits law (T.endpoint x) p)
      (T.addressLaw : Measure (ℕ → ℕ)) := by
    refine Integrable.of_bound ?_ (T.sizes d) ?_
    · exact ((weightedConfigurationHits_upperSemicontinuous hlaw _ _).comp
        (T.continuous_endpoint.prodMk continuous_const)).measurable.aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (weightedConfigurationHits_nonneg law _ p)]
        exact weightedConfigurationHits_le_card law _ p
  calc
    ∫ x, weightedConfigurationHits law (T.endpoint x) p ∂(T.addressLaw : Measure (ℕ → ℕ)) ≤
        ∫ x, g (PiNat.res (FusionTrajectory.branch x) d) (x (d + 1))
          ∂(T.addressLaw : Measure (ℕ → ℕ)) := by
      apply integral_mono hfi hgi
      intro x
      exact T.le_childCap _ _ p (T.endpoint_mem x (d + 1))
    _ = ∫ h : FusionTrajectory.History d,
        ∫ a, g (FusionTrajectory.history d h) a
          ∂(T.step (FusionTrajectory.history d h) : Measure ℕ)
        ∂(FusionTrajectory.measure T.step).map (frestrictLe d) :=
      FusionTrajectory.integral_next T.step d g (T.sizes d) hg
    _ ≤ C + T.error := by
      have hnonneg (h : FusionTrajectory.History d) :
          0 ≤ ∫ a, g (FusionTrajectory.history d h) a
            ∂(T.step (FusionTrajectory.history d h) : Measure ℕ) :=
        integral_nonneg fun a => T.childCap_nonneg _ a p
      have hbound (l : List ℕ) (hl : l.length = d) :
          ∫ a, g l a ∂(T.step l : Measure ℕ) ≤ C + T.error := by
        subst d
        exact T.integral_childCap_le l p
      calc
        _ ≤ ∫ _ : FusionTrajectory.History d, C + T.error
            ∂(FusionTrajectory.measure T.step).map (frestrictLe d) :=
          integral_mono_of_nonneg (Eventually.of_forall hnonneg) (integrable_const _)
            (Eventually.of_forall fun h => hbound _ (by
              simp only [FusionTrajectory.history, PiNat.res_length]))
        _ = C + T.error := by simp

end HitFusionData
end CircleDomainRigidity

end

end OAI
