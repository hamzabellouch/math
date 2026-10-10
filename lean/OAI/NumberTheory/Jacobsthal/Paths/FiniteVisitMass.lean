import OAI.NumberTheory.Jacobsthal.Estimates.RawSuppliedPast

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.TransitionKernels

abbrev FiniteRawHistory := Σ n : ℕ, RawHistory n

def selectedVisitPrefix (q : Σ t : ℕ, RawReturnTrace t) : FiniteRawHistory :=
  ⟨q.1+1,rawPrefix (show q.1+1 ≤ q.1+2*(q.2.1+1) by omega) q.2.2⟩

lemma selectedVisitPrefix_measurable : Measurable selectedVisitPrefix := by
  apply measurable_sigma_family
  intro t
  apply measurable_sigma_family
  intro n
  exact (measurableSigmaMk (t+1)).comp (rawPrefix_measurable (show t+1 ≤ t+2*(n+1) by omega))

noncomputable def rawVisitPrefix (a : ℕ) : RawEvenMarkedHitTrace a → FiniteRawHistory :=
  selectedVisitPrefix ∘ rawEvenFinalCycle a

lemma rawVisitPrefix_measurable (a : ℕ) : Measurable (rawVisitPrefix a) :=
  selectedVisitPrefix_measurable.comp (rawEvenFinalCycle_measurable a)

noncomputable def finiteRawLast (h : FiniteRawHistory) : CostState := rawLast h.1 h.2

lemma finiteRawLast_measurable : Measurable finiteRawLast := by
  apply measurable_sigma_family
  intro n
  exact rawLast_measurable n

lemma rawVisitPrefix_length (a : ℕ) (z : RawEvenMarkedHitTrace a) : a+1 < (rawVisitPrefix a z).1 := by
  have h := rawEvenFinalCycle_anchor_gt a z
  change a+1 < (rawEvenFinalCycle a z).1+1
  omega

lemma rawVisitPrefix_last (a : ℕ) (z : RawEvenMarkedHitTrace a) :
    finiteRawLast (rawVisitPrefix a z)=recordFirst (rawEvenHitRecord a z) := by
  rw [rawEvenFinalCycle_record]
  change finiteRawLast (selectedVisitPrefix (rawEvenFinalCycle a z))=
    recordFirst (rawReturnInputSignature (rawEvenFinalCycle a z).1 (rawEvenFinalCycle a z).2)
  rcases he : rawEvenFinalCycle a z with ⟨t,n,h⟩
  rfl

noncomputable def rawVisitPrefixKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) FiniteRawHistory :=
  (rawEvenMarkedHitKernel a v H).map (rawVisitPrefix a)

instance rawVisitPrefixKernel_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (rawVisitPrefixKernel a v H) := by
  unfold rawVisitPrefixKernel
  infer_instance

theorem rawVisitPrefix_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    rawVisitPrefixKernel a v H past univ=rawEvenMarkedHitKernel a v H past univ := by
  rw [rawVisitPrefixKernel,Kernel.map_apply' _ (rawVisitPrefix_measurable a) _ MeasurableSet.univ,preimage_univ]

theorem rawVisitPrefix_mass_eq_ordinaryHit (a : ℕ) (v H : ℝ) (past : RawHistory a) (s : EvenState)
    (hs : rawLast a past=(Sum.inl s,0)) :
    rawVisitPrefixKernel a v H past univ=ordinaryInitialHitMass s v H := by
  rw [rawVisitPrefix_mass,rawEvenMarkedHit_mass a v H past s hs]

theorem rawVisitPrefix_last_law (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (rawVisitPrefixKernel a v H past).map finiteRawLast=
      (rawEvenMarkedHitKernel a v H past).map (fun z => recordFirst (rawEvenHitRecord a z)) := by
  rw [rawVisitPrefixKernel,Kernel.map_apply _ (rawVisitPrefix_measurable a),
    Measure.map_map finiteRawLast_measurable (rawVisitPrefix_measurable a)]
  congr 1
  funext z
  exact rawVisitPrefix_last a z

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.FinitePathGeometry

noncomputable def finiteRawPrevious (h : FiniteRawHistory) : CostState :=
  h.2 ⟨h.1-1,Finset.mem_Iic.mpr (Nat.sub_le _ _)⟩

lemma finiteRawPrevious_measurable : Measurable finiteRawPrevious := by
  apply measurable_sigma_family
  intro n
  change Measurable (fun h : RawHistory n => h ⟨n-1,Finset.mem_Iic.mpr (Nat.sub_le _ _)⟩)
  exact measurable_pi_apply _

lemma finiteRawLength_measurable : Measurable (fun q : FiniteRawHistory => q.1) := by
  apply measurable_sigma_family
  intro n
  exact measurable_const

lemma rawVisitPrefix_previous (a : ℕ) (z : RawEvenMarkedHitTrace a) :
    finiteRawPrevious (rawVisitPrefix a z)=rawEvenHitAnchor a z := by
  change finiteRawPrevious (selectedVisitPrefix (rawEvenFinalCycle a z))=
    selectedCycleAnchor (rawEvenFinalCycle a z)
  rcases rawEvenFinalCycle a z with ⟨t,n,h⟩
  simp only [finiteRawPrevious,selectedVisitPrefix,Nat.add_sub_cancel]
  rfl

lemma rawEvenHitAnchor_cost (a : ℕ) (z : RawEvenMarkedHitTrace a) :
    (rawEvenHitAnchor a z).2=(rawEvenHitRecord a z).1 := by
  rw [rawEvenFinalCycle_record]
  rfl

noncomputable def finiteSuppliedPast (a : ℕ) (past : RawHistory a) : Set FiniteRawHistory :=
  {q | q.2 ∈ suppliedPastEvent a past q.1}

lemma finiteSuppliedPast_measurable (a : ℕ) (past : RawHistory a) : MeasurableSet (finiteSuppliedPast a past) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact suppliedPastEvent_measurable a past n

lemma selectedVisitPrefix_past (a : ℕ) (past : RawHistory a) (q : Σ t : ℕ, RawReturnTrace t)
    (ha : a ≤ q.1+1) (hq : q ∈ selectedHistoryProperty (suppliedPastEvent a past)) :
    selectedVisitPrefix q ∈ finiteSuppliedPast a past := by
  obtain ⟨hab,hp⟩ := hq
  exact ⟨ha,hp⟩

theorem rawVisitPrefix_ae_past (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    ∀ᵐ q ∂rawVisitPrefixKernel a v H past, q ∈ finiteSuppliedPast a past := by
  rw [rawVisitPrefixKernel,Kernel.map_apply _ (rawVisitPrefix_measurable a)]
  apply (ae_map_iff (rawVisitPrefix_measurable a).aemeasurable (finiteSuppliedPast_measurable a past)).mpr
  filter_upwards [rawEvenHit_retains_suppliedPast a v H past] with z hz
  exact selectedVisitPrefix_past a past (rawEvenFinalCycle a z)
    (by have ha:=rawEvenFinalCycle_anchor_gt a z; omega) hz

noncomputable def finitePrefixSourceEvent (a : ℕ) (v H : ℝ) : Set FiniteRawHistory :=
  {q | a+1 < q.1 ∧ finiteRawPrevious q ∈ regenerationSet ∧
    firstArrivalMark (finiteRawLast q)=true ∧
    (finiteRawLast q).2=(finiteRawPrevious q).2+cost (stateRatio (finiteRawLast q).1) ∧
    (finiteRawPrevious q).2 ∈ Icc v (v+H)}

lemma finitePrefixSourceEvent_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (finitePrefixSourceEvent a v H) :=
  (measurableSet_lt measurable_const finiteRawLength_measurable).inter
    ((regenerationSet_measurable.preimage finiteRawPrevious_measurable).inter
      (((firstArrivalMark_measurable.comp finiteRawLast_measurable) (measurableSet_singleton true)).inter
        ((measurableSet_eq_fun (measurable_snd.comp finiteRawLast_measurable)
          ((measurable_snd.comp finiteRawPrevious_measurable).add
            (cost_measurable.comp (stateRatio_measurable.comp (measurable_fst.comp finiteRawLast_measurable))))).inter
          (measurableSet_Icc.preimage (measurable_snd.comp finiteRawPrevious_measurable)))))

theorem rawVisitPrefix_ae_source (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    ∀ᵐ q ∂rawVisitPrefixKernel a v H past, q ∈ finitePrefixSourceEvent a v H := by
  rw [rawVisitPrefixKernel,Kernel.map_apply _ (rawVisitPrefix_measurable a)]
  apply (ae_map_iff (rawVisitPrefix_measurable a).aemeasurable (finitePrefixSourceEvent_measurable a v H)).mpr
  filter_upwards [rawEvenHit_anchor_regenerates a v H past,rawEvenHit_ae_physical a v H past] with z hA hP
  refine ⟨rawVisitPrefix_length a z,?_,?_,?_,?_⟩
  · rw [rawVisitPrefix_previous]
    exact hA
  · rw [rawVisitPrefix_last]
    exact hP.1.1
  · rw [rawVisitPrefix_last,rawVisitPrefix_previous,rawEvenHitAnchor_cost]
    exact hP.1.2
  · rw [rawVisitPrefix_previous,rawEvenHitAnchor_cost]
    exact hP.2

theorem rawVisitPrefix_witness_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    rawVisitPrefixKernel a v H past (finiteSuppliedPast a past ∩ finitePrefixSourceEvent a v H)=
      rawEvenMarkedHitKernel a v H past univ := by
  have hm := (finiteSuppliedPast_measurable a past).inter (finitePrefixSourceEvent_measurable a v H)
  have hA : ∀ᵐ q ∂rawVisitPrefixKernel a v H past, q ∈ finiteSuppliedPast a past ∩ finitePrefixSourceEvent a v H := by
    filter_upwards [rawVisitPrefix_ae_past a v H past,rawVisitPrefix_ae_source a v H past] with q hp hs
    exact ⟨hp,hs⟩
  rw [(ae_mem_iff_measure_eq hm.nullMeasurableSet).mp hA,rawVisitPrefix_mass]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels

lemma finitePrefixSourceEvent_even_witness {a : ℕ} {v H : ℝ} {q : FiniteRawHistory}
    (hq : q ∈ finitePrefixSourceEvent a v H) :
    ∃ tau : EvenState, 209/100 ≤ tau.1 ∧ tau.1 ≤ 213/100 ∧
      finiteRawLast q=(Sum.inl tau,(finiteRawPrevious q).2+NumberTheoryLean.FinitePathGeometry.cost tau.1) := by
  let c : CycleInputSignature := ((finiteRawPrevious q).2,(q.1,(finiteRawLast q,finiteRawLast q)))
  have hc : c ∈ physicalMarkedRecord := ⟨hq.2.2.1,hq.2.2.2.1⟩
  exact physicalMarkedRecord_witness hc

noncomputable def visitHorizonEvent (a : ℕ) (v H : ℝ) (past : RawHistory a) (N : ℕ) : Set FiniteRawHistory :=
  (finiteSuppliedPast a past ∩ finitePrefixSourceEvent a v H) ∩ {q | q.1 ≤ N}

lemma visitHorizonEvent_measurable (a : ℕ) (v H : ℝ) (past : RawHistory a) (N : ℕ) :
    MeasurableSet (visitHorizonEvent a v H past N) :=
  ((finiteSuppliedPast_measurable a past).inter (finitePrefixSourceEvent_measurable a v H)).inter
    (measurableSet_le finiteRawLength_measurable measurable_const)

theorem finite_visit_horizon_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    Tendsto (fun N : ℕ => rawVisitPrefixKernel a v H past (visitHorizonEvent a v H past N)) atTop
      (𝓝 (rawEvenMarkedHitKernel a v H past univ)) := by
  have hm : Monotone (visitHorizonEvent a v H past) := by
    intro N M hNM q hq
    exact ⟨hq.1,hq.2.trans hNM⟩
  have hu : (⋃ N : ℕ, visitHorizonEvent a v H past N)=
      finiteSuppliedPast a past ∩ finitePrefixSourceEvent a v H := by
    ext q
    constructor
    · intro hq
      obtain ⟨N,hN⟩ := mem_iUnion.mp hq
      exact hN.1
    · intro hq
      exact mem_iUnion.mpr ⟨q.1,hq,(show q.1 ≤ q.1 from le_rfl)⟩
  have ht := tendsto_measure_iUnion_atTop (μ := rawVisitPrefixKernel a v H past) hm
  rw [hu,rawVisitPrefix_witness_mass] at ht
  exact ht

theorem finite_visit_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ (a : ℕ) (past : RawHistory a) (s : EvenState),
      rawLast a past=(Sum.inl s,0) → s.1 ≤ S → ∀ v H : ℝ, 0 ≤ H →
        1-rawVisitPrefixKernel a v H past (finiteSuppliedPast a past ∩ finitePrefixSourceEvent a v H) ≤
          ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,eta0,B,heta,hC,heta0,hB,h⟩ := rawEvenMarkedHit_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro a past s hs hS v H hH
  rw [rawVisitPrefix_witness_mass]
  exact h a past s hs hS v H hH

theorem moving_finite_visit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ (a : ℕ) (past : RawHistory a) (s : EvenState),
        rawLast a past=(Sum.inl s,0) → 199/100 ≤ s.1 → s.1 ≤ 23/10 →
        1-rawVisitPrefixKernel a (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) past
          (finiteSuppliedPast a past ∩ finitePrefixSourceEvent a
            (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))) ≤ ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_raw_even_marked_hit heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr a past s hs hs0 hs1
  rw [rawVisitPrefix_witness_mass]
  exact hw.2 r hr a past s hs hs0 hs1

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
