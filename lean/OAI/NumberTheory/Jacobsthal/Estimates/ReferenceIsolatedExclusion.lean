import OAI.NumberTheory.Jacobsthal.Partitions.ThresholdMeshRate
import OAI.NumberTheory.Jacobsthal.Paths.WeightedIsolatedWords
import OAI.NumberTheory.Jacobsthal.Paths.WeightedRepeatedWords
import OAI.NumberTheory.Jacobsthal.Primes.LogarithmicPrimeLength

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceLengthExclusion
open _root_.Set _root_.Filter FinitePathGeometry ReferenceAdmission LogarithmicBinPartition LogarithmicPrimeLength
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

theorem sourcePrimeSet_eq_between {w top : ℝ} (hw : 0 ≤ w) : sourcePrimeSet w top=primesBetween w top := by
  ext p
  simp only [sourcePrimeSet,primesBetween,Finset.mem_sdiff,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hn⟩
    refine ⟨hp,?_⟩
    by_contra! hle
    exact hn (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hw).mpr hle,(Nat.mem_primesLE.mp hp).2⟩)
  · rintro ⟨hp,hlo⟩
    refine ⟨hp,?_⟩
    intro hsmall
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hw).mp (Nat.mem_primesLE.mp hsmall).1)

theorem uniform_source_length_exclusion (A : ℝ) :
    ∃ L B₀ w₀ : ℝ,1 ≤ L ∧ 1 < B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w^B=top → ∀ Clen : ℝ,L ≤ Clen →
      ∀ F : Finset (List ℕ),F ⊆ decreasingPrefixes (sourcePrimeSet w top) →
      (∀ ps ∈ F,Clen*Real.log B < (ps.length:ℝ)) → (∑ ps ∈ F,prefixWeight ps) ≤ B^(-A) := by
  obtain ⟨w₀,hw₀,hTail⟩ := logarithmic_prime_length_tail
  obtain ⟨L,hL,hTail⟩ := hTail A
  obtain ⟨BT,hBT⟩ := eventually_atTop.mp hTail
  refine ⟨L,max 2 BT,w₀,hL,lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _),hw₀,?_⟩
  intro B w top hB hw htop Clen hClen F hF hLong
  have hB2 : 2 ≤ B := (le_max_left _ _).trans hB
  have hw1 : 1 < w := hw₀.trans_le hw
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  let m := ⌈L*Real.log B⌉₊
  have hsub : F ⊆ (decreasingPrefixes (primesBetween w (w^B))).filter (fun ps => m ≤ ps.length) := by
    intro ps hp
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · simpa only [sourcePrimeSet_eq_between (zero_lt_one.trans hw1).le,← htop] using hF hp
    · apply Nat.ceil_le.mpr
      exact ((mul_le_mul_of_nonneg_right hClen hlog).trans_lt (hLong ps hp)).le
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ps _ _ => prefixWeight_nonneg ps)
  exact hh.trans (hBT B ((le_max_right _ _).trans hB) w hw m (Nat.le_ceil _))

noncomputable def longReferenceWords (w top Clen B : ℝ) (i : Side) (r : ℝ) : Finset (List ℕ) :=
  (referencePrefixes w (sourcePrimeSet w top) i r).filter (fun ps => Clen*Real.log B < (ps.length:ℝ))

theorem literal_reference_length_exclusion (A : ℝ) :
    ∃ L B₀ w₀ : ℝ,1 ≤ L ∧ 1 < B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w^B=top → ∀ Clen : ℝ,L ≤ Clen →
      ∀ i : Side,∀ r : ℝ,(∑ ps ∈ longReferenceWords w top Clen B i r,prefixWeight ps) ≤ B^(-A) := by
  obtain ⟨L,B₀,w₀,hL,hB₀,hw₀,hBound⟩ := uniform_source_length_exclusion A
  refine ⟨L,B₀,w₀,hL,hB₀,hw₀,?_⟩
  intro B w top hB hw htop Clen hClen i r
  apply hBound B w top hB hw htop Clen hClen (longReferenceWords w top Clen B i r)
  · intro ps hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · intro ps hp
    exact (Finset.mem_filter.mp hp).2
end NumberTheoryLean.SourceLengthExclusion



namespace NumberTheoryLean.ReferenceClearanceFailure
open FinitePathGeometry PrimeHistories ReferenceAdmission ActualPrefixClearance RepresentativeStopGeometry
open PrimePrefixRecovery ReconstructedParentCoupling MarkedPrefixTools LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass


theorem admitted_even_endpoint (w : ℝ) (z : Node) (ps : List ℕ)
    (ha : admitted w z.side z.gap ps) (hne : ps ≠ []) (hi : (terminal w z ps).side=.even) :
    sourceHeight (terminal w z ps).cutoff ≤ (terminal w z ps).gap := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    cases ps with
    | nil =>
      cases hz : z.side with
      | even => simp [terminal,step,hz,Side.flip] at hi
      | odd =>
        have hh := ha.1
        rw [hz] at hh
        exact hh
    | cons q qs => exact ih (step w z p) ha.2 (by simp) hi

theorem reference_clearance_failure_prefix {w top Delta : ℝ} (hw : 1 < w) (htop : w < top)
    (z : Node) (ps : List ℕ)
    (hps : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hbad : ¬actualClearance w z Delta ps) : hasNearThresholdPrefix w (10*Delta) z ps := by
  classical
  change ¬∀ qs ∈ ps.inits,qs ≠ [] → (terminal w z qs).side=.even →
    sourceHeight (terminal w z qs).cutoff+10*Delta < (terminal w z qs).gap at hbad
  push Not at hbad
  obtain ⟨qs,hqs,hne,hi,hfail⟩ := hbad
  obtain ⟨tail,htail⟩ := (List.mem_inits _ _).mp hqs
  have ha : admitted w z.side z.gap qs :=
    ((admitted_append w z.gap z.side qs tail).mp (by simpa only [htail] using (Finset.mem_filter.mp hps).2)).1
  have hgate := admitted_even_endpoint w z qs ha hne hi
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hps).1
  have hlast : qs.getLastD 0 ∈ qs := by
    have he : qs.getLastD 0=qs.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hne
  have hlastPS : qs.getLastD 0 ∈ ps := by rw [← htail]; exact List.mem_append.mpr (Or.inl hlast)
  have hprime := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hd.2 _ hlastPS)
  have hx : 1 < primeExponent w (qs.getLastD 0) :=
    (one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hprime.2.1)
  rw [← terminal_lastD w z qs hne] at hx
  exact ⟨qs,tail,htail.symm,hne,hi,hx,by linarith,by linarith⟩
end NumberTheoryLean.ReferenceClearanceFailure



namespace NumberTheoryLean.SourceThresholdRate
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories SourceSelectedCompactOccupation SourceThresholdCoupling ThresholdMeshRate
open SourceCouplingRate ExponentialMesh TwoSidedThresholdKernel LowStateHorizon


theorem source_prime_threshold_probability : ∃ κ₀ : ℝ,0 < κ₀ ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ D eps : ℝ,0 < D → 0 < eps →
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ D*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      ∀ delta : ℝ,0 ≤ delta → delta ≤ 1 →
      fullSourceLaw w ell S start hs (mesh κ w) N {h | primeThresholdOccurs delta N h} ≤
        ENNReal.ofReal ((8/3:ℝ)*thickConstant*delta+eps) := by
  have hCpos : 0 < thickConstant := thickConstant_pos
  obtain ⟨κ₀,hκ₀,hCouple⟩ := source_coupling_rate
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle D eps hD heps
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ hκle D hD
  have hA : 0 ≤ 5*D^3 := by positivity
  have hEvents := (threshold_mesh_controls hA thickConstant_pos.le hκ (show 0 < eps/2 by positivity)).and
    (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
      (eventually_le_nhds (show 0 < eps/2 by positivity))).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (D^2)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨max WC (max normalizationThreshold W),hWC.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hr hs23 hc hsize
  dsimp only
  intro delta hd0 hd1
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hcontrols := hwe.1 (sourceHorizon ((Real.log B)^2) B) hscale.2
  have hf := (hC w hwC ell B start hs hell hB hlogB hcomp hr hs23 hc hsize).1
    (sourceHorizon ((Real.log B)^2) B) le_rfl |>.1
  have hfail : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using hwe.2.1
  have hprob := source_threshold_probability hnorm hell hS0 hscale.1 hr hs hsS hc
    (mesh_pos κ w) (mesh_le_one hκ.le w) hd0 hd1 (sourceHorizon ((Real.log B)^2) B) hcontrols.1
  rw [← fullSourceLaw_eq hnorm hell hS0 hscale.1 hr hs hsS] at hprob
  have he : thickConstant*((8/3:ℝ)*delta+((sourceHorizon ((Real.log B)^2) B:ℝ)+1)*
      thresholdPerturbation (mesh κ w) (sourceHorizon ((Real.log B)^2) B)) ≤
        (8/3:ℝ)*thickConstant*delta+eps/2 := by nlinarith [hcontrols.2]
  calc
    _ ≤ _ := hprob
    _ ≤ ENNReal.ofReal (eps/2)+ENNReal.ofReal ((8/3:ℝ)*thickConstant*delta+eps/2) :=
      add_le_add (hf.trans (ENNReal.ofReal_le_ofReal hfail)) (ENNReal.ofReal_le_ofReal he)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2)
        (by positivity : 0 ≤ (8/3:ℝ)*thickConstant*delta+eps/2)]
      congr 1
      ring
end NumberTheoryLean.SourceThresholdRate



namespace NumberTheoryLean.WeightedNearThreshold
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership ActualPrimeHigh
open SourceSelectedCompactOccupation CompactPrefixOccurrence PrimePrefixRecovery NearPrefixOccurrence
open SourceThresholdRate UncappedCompactEvent TwoSidedThresholdKernel ExponentialMesh
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem weighted_near_threshold_prefix_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ,0 < C ∧ ∀ eps : ℝ,0 < eps → ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
    ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ,∀ start : Node,∀ _hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ D*Real.log w →
      start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 → Consistent start → start.cutoff=B →
      ∀ delta : ℝ,0 ≤ delta → delta ≤ 1 → ∀ E : Set (List ℕ),
      (∀ ps ∈ uncappedPrefixes w ell start,ps ∈ E →
        (terminal w start ps).gap ≤ R ∧ hasNearThresholdPrefix w delta start ps) →
      B^2*(∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤ C*delta+eps := by
  obtain ⟨cR,WC,hcR,hWC,hCompact⟩ := uncapped_compact_event R hR D hD
  obtain ⟨κ,hκ,hProb⟩ := source_prime_threshold_probability
  have hCT : 0 < thickConstant := thickConstant_pos
  refine ⟨cR*((8/3:ℝ)*thickConstant),by positivity,?_⟩
  intro eps heps
  let eta := eps/(2*cR)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨WP,hWP,hP⟩ := hProb κ hκ le_rfl D eta hD heta
  obtain ⟨BC,hBC,hCbound⟩ := hCompact (3:ℝ)
  let w₀ := max WC (max WP (max normalizationThreshold (Real.exp (D^2))))
  refine ⟨max BC (max (Real.exp 2) (2/eps)),w₀,hBC.trans_le (le_max_left _ _),
    hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hBB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut delta hd0 hd1 E hE
  have hB : 0 < B := hBC.trans_le ((le_max_left _ _).trans hBB)
  have hExpB : Real.exp 2 ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr hExpB
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hwP : WP ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  have hExpW : Real.exp (D^2) ≤ w :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw
  have hlogw : D^2 ≤ Real.log w := (Real.le_log_iff_exp_le (zero_lt_one.trans hw1)).mpr hExpW
  have hscale := UniformBudgetRate.source_scale_bound hlogw hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hrnode := SourceNodeCoordinates.source_node_bounds hB start hi h199 h23 hc hcut
  have hHist : ∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E →
      hasNearThresholdPrefix w delta start p.primes := by
    intro p hp
    have hu : p.primes ∈ uncappedPrefixes w ell start :=
      (mem_uncappedPrefixes hw1 start p.primes).mpr
        ((uncapped_iff_exists_ceiling w ell start p.primes).mpr ⟨(Real.log B)^2,hsS,p.admissible⟩)
    exact (hE p.primes hu hp).2
  have hOcc := near_prefix_occurrence_probability hnorm hell hS0 hscale.1 hrnode.2.1 hs hsS
    (mesh κ w) delta (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) E hHist
  have hProbability := hOcc.trans (hP w hwP ell B start hs hell hB hlogB hcomp hrnode.2.1 h23 hc hrnode.2.2.2 delta hd0 hd1)
  have hpr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hProbability
  rw [ENNReal.toReal_ofReal (show 0 ≤ (8/3:ℝ)*thickConstant*delta+eta by positivity)] at hpr
  have hMass := hCbound B w ((le_max_left _ _).trans hBB) hwC ell start hs hell hellB hcomp
    hi h199 h23 hc hcut (mesh κ w) E (fun ps hp hsel => (hE ps hp hsel).1)
  have hMass' : (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (cR/B^2)*((8/3:ℝ)*thickConstant*delta+eta)+B^(-(3:ℝ)) :=
    hMass.trans (add_le_add (mul_le_mul_of_nonneg_left hpr (show 0 ≤ cR/B^2 by positivity)) le_rfl)
  have hlarge : 2/eps ≤ B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hBB
  have hinv : 1/B ≤ eps/2 := by
    have hh := (div_le_iff₀ heps).mp hlarge
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hcEta : cR*eta=eps/2 := by dsimp [eta]; field_simp [hcR.ne']
  have hpow : B^(-(3:ℝ))=(B^3)⁻¹ := by rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
  calc
    _ ≤ B^2*((cR/B^2)*((8/3:ℝ)*thickConstant*delta+eta)+B^(-(3:ℝ))) :=
      mul_le_mul_of_nonneg_left hMass' (sq_nonneg B)
    _ = cR*((8/3:ℝ)*thickConstant)*delta+cR*eta+1/B := by rw [hpow]; field_simp [hB.ne']
    _ ≤ _ := by rw [hcEta]; linarith
end NumberTheoryLean.WeightedNearThreshold



namespace NumberTheoryLean.ReferenceClearanceMass
open _root_.Set _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ActualPrefixClearance ReferenceClearanceFailure WeightedNearThreshold
open StrongReferenceTransport StrongSourceFamilies LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem uniform_reference_clearance_failure_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ,0 < C ∧ ∀ eps : ℝ,0 < eps → ∃ B₀ w₀ : ℝ,3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ D*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ Delta : ℝ,0 ≤ Delta → 10*Delta ≤ 1 → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ R ∧ ¬actualClearance w z Delta ps) →
      B^2*(∑ ps ∈ F,prefixWeight ps) ≤ C*Delta+eps := by
  obtain ⟨c,hc,hMass⟩ := weighted_near_threshold_prefix_mass R hR D hD
  refine ⟨10*c,by positivity,?_⟩
  intro eps heps
  obtain ⟨BC,w₀,_hBC,hw₀,hBound⟩ := hMass eps heps
  refine ⟨max BC 3,w₀,le_max_right _ _,hw₀,?_⟩
  intro B w top hB hw htop hcomp z hi h199 h23 hz hcut hclosed hcap Delta hDel hsmall F hF hBad
  have hB3 : 3 ≤ B := (le_max_right _ _).trans hB
  have hw1 : 1 < w := hw₀.trans_le hw
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap' : w^z.cutoff=top := by rwa [hcut]
  have hsub : F ⊆ uncappedPrefixes w 1 z :=
    fun ps hp => (source_reference_transport hw1 htop z hs hz hg hclosed hcap' ps (hF hp)).1
  have he : (uncappedPrefixes w 1 z).filter (fun ps => ps ∈ (F : Set (List ℕ)))=F := by
    ext ps
    simp only [Finset.mem_filter,Finset.mem_coe]
    exact ⟨And.right,fun hp => ⟨hsub hp,hp⟩⟩
  have hSelected := hBound B w ((le_max_left _ _).trans hB) hw 1 z hs (by norm_num) (by linarith)
    hcomp hi h199 h23 hz hcut (10*Delta) (by positivity) hsmall (F : Set (List ℕ))
    (fun ps _hp hps => ⟨(hBad ps hps).1,reference_clearance_failure_prefix hw1 htop z ps (hF hps) (hBad ps hps).2⟩)
  have hSelected' : B^2*(∑ ps ∈ F,prefixWeight ps) ≤ c*(10*Delta)+eps := by
    convert! hSelected using 1
    congr 1
    apply Finset.sum_congr
    · ext ps
      simp only [Finset.mem_filter,Finset.mem_coe]
      exact ⟨fun hp => ⟨hsub hp,hp⟩,And.right⟩
    · intro ps _
      rfl
  nlinarith
end NumberTheoryLean.ReferenceClearanceMass



namespace NumberTheoryLean.ReferenceRepeatedExclusion
open _root_.Set _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission RepeatedWordEvents WeightedRepeatedWords
open StrongReferenceTransport StrongSourceFamilies LogarithmicBinPartition
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem uniform_reference_repeated_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D)
    (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → Real.log B ≤ D*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ R ∧ (searchRepeatedWord hw htop hxi ps ∨
        compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z ps)) →
      B^2*(∑ ps ∈ F,prefixWeight ps) ≤ eps := by
  obtain ⟨BC,WC,hBC,hWC,hBound⟩ := weighted_repeated_word_mass R hR D hD L hL eps heps
  refine ⟨max BC 3,WC,le_max_right _ _,hWC,?_⟩
  intro B w top hB hw₀ hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap F hF hBad
  have hB3 : 3 ≤ B := (le_max_right _ _).trans hB
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap' : w^z.cutoff=top := by rwa [hcut]
  have hsub : F ⊆ uncappedPrefixes w 1 z :=
    fun ps hp => (source_reference_transport hw htop z hs hz hg hclosed hcap' ps (hF hp)).1
  obtain ⟨hw',hSel⟩ := hBound B w ((le_max_left _ _).trans hB) hw₀ top htop xi hxi hxi1
  have hSelected := hSel 1 z hs (by norm_num) (by linarith) hcomp hi h199 h23 hz hcut hcap'
    (F : Set (List ℕ)) (fun ps _hp hps => hBad ps hps)
  convert! hSelected using 1
  congr 1
  apply Finset.sum_congr
  · ext ps
    simp only [Finset.mem_filter,Finset.mem_coe]
    exact ⟨fun hp => ⟨hsub hp,hp⟩,And.right⟩
  · intro ps _
    rfl
end NumberTheoryLean.ReferenceRepeatedExclusion



namespace NumberTheoryLean.BasicRegularMass
open FinitePathGeometry PrimeHistories ActualRegularBoxes ActualPrefixClearance RepeatedWordEvents
open ReferenceAdmission RegularityDefectPartition ReferenceRepeatedExclusion ReferenceClearanceMass SourceLengthExclusion
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem basic_regular_defect_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D) :
    ∃ L C : ℝ,1 ≤ L ∧ 0 < C ∧ ∀ Clen : ℝ,L ≤ Clen → ∀ eps : ℝ,0 < eps →
      ∃ B₀ w₀ : ℝ,3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 20*Clen*xi ≤ 1 → Real.log B ≤ D*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      PrimeBinMembership.Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ R) →
      B^2*(∑ ps ∈ F \ regularWords hw htop hxi Clen B R z,prefixWeight ps) ≤ C*(2*Clen*xi)+eps := by
  obtain ⟨L,BL,WL,hL,hBL,hWL,hLen⟩ := uniform_source_length_exclusion (3:ℝ)
  obtain ⟨C,hC,hClear⟩ := uniform_reference_clearance_failure_mass R hR D hD
  refine ⟨L,C,hL,hC,?_⟩
  intro Clen hClen eps heps
  have hClen0 : 0 ≤ Clen := (by linarith : 0 ≤ L).trans hClen
  have he : 0 < eps/3 := by positivity
  obtain ⟨BC,WC,hBC,hWC,hClear⟩ := hClear (eps/3) he
  obtain ⟨BR,WR,hBR,hWR,hRepeat⟩ := uniform_reference_repeated_mass R hR D hD 0 (by norm_num) (eps/3) he
  refine ⟨max BL (max BC (max BR (3/eps))),max WL (max WC WR),
    hBC.trans (le_trans (le_max_left _ _) (le_max_right _ _)),hWL.trans_le (le_max_left _ _),?_⟩
  intro B w top hB hw₀ hw htop xi hxi hxi1 hsmall hcomp z hi h199 h23 hz hcut hclosed hcap F hF hg
  have hBlen : BL ≤ B := (le_max_left _ _).trans hB
  have hBclear : BC ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hBrep : BR ≤ B := (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hB
  have hBsize : 3/eps ≤ B := (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hB
  have hBp : 0 < B := (by linarith : 0 < BL).trans_le hBlen
  have hwlen : WL ≤ w := (le_max_left _ _).trans hw₀
  have hwclear : WC ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have hwrep : WR ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀
  have hlong := hLen B w top hBlen hwlen hcap Clen hClen (F.filter (lengthFailure Clen B))
    (fun ps hp => (Finset.mem_filter.mp (hF (Finset.mem_filter.mp hp).1)).1)
    (fun ps hp => (Finset.mem_filter.mp hp).2)
  have hclear := hClear B w top hBclear hwclear htop hcomp z hi h199 h23 hz hcut hclosed hcap
    (2*Clen*xi) (by positivity) (by nlinarith) (F.filter (clearanceFailure w (2*Clen*xi) z))
    (fun ps hp => hF (Finset.mem_filter.mp hp).1)
    (fun ps hp => ⟨hg ps (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩)
  have hrepeat := hRepeat B w top hBrep hwrep hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap
    (F.filter (searchRepeatedWord hw htop hxi)) (fun ps hp => hF (Finset.mem_filter.mp hp).1)
    (fun ps hp => ⟨hg ps (Finset.mem_filter.mp hp).1,Or.inl (Finset.mem_filter.mp hp).2⟩)
  have hinv : 1/B ≤ eps/3 := by
    have hh := (div_le_iff₀ heps).mp hBsize
    apply (div_le_iff₀ hBp).mpr
    nlinarith
  have hpow : B^2*B^(-(3:ℝ))=1/B := by
    rw [Real.rpow_neg hBp.le,Real.rpow_ofNat]
    field_simp [hBp.ne']
  have hlong' : B^2*(∑ ps ∈ F.filter (lengthFailure Clen B),prefixWeight ps) ≤ eps/3 :=
    (mul_le_mul_of_nonneg_left hlong (sq_nonneg B)).trans (hpow.le.trans hinv)
  have hpart := mul_le_mul_of_nonneg_left (regularity_defect_sum (C:=Clen) (B:=B) hw htop hxi z F hF hg) (sq_nonneg B)
  nlinarith
end NumberTheoryLean.BasicRegularMass



namespace NumberTheoryLean.ReferenceIsolatedExclusion
open _root_.Set _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission NonisolatedWordOccurrence WeightedIsolatedWords
open StrongReferenceTransport StrongSourceFamilies LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem uniform_reference_nonisolated_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (eps : ℝ) (heps : 0 < eps) :
    ∃ alpha B₀ w₀ : ℝ,0 < alpha ∧ alpha ≤ theta ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
    ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → Real.log B ≤ D*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 →
      Consistent z → z.cutoff=B → z.closed=true → w^B=top →
      ∀ F : Finset (List ℕ),F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ R ∧ noIsolatedWord hw htop hxi B alpha (4*theta) ps) →
      B^2*(∑ ps ∈ F,prefixWeight ps) ≤ eps := by
  obtain ⟨alpha,BC,WC,ha,hath,hBC,hWC,hBound⟩ := weighted_nonisolated_mass R hR D hD theta htheta htheta1 eps heps
  refine ⟨alpha,max BC 3,WC,ha,hath,le_max_right _ _,hWC,?_⟩
  intro B w top hB hw₀ hw htop xi hxi hxi1 hcomp z hi h199 h23 hz hcut hclosed hcap F hF hBad
  have hB3 : 3 ≤ B := (le_max_right _ _).trans hB
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap' : w^z.cutoff=top := by rwa [hcut]
  have hsub : F ⊆ uncappedPrefixes w 1 z :=
    fun ps hp => (source_reference_transport hw htop z hs hz hg hclosed hcap' ps (hF hp)).1
  have hSelected := hBound B w ((le_max_left _ _).trans hB) hw₀ hw top htop xi hxi hxi1
    1 z hs (by norm_num) (by linarith) hcomp hi h199 h23 hz hcut hcap'
    (F : Set (List ℕ)) (fun ps _hp hps => hBad ps hps)
  convert! hSelected using 1
  congr 1
  apply Finset.sum_congr
  · ext ps
    simp only [Finset.mem_filter,Finset.mem_coe]
    exact ⟨fun hp => ⟨hsub hp,hp⟩,And.right⟩
  · intro ps _
    rfl
end NumberTheoryLean.ReferenceIsolatedExclusion


end Erdos970

end OAI
