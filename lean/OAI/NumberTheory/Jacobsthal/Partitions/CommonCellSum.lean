import OAI.NumberTheory.Jacobsthal.Primes.PrimeCompactWeights
import OAI.NumberTheory.Jacobsthal.Probability.ActualCouplingUpdates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousParentBins

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltBounds PrimeTiltMonotone ContinuousRatioBins
open HarmonicExponentMeasure WeightGlobalBounds

theorem multiplier_source_ratio {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (u : ℝ) :
    multiplier i s u = (weight i t/weight i s)*multiplier i t u := by
  by_cases hu : u = 0
  · simp [multiplier,hu]
  · unfold multiplier
    field_simp [hu,(weight_pos hs).ne',(weight_pos ht).ne']

theorem continuous_bin_mass_ratio {i : Side} {s t a b : ℝ} (hs : Valid i s) (ht : Valid i t)
    (hsa : minRatio i s ≤ a) (hta : minRatio i t ≤ a) :
    weightedRatioLaw i s (Ico a b) = ENNReal.ofReal (weight i t/weight i s) * weightedRatioLaw i t (Ico a b) := by
  have hq : 0 ≤ weight i t/weight i s := (div_pos (weight_pos ht) (weight_pos hs)).le
  simp only [weightedRatioLaw, withDensity_apply _ measurableSet_Ico]
  rw [ratio_restrict_bin hsa, ratio_restrict_bin hta, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [multiplier_source_ratio hs ht u, ENNReal.ofReal_mul hq]

theorem continuousBin_parent_ratio {i : Side} {s t a b : ℝ} (hs : Valid i s) (ht : Valid i t)
    (hsa : minRatio i s ≤ a) (hta : minRatio i t ≤ a) :
    continuousBin i s a b = (weight i t/weight i s)*continuousBin i t a b := by
  unfold continuousBin
  rw [continuous_bin_mass_ratio hs ht hsa hta, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_pos (weight_pos ht) (weight_pos hs)).le]

theorem positive_ratio_error {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlog : |Real.log a-Real.log b| ≤ d) : |a/b-1| ≤ Real.exp d-1 := by
  have hq := div_pos ha hb
  rw [← Real.log_div ha.ne' hb.ne'] at hlog
  have hlo := Real.exp_le_exp.mpr (abs_le.mp hlog).1
  have hup := Real.exp_le_exp.mpr (abs_le.mp hlog).2
  rw [Real.exp_log hq] at hlo hup
  have hsum : 2 ≤ Real.exp d+Real.exp (-d) := by
    linarith [Real.add_one_le_exp d, Real.add_one_le_exp (-d)]
  rw [abs_le]
  constructor <;> linarith

theorem continuous_parent_bin_error : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s t a b : ℝ, Valid i s → Valid i t → s ≤ S → t ≤ S →
      minRatio i s ≤ a → minRatio i t ≤ a →
      |continuousBin i s a b-continuousBin i t a b| ≤
        (Real.exp (C*(1+S)^3*|s-t|)-1)*continuousBin i t a b := by
  obtain ⟨C,hC,hbound⟩ := weights_log_lipschitz
  refine ⟨C,hC,?_⟩
  intro S hS i s t a b hs ht hsS htS hsa hta
  have hlogs : |Real.log (weight i s)-Real.log (weight i t)| ≤ C*(1+S)^3*|s-t| := by
    cases i with
    | even => exact (hbound S hS).1 s t hs ht hsS htS
    | odd => exact (hbound S hS).2 s t hs ht hsS htS
  have hr := positive_ratio_error (weight_pos ht) (weight_pos hs)
    ((abs_sub_comm _ _).trans_le hlogs)
  have hmass : 0 ≤ continuousBin i t a b := ENNReal.toReal_nonneg
  rw [continuousBin_parent_ratio hs ht hsa hta]
  rw [show (weight i t/weight i s)*continuousBin i t a b-continuousBin i t a b =
    (weight i t/weight i s-1)*continuousBin i t a b by ring, abs_mul, abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_right hr hmass

end NumberTheoryLean.ContinuousParentBins

end

section

namespace NumberTheoryLean.NearbyParentFullBins

open _root_.Set _root_.MeasureTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open PrimeBinMembership ActualPrimeBins ContinuousKilledBins
open NormalizedPrimeBins ContinuousRatioBins ContinuousParentBins RegeneratingInverseBands

 theorem nearby_parent_full_bin_error : ∃ c C D w₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ a b : ℝ,
      1 ≤ ell → 3 ≤ S → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 →
      minRatio h.node.side h.node.ratio < a → minRatio (stateSide z.1) (stateRatio z.1) < a →
      a ≤ b → b ≤ S → b ≤ h.node.gap/ell-1 → b ≤ gapValue v z/ell-1 →
      |(chain w ell S start (some h) (liveBin a b)).toReal -
        (continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet a b)).toReal| ≤
      C*(1+S)^5*((b-a)^2+Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) +
        epsilon w*continuousBin h.node.side h.node.ratio a b +
        (Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)*
          continuousBin (stateSide z.1) (stateRatio z.1) a b := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hprime⟩ := normalized_bin_error
  obtain ⟨D,hD,hparent⟩ := continuous_parent_bin_error
  refine ⟨c,C,D,w₀,hc,hC,hD,hw₀,?_⟩
  intro w hw ell S start h v z a b hell hS hr hs hsS hcons htS hside hma hta hab hbS harrP harrC
  have hw1 := hw₀.trans_le hw
  have hell0 : 0 < ell := by linarith
  have hnvalid := terminal_valid hs h.admissible
  have hngap := terminal_gap_positive hell0.le hr hs h.admissible
  have hnS := terminal_ratio_le hsS h.admissible
  have hncons := history_consistent hell0.le hr hs hcons h
  have htvalid : Valid h.node.side (stateRatio z.1) := by rw [hside]; exact stateRatio_valid z.1
  have hta' : minRatio h.node.side (stateRatio z.1) < a := by rwa [hside]
  have ha : 0 < a := (PrimeTiltMonotone.minRatio_pos hnvalid).trans hma
  have hlow : (1/2 : ℝ) ≤ h.node.gap/(b+1) := by
    have h : ell ≤ h.node.gap/(b+1) := by
      apply (le_div_iff₀ (by linarith : 0 < b+1)).mpr
      have hm := (le_div_iff₀ hell0).mp (show b+1 ≤ h.node.gap/ell by linarith)
      nlinarith
    linarith
  rw [chain_full_bin_real h hw1 hell0 hngap hnvalid hncons hma hab hbS harrP,
    continuousChain_full_bin_real v hell0 z hbS harrC, ← hside]
  exact (abs_sub_le _ (continuousBin h.node.side h.node.ratio a b) _).trans (add_le_add
    (hprime w hw h.node.gap S hngap hS h.node.side h.node.ratio a b hnvalid hnS hma.le hab hbS hlow)
    (hparent S hS h.node.side h.node.ratio (stateRatio z.1) a b hnvalid htvalid hnS htS hma.le hta'.le))

end NumberTheoryLean.NearbyParentFullBins

end

section

namespace NumberTheoryLean.ActualSupportIntervals

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open PrimeTiltGeometry ActualCouplingUpdates ContinuousKilledBins LowStateHorizon
open ArrivalKernelGeometry RegeneratingInverseBands PairedCostGrouping

noncomputable def upperSupport (S ell r : ℝ) : ℝ := min S (r/ell-1)

theorem prime_child_interval {w ell S : ℝ} {start : Node} (h : History w ell S start)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio)
    (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node.ratio ∈ Icc (minRatio h.node.side h.node.ratio) (upperSupport S ell h.node.gap) := by
  classical
  have hp' := (Finset.mem_filter.mp hp).2
  have ht0 := valid_pos (child_valid hs hp)
  have hx := hp'.1
  have heq := nextExponent_childRatio hr (child_exponent_positive hell.le hp)
  have hu : childRatio w h.node.gap p < h.node.gap/ell-1 := by
    rw [← heq] at hx
    have hmul := (lt_div_iff₀ (by linarith : 0 < childRatio w h.node.gap p+1)).mp hx
    have hdiv : childRatio w h.node.gap p+1 < h.node.gap/ell := (lt_div_iff₀ hell).mpr (by nlinarith)
    linarith
  rw [History.append_node]
  exact ⟨hp'.2.2.1,le_min hp'.2.2.2 hu.le⟩

theorem prime_row_interval {w ell S : ℝ} {start : Node} (h : History w ell S start)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio) :
    ∀ᵐ k ∂chain w ell S start (some h),
      match k with
      | none => True
      | some k => k.node.ratio ∈ Icc (minRatio h.node.side h.node.ratio) (upperSupport S ell h.node.gap) := by
  filter_upwards [prime_follows h] with k hk
  cases k with
  | none => trivial
  | some k =>
    obtain ⟨p,hp,rfl⟩ := hk
    exact prime_child_interval h hell hr hs p hp

theorem costKernel_lower_support (z : CostState) :
    ∀ᵐ y ∂costKernel z, minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio y.1 := by
  have hm : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hP : MeasurableSet {y : CostState | minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio y.1} :=
    measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)
  rw [costKernel_eq_map]
  exact (ae_map_iff hm.aemeasurable hP).mpr (stateKernel_ae_minRatio z.1)

theorem continuous_interval_measurable (v ell S : ℝ) (z : CostState) :
    MeasurableSet {y : CostState | stateRatio y.1 ∈
      Icc (minRatio (stateSide z.1) (stateRatio z.1)) (upperSupport S ell (gapValue v z))} :=
  (stateRatio_measurable.comp measurable_fst) measurableSet_Icc

theorem continuous_low_interval (v S : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState) :
    ∀ᵐ y ∂lowKernel costKernel v ell S z, stateRatio y.1 ∈
      Icc (minRatio (stateSide z.1) (stateRatio z.1)) (upperSupport S ell (gapValue v z)) := by
  rw [lowKernel,Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (costKernel_time_update z),ae_restrict_of_ae (costKernel_lower_support z),
    ae_restrict_mem (lowDomain_measurable v ell S)] with y htime hlo hD
  have hy : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl htime
  have hcur : currentExponent v y = nextExponent (gapValue v z) (stateRatio y.1) := by
    calc
      _ = currentExponent v (y.1,z.2+cost (stateRatio y.1)) := congrArg (currentExponent v) hy
      _ = _ := currentExponent_update v z y.1
  have hupper : stateRatio y.1 < gapValue v z/ell-1 := by
    have hx : ell < nextExponent (gapValue v z) (stateRatio y.1) := by
      rw [← hcur]
      exact hD.1
    have ht0 := OccupationBoundaries.stateRatio_pos y.1
    have hmul := (lt_div_iff₀ (by linarith : 0 < stateRatio y.1+1)).mp hx
    have hdiv : stateRatio y.1+1 < gapValue v z/ell := (lt_div_iff₀ hell).mpr (by nlinarith)
    linarith
  exact ⟨hlo,le_min hD.2 hupper.le⟩

theorem continuous_row_interval (v S : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState) :
    ∀ᵐ y ∂continuousChain v ell S (.inl z), liftPredicate (fun y : CostState => stateRatio y.1 ∈
      Icc (minRatio (stateSide z.1) (stateRatio z.1)) (upperSupport S ell (gapValue v z))) y :=
  complete_ae _ z (continuous_interval_measurable v ell S z) (continuous_low_interval v S hell z)

end NumberTheoryLean.ActualSupportIntervals

end

section

namespace NumberTheoryLean.ActualMeshBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ActualPrimeBins ContinuousKilledBins
open MeshRatioLabels MeshBoundaryGeometry ActualSupportIntervals PrimeBinMembership
open NearbyParentFullBins ContinuousRatioBins RegeneratingInverseBands

variable {w ell S : ℝ} {start : Node}

theorem prime_label_eq_bin {mesh : ℝ} (hm : 0 < mesh) (hs : Valid start.side start.ratio)
    (hsS : start.ratio ≤ S) (j : Label S mesh) (hj : j ≠ cemeteryLabel S mesh) :
    (primeLabel w ell S mesh start) ⁻¹' {j} = liveBin (lowerEdge j) (upperEdge j) := by
  ext p
  cases p with
  | none =>
    change cemeteryLabel S mesh = j ↔ False
    simp [Ne.symm hj]
  | some h =>
    have ht := valid_pos (terminal_valid hs h.admissible)
    have hS := terminal_ratio_le hsS h.admissible
    exact ratioLabel_eq_iff hm ht.le hS j

theorem continuous_label_mass_eq_bin (v ell S : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (z : CostState) (j : Label S mesh) (hj : j ≠ cemeteryLabel S mesh) :
    continuousChain v ell S (.inl z) ((continuousLabel S mesh) ⁻¹' {j}) =
      continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet (lowerEdge j) (upperEdge j)) := by
  apply measure_congr
  filter_upwards [continuous_supported v ell S (.inl z)] with y hy
  apply propext
  cases y with
  | inr u =>
    change (cemeteryLabel S mesh = j) ↔ ∃ x ∈ ratioBinSet (lowerEdge j) (upperEdge j), (Sum.inl x : CemeteryKernel.Space CostState) = Sum.inr u
    simp [Ne.symm hj]
  | inl y =>
    have heq := ratioLabel_eq_iff hm (OccupationBoundaries.stateRatio_pos y.1).le hy j
    change (ratioLabel S mesh (stateRatio y.1) = j) ↔ ∃ x ∈ ratioBinSet (lowerEdge j) (upperEdge j), (Sum.inl x : CemeteryKernel.Space CostState) = Sum.inl y
    simpa only [Set.mem_image,Sum.inl.injEq,exists_eq_right,ratioBinSet,mem_ofPred_eq,lowerEdge,upperEdge] using heq

theorem cell_below_S_not_cemetery {S mesh : ℝ} (hm : 0 < mesh) (j : Label S mesh)
    (hj : upperEdge j ≤ S) : j ≠ cemeteryLabel S mesh := by
  intro heq
  subst j
  have hf := Nat.lt_floor_add_one (S/mesh)
  have hmul : S < ((⌊S/mesh⌋₊:ℝ)+1)*mesh := (div_lt_iff₀ hm).mp hf
  change (((binCount S mesh+1:ℕ):ℝ)+1)*mesh ≤ S at hj
  simp only [Nat.cast_add,Nat.cast_one,binCount] at hj
  nlinarith

theorem mesh_cells_disjoint {S mesh : ℝ} (hm : 0 < mesh) :
    Pairwise (fun j k : Label S mesh => Disjoint (Ico (lowerEdge j) (upperEdge j)) (Ico (lowerEdge k) (upperEdge k))) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro t htj htk
  have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (j.val:ℝ)+1 ≤ (k.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have he : upperEdge j ≤ lowerEdge k := mul_le_mul_of_nonneg_right hle hm.le
    exact (htj.2.trans_le (he.trans htk.1)).false
  · have hle : (k.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have he : upperEdge k ≤ lowerEdge j := mul_le_mul_of_nonneg_right hle hm.le
    exact (htk.2.trans_le (he.trans htj.1)).false

theorem continuous_mesh_sum_le_one {S mesh s : ℝ} {i : Side} (hm : 0 < mesh) (hs : Valid i s)
    (I : Finset (Label S mesh)) :
    (∑ j ∈ I,continuousBin i s (lowerEdge j) (upperEdge j)) ≤ 1 := by
  let := weightedRatioLaw_probability hs
  have hUnion := measure_biUnion_finset (μ:=weightedRatioLaw i s)
    (s:=I) (f:=fun j => Ico (lowerEdge j) (upperEdge j))
    (fun _ _ _ _ hne => mesh_cells_disjoint hm hne) (fun _ _ => measurableSet_Ico)
  have hmass : (∑ j ∈ I,weightedRatioLaw i s (Ico (lowerEdge j) (upperEdge j))) ≤ 1 := by
    rw [← hUnion]
    exact (measure_mono (subset_univ _)).trans_eq measure_univ
  unfold continuousBin
  rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top (weightedRatioLaw i s) (Ico (lowerEdge j) (upperEdge j)))]
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hmass

theorem common_cell_error : ∃ c C D w₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ, ∀ j : Label S mesh,
      1 ≤ ell → 3 ≤ S → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      fullCell (minRatio h.node.side h.node.ratio) (minRatio (stateSide z.1) (stateRatio z.1))
        (upperSupport S ell h.node.gap) (upperSupport S ell (gapValue v z)) j →
      |(chain w ell S start (some h) ((primeLabel w ell S mesh start) ⁻¹' {j})).toReal-
        (continuousChain v ell S (.inl z) ((continuousLabel S mesh) ⁻¹' {j})).toReal| ≤
        C*(1+S)^5*(mesh^2+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))+
        epsilon w*continuousBin h.node.side h.node.ratio (lowerEdge j) (upperEdge j)+
        (Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)*
          continuousBin (stateSide z.1) (stateRatio z.1) (lowerEdge j) (upperEdge j) := by
  obtain ⟨c,C,D,w₀,hc,hC,hD,hw₀,hbound⟩ := nearby_parent_full_bin_error
  refine ⟨c,C,D,w₀,hc,hC,hD,hw₀,?_⟩
  intro w hw ell S start h v z mesh j hell hS hr hs hsS hcons hzS hside hm hcell
  have hLd := (le_max_left _ _).trans_lt hcell.1
  have hLc := (le_max_right _ _).trans_lt hcell.1
  have hUd := hcell.2.trans (min_le_left _ _)
  have hUc := hcell.2.trans (min_le_right _ _)
  have hbS := hUd.trans (min_le_left _ _)
  have hbp := hUd.trans (min_le_right _ _)
  have hbc := hUc.trans (min_le_right _ _)
  have hj := cell_below_S_not_cemetery hm j hbS
  rw [prime_label_eq_bin hm hs hsS j hj,continuous_label_mass_eq_bin v ell S hm z j hj]
  have hab : lowerEdge j ≤ upperEdge j := by unfold lowerEdge upperEdge; nlinarith
  have he := hbound w hw ell S start h v z (lowerEdge j) (upperEdge j) hell hS hr hs hsS hcons hzS hside hLd hLc hab hbS hbp hbc
  have hwidth : upperEdge j-lowerEdge j = mesh := by unfold upperEdge lowerEdge; ring
  rwa [hwidth] at he

end NumberTheoryLean.ActualMeshBins

end

section

namespace NumberTheoryLean.CommonCellSum

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels MeshBoundaryGeometry ActualSupportIntervals ActualMeshBins
open ActualProcessCoupling ContinuousKilledBins PrimeBinMembership
open ContinuousRatioBins RegeneratingInverseBands KernelBinConditioning

theorem common_cell_sum_error : ∃ c C D w₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ, ∀ I : Finset (Label S mesh),
      1 ≤ ell → 3 ≤ S → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      (∀ j ∈ I, fullCell (minRatio h.node.side h.node.ratio) (minRatio (stateSide z.1) (stateRatio z.1))
        (upperSupport S ell h.node.gap) (upperSupport S ell (gapValue v z)) j) →
      (∑ j ∈ I, |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
        labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|) ≤
        (S/mesh+2)*(C*(1+S)^5*(mesh^2+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))))+
        epsilon w+(Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1) := by
  obtain ⟨c,C,D,w₀,hc,hC,hD,hw₀,hbound⟩ := common_cell_error
  refine ⟨c,C,D,w₀,hc,hC,hD,hw₀,?_⟩
  intro w hw ell S start h v z mesh I hell hS hr hs hsS hcons hzS hside hm hcells
  let A := C*(1+S)^5*(mesh^2+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))
  let Q := Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1
  let P : Label S mesh → ℝ := fun j => continuousBin h.node.side h.node.ratio (lowerEdge j) (upperEdge j)
  let R : Label S mesh → ℝ := fun j => continuousBin (stateSide z.1) (stateRatio z.1) (lowerEdge j) (upperEdge j)
  have hS1 : 0 ≤ 1+S := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ : 0 ≤ Q := by
    apply sub_nonneg.mpr
    apply Real.one_le_exp_iff.mpr
    positivity
  have hPsum : (∑ j ∈ I,P j) ≤ 1 := continuous_mesh_sum_le_one hm (terminal_valid hs h.admissible) I
  have hRsum : (∑ j ∈ I,R j) ≤ 1 := continuous_mesh_sum_le_one hm (stateRatio_valid z.1) I
  have hcard : (I.card:ℝ) ≤ S/mesh+2 := by
    have h : (I.card:ℝ) ≤ (Fintype.card (Label S mesh):ℝ) := by exact_mod_cast Finset.card_le_univ I
    exact h.trans (label_card_le (by linarith) hm)
  calc
    _ ≤ ∑ j ∈ I,(A+epsilon w*P j+Q*R j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hbound w hw ell S start h v z mesh j hell hS hr hs hsS hcons hzS hside hm (hcells j hj)
    _ = (I.card:ℝ)*A+epsilon w*(∑ j ∈ I,P j)+Q*(∑ j ∈ I,R j) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right hcard hA
      have h2 := mul_le_mul_of_nonneg_left hPsum (epsilon_pos w).le
      have h3 := mul_le_mul_of_nonneg_left hRsum hQ
      dsimp only [A,Q] at h1 h3 ⊢
      linarith

end NumberTheoryLean.CommonCellSum

end

end Erdos970

end OAI
