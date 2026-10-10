import OAI.NumberTheory.Jacobsthal.Partitions.CommonCellSum
import OAI.NumberTheory.Jacobsthal.Partitions.FiniteLabelBudget
import OAI.NumberTheory.Jacobsthal.Primes.ConditionalPrimeBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CoupledBoundaryEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualSupportIntervals MeshBoundaryGeometry MeshRatioLabels
open PrimeCompletedIntervalUpper ContinuousIntervalUpper ActualCouplingSupport
open RegeneratingInverseBands ContinuousKilledBins

noncomputable def lowerA (Ld Lc : ℝ) : ℝ := max (1/2) (min Ld Lc)
noncomputable def lowerB (mesh Ld Lc : ℝ) : ℝ := max (1/2) (max Ld Lc+mesh)
noncomputable def upperA (mesh Ud Uc : ℝ) : ℝ := max (1/2) (min Ud Uc-mesh)
noncomputable def upperB (Ud Uc : ℝ) : ℝ := max (1/2) (max Ud Uc)

variable {w ell S : ℝ} {start : Node}

def primeBadCells (mesh Ld Lc Ud Uc : ℝ) : Set (ChainState w ell S start) :=
  fun p => match p with
    | none => False
    | some h => ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh h.node.ratio)

def continuousBadCells (S mesh Ld Lc Ud Uc : ℝ) : Set (CemeteryKernel.Space CostState) :=
  fun p => match p with
    | .inr _ => False
    | .inl z => ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh (stateRatio z.1))

theorem packet_widths {mesh : ℝ} (hm : 0 ≤ mesh) (Ld Lc Ud Uc : ℝ) :
    (0 < lowerA Ld Lc ∧ lowerA Ld Lc ≤ lowerB mesh Ld Lc ∧
      lowerB mesh Ld Lc-lowerA Ld Lc ≤ |Ld-Lc|+mesh) ∧
    (0 < upperA mesh Ud Uc ∧ upperA mesh Ud Uc ≤ upperB Ud Uc ∧
      upperB Ud Uc-upperA mesh Ud Uc ≤ |Ud-Uc|+mesh) := by
  have hl : min Ld Lc ≤ max Ld Lc+mesh := by linarith [min_le_max (a:=Ld) (b:=Lc)]
  have hu : min Ud Uc-mesh ≤ max Ud Uc := by linarith [min_le_max (a:=Ud) (b:=Uc)]
  exact ⟨clipped_packet_width hl (le_of_eq (lowerPacket_width mesh Ld Lc)),
    clipped_packet_width hu (le_of_eq (upperPacket_width mesh Ud Uc))⟩

theorem point_in_clipped_packets {mesh t Ld Lc Ud Uc : ℝ} (hm : 0 ≤ mesh) (ht : (1/2:ℝ) ≤ t)
    (h : t ∈ lowerPacket mesh Ld Lc ∪ upperPacket mesh Ud Uc) :
    t ∈ Icc (lowerA Ld Lc) (lowerB mesh Ld Lc) ∪ Icc (upperA mesh Ud Uc) (upperB Ud Uc) := by
  rcases h with h | h
  · exact Or.inl (clipPacket (show min Ld Lc ≤ max Ld Lc+mesh by linarith [min_le_max (a:=Ld) (b:=Lc)]) ht h).1
  · exact Or.inr (clipPacket (show min Ud Uc-mesh ≤ max Ud Uc by linarith [min_le_max (a:=Ud) (b:=Uc)]) ht h).1

theorem prime_bad_cell_packets (h : History w ell S start) (hell : 0 < ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    {mesh : ℝ} (hm : 0 < mesh) (Lc Uc : ℝ) :
    let Ld := minRatio h.node.side h.node.ratio
    let Ud := upperSupport S ell h.node.gap
    chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc) ≤
      chain w ell S start (some h) (closedLiveBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
      chain w ell S start (some h) (closedLiveBin (upperA mesh Ud Uc) (upperB Ud Uc)) := by
  dsimp only
  have hvalid := terminal_valid hs h.admissible
  have hgap := terminal_gap_positive hell.le hr hs h.admissible
  apply le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [prime_row_interval h hell hgap hvalid] with k hk
  intro hbad
  cases k with
  | none => exact False.elim hbad
  | some k =>
    have hhalf : (1/2:ℝ) ≤ k.node.ratio := PrimeTiltBounds.valid_ge_half (terminal_valid hs k.admissible)
    have hS := terminal_ratio_le hsS k.admissible
    have hp := noninterior_in_packets hm (by linarith : 0 ≤ k.node.ratio) hS (Or.inl hk) hbad
    exact point_in_clipped_packets hm.le hhalf hp

theorem continuous_bad_cell_packets (v : ℝ) (z : CostState) (hell : 0 < ell)
    {mesh : ℝ} (hm : 0 < mesh) (Ld Ud : ℝ) :
    let Lc := minRatio (stateSide z.1) (stateRatio z.1)
    let Uc := upperSupport S ell (gapValue v z)
    continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc) ≤
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (upperA mesh Ud Uc) (upperB Ud Uc)) := by
  dsimp only
  apply le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [continuous_row_interval v S hell z,continuous_supported v ell S (.inl z)] with y hy hS
  intro hbad
  cases y with
  | inr u => exact False.elim hbad
  | inl y =>
    have hhalf := CostPrefixTransport.stateRatio_ge_half y.1
    have hp := noninterior_in_packets hm (by linarith : 0 ≤ stateRatio y.1) hS (Or.inr hy) hbad
    rcases point_in_clipped_packets hm.le hhalf hp with hp | hp
    · exact Or.inl (Set.mem_image_of_mem Sum.inl hp)
    · exact Or.inr (Set.mem_image_of_mem Sum.inl hp)

end NumberTheoryLean.CoupledBoundaryEvents

end

section


namespace NumberTheoryLean.CouplingLabelEvents

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels MeshBoundaryGeometry ActualProcessCoupling ActualCouplingSupport
open CoupledBoundaryEvents KernelBinConditioning FiniteLabelBudget ContinuousKilledBins

noncomputable def interiorLabels (S mesh Ld Lc Ud Uc : ℝ) : Finset (Label S mesh) := by
  classical
  exact Finset.univ.filter (fullCell Ld Lc Ud Uc)

noncomputable def boundaryLabels (S mesh Ld Lc Ud Uc : ℝ) : Finset (Label S mesh) := by
  classical
  exact (Finset.univ.erase (cemeteryLabel S mesh)).filter (fun j => ¬fullCell Ld Lc Ud Uc j)

variable {w ell S : ℝ} {start : Node}

theorem prime_boundary_event {mesh : ℝ} (hm : 0 < mesh)
    (hsS : start.ratio ≤ S) (Ld Lc Ud Uc : ℝ) :
    (primeLabel w ell S mesh start) ⁻¹' (boundaryLabels S mesh Ld Lc Ud Uc : Set (Label S mesh)) =
      primeBadCells mesh Ld Lc Ud Uc := by
  classical
  ext p
  cases p with
  | none =>
    change cemeteryLabel S mesh ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ False
    simp [boundaryLabels]
  | some h =>
    have hne : ratioLabel S mesh h.node.ratio ≠ cemeteryLabel S mesh := ratioLabel_ne_cemetery hm (terminal_ratio_le hsS h.admissible)
    change ratioLabel S mesh h.node.ratio ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh h.node.ratio)
    simp [boundaryLabels,hne]

theorem continuous_boundary_event_mass (v ell S : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (z : CostState) (Ld Lc Ud Uc : ℝ) :
    continuousChain v ell S (.inl z)
      ((continuousLabel S mesh) ⁻¹' (boundaryLabels S mesh Ld Lc Ud Uc : Set (Label S mesh))) =
      continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc) := by
  classical
  apply measure_congr
  filter_upwards [continuous_supported v ell S (.inl z)] with y hy
  apply propext
  cases y with
  | inr u =>
    change cemeteryLabel S mesh ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ False
    simp [boundaryLabels]
  | inl y =>
    have hne := ratioLabel_ne_cemetery hm hy
    change ratioLabel S mesh (stateRatio y.1) ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh (stateRatio y.1))
    simp [boundaryLabels,hne]

theorem prime_boundary_mass [IsMarkovKernel (chain w ell S start)] {mesh : ℝ} (hm : 0 < mesh)
    (hsS : start.ratio ≤ S)
    (h : History w ell S start) (Ld Lc Ud Uc : ℝ) :
    (∑ j ∈ boundaryLabels S mesh Ld Lc Ud Uc,labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j) =
      (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal := by
  rw [selected_label_mass _ (primeLabel_measurable w ell S mesh start),prime_boundary_event hm hsS]

theorem continuous_boundary_mass (v ell S : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (z : CostState) (Ld Lc Ud Uc : ℝ) :
    (∑ j ∈ boundaryLabels S mesh Ld Lc Ud Uc,labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j) =
      (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal := by
  rw [selected_label_mass _ (continuousLabel_measurable S mesh),continuous_boundary_event_mass v ell S hm z]

theorem actual_label_budget (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (h : History w ell S start) (v : ℝ) (z : CostState) {mesh : ℝ} (hm : 0 < mesh)
    (Ld Lc Ud Uc : ℝ) :
    (∑ j : Label S mesh, |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
      labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|) ≤
      2*((∑ j ∈ interiorLabels S mesh Ld Lc Ud Uc,
        |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
          labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|)+
        (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal+
        (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal) := by
  classical
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  let a := labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h)
  let b := labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z)
  let good := fullCell (S:=S) (mesh:=mesh) Ld Lc Ud Uc
  have hbudget := interior_boundary_budget a b (cemeteryLabel S mesh) good
    (labelMass_nonneg (chain w ell S start) (primeLabel w ell S mesh start) (some h))
    (labelMass_nonneg (continuousChain v ell S) (continuousLabel S mesh) (.inl z))
    (labelMass_sum (chain w ell S start) (primeLabel_measurable w ell S mesh start) (some h))
    (labelMass_sum (continuousChain v ell S) (continuousLabel_measurable S mesh) (.inl z))
  have hsub : (Finset.univ.erase (cemeteryLabel S mesh)).filter good ⊆ interiorLabels S mesh Ld Lc Ud Uc := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => abs_nonneg (a j-b j))
  change (∑ j,|a j-b j|) ≤ _
  have hbad : (∑ j ∈ (Finset.univ.erase (cemeteryLabel S mesh)).filter (fun j => ¬good j),(a j+b j)) =
      (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal+
      (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal := by
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (prime_boundary_mass hm hsS h Ld Lc Ud Uc)
      (continuous_boundary_mass v ell S hm z Ld Lc Ud Uc)
  rw [hbad] at hbudget
  linarith

end NumberTheoryLean.CouplingLabelEvents

end

end Erdos970

end OAI
