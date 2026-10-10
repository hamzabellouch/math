import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalResidualNorm
import OAI.Analysis.LipschitzHilbert.Trees.SourceParentResidualSquare
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualSplit

namespace OAI

/-! A parent-cone reference event controls the original short residuals.
The remaining long packets occur only in the terminal block and retain
the original single-scale selector estimate. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem eventually_physical_parent_full_residual_square
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ K) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s w R C F pathSlope : ℝ) (hw : 0 < w) (hR : 0 < R)
      (hcone : 0 ≤ C+(SourceParameters.branching L)^3) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hKb shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let cone := C+(SourceParameters.branching L)^3
    let S := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R pathSlope cone w
    let Q := P.referenceFamily t pathSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t pathSlope R cone w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      pathSlope a (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
        (L^(3*q+13))^2 := by
  filter_upwards [eventually_physical_parent_short_square q D hq hD,
    eventually_physical_shifted_residual_norm q D 1 hD zero_le_one K H,
    eventually_ge_atTop (2:ℝ)] with L hshortBound hlongBound hL
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w R C F pathSlope hw hR hcone hF hwide hfrequency
    hbranch hKb shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he hangle hgood
  let cut := grid.rootWidth/(SourceParameters.branching L)^2
  let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  let weight := fun top z => (T top).weight (L^(A+2)) D z
  let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hKb shift
  let short := packets.filter (fun u => P.length u.1 ≤ R)
  let long := packets.filter (fun u => ¬P.length u.1 ≤ R)
  let value := P.physicalMaskedValue alt hAlt t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
  let base := grid.sourcePacketBase tops slope precision cut weight assigned
    (fun u => stop u.1) value alpha z
  let trans := grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
    (grid.sourceBoundaryGap L) phase z
  let residual (Q : Finset P.PacketIndex) (j : Fin count) :=
    grid.packetResidual Q (fun u => slope (assigned u)) (fun u => stop u.1) base trans
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)
  have hshort : (∑ j : Fin count, ‖residual short j‖^2) ≤ (L^(3*q+12))^2 :=
    hshortBound N κ Label Item P horder hP alt hAlt t pathSlope R C F w a hw
      hcone hF hwide hfrequency b hb hb1 v hv f hf hf1 τ grid tops slope precision T A s
      hbranch hKb shift hzero hp phase hz alpha ha ha1 z packets assigned hassigned he
      hangle hgood count
  have hsupport (j : Fin count) (hj : j.val+1 < count) : residual long j = 0 :=
    grid.source_shifted_long_residual_support packets (fun u => slope (assigned u))
      (fun u : P.PacketIndex => P.length u.1) (fun u => P.length_pos u.1)
      hw (SourceParameters.branching_pos L) hR hKb shift
      (fun u _ => hzero u.1) base trans pathSlope j hj
  have hterminal (j : Fin count) : ‖residual long j‖ ≤ L^(2*q+3) :=
    hlongBound N κ Label Item P horder hP alt hAlt t d radius hd hradius hlocal b hb hb1
      hsupp v hv f hf hf1 τ grid tops slope precision T A w hw hbranch hKb shift hzero hp
      phase hz alpha ha ha1 z long assigned
      (fun u hu => hassigned u (Finset.mem_filter.mp hu).1)
      (fun u hu => he u (Finset.mem_filter.mp hu).1) j.val pathSlope
  have hsplit (j : Fin count) : residual packets j = residual short j+residual long j :=
    grid.packetResidual_filter_split packets (fun u => slope (assigned u)) (fun u => stop u.1)
      base trans (fun u => P.length u.1 ≤ R) _ _ _
  change (∑ j : Fin count, ‖residual packets j‖^2) ≤ _
  by_cases hc : 0 < count
  · have hfull := terminal_perturbation_square_sum hc (residual packets) (residual short)
      (residual long) hsplit hsupport hshort (Real.rpow_nonneg (by linarith) _) (hterminal _)
    refine hfull.trans ?_
    have hsmall : L^(2*q+3) ≤ L^(3*q+12) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hsmallSq := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hsmall 2
    have hpos : 0 ≤ L^(3*q+12) := Real.rpow_nonneg (by linarith) _
    have hscale : 2*L^(3*q+12) ≤ L^(3*q+12)*L := by nlinarith
    have hscaleSq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*L^(3*q+12)) hscale 2
    have hpow : L^(3*q+13) = L^(3*q+12)*L := by
      rw [show 3*q+13 = (3*q+12)+1 by ring,Real.rpow_add (by linarith),Real.rpow_one]
    rw [hpow]
    nlinarith
  · have hzcount : count = 0 := by omega
    have hsum : (∑ j : Fin count, ‖residual packets j‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      omega
    rw [hsum]
    positivity

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
