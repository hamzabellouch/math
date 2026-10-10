import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalSingleScale
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualBlockBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualMask
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryScales

namespace OAI

/-! The original physical residual at one angular block has a uniform
polynomial norm bound. This controls the one possible long-packet block;
no total label count or carrier-frequency factor enters. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem physicalMaskedValue_eq_complex_cross (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) :
    P.physicalMaskedValue alt hAlt t b v f T L A z =
      fun u => ((T u.1 u.2.1 u.2.2).mask L A z:ℂ) •
        P.physicalCrossPacketValue alt hAlt t b v f 0 z u := by
  funext u
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have h := P.physicalMaskedValue_eq_cross alt hAlt t b v f T L A
    (z.2-t*z.1) z.1 u
  rw [hpoint] at h
  rw [h]
  ext k
  simp only [PiLp.smul_apply,Complex.real_smul,smul_eq_mul]

/-- Absolute summation at each source length, followed by the exact
mask/mass coefficient estimate, controls any single residual block. -/
theorem physical_masked_residual_norm {τ : Type*}
    (horder : 6 ≤ P.order) (t : ℝ) (d radius : Fin N → ℝ) (M : ℝ) (K H : ℕ)
    (hd : ∀ j, 0 < d j) (hM : 0 ≤ M) (hradius : ∀ j, radius j ≤ K)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) (d j) H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius j*d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (T : τ → SlopeBox) (L A D : ℝ) (hL : 2 ≤ L) (hD : 0 ≤ D)
    (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ)) (hp : ∀ top ∈ tops, 0 ≤ precision top)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (hassigned : ∀ u ∈ packets, assigned u ∈ tops)
    (he : ∀ u ∈ packets, grid.eligible cutoff (precision (assigned u)) (stop u.1))
    (lower upper : ℕ) (pathSlope : ℝ) :
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    ‖grid.packetResidual packets (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        value alpha z)
      (grid.sourceTransition tops slope precision cutoff weight Kb gap phase z)
      lower upper (grid.index lower pathSlope)‖ ≤
    ((residualLengthSet stop lower upper).card:ℝ)*
      (P.absoluteConstant*((64*(4*Real.pi)^2)*
        ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2))) := by
  let weight := fun top z => (T top).weight (L^(A+2)) D z
  let C := P.absoluteConstant*((64*(4*Real.pi)^2)*
    ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2))
  let mask := fun top => ((T top).mask L A z:ℂ)
  have hw (top : τ) (x : ℝ×ℝ) : 0 < weight top x :=
    (T top).weight_pos (Real.rpow_pos_of_pos (by linarith) _) D x
  have hm (top : τ) (_htop : top ∈ tops) : weight top z^(-alpha)*‖mask top‖ ≤ 1 := by
    simpa only [mask,Complex.norm_real,Real.norm_eq_abs] using
      (T top).residual_mask_weight_bound hL hD hdegree ha ha1 z
  dsimp only
  rw [P.physicalMaskedValue_eq_complex_cross alt hAlt]
  have h := grid.source_packet_residual_norm_bound tops slope precision cutoff weight hp hw hKb
    gap phase hz alpha ha z packets assigned (fun u : P.PacketIndex => u.1) stop mask
    (P.physicalCrossPacketValue alt hAlt t b v f 0 z) hassigned he 1 zero_le_one hm
    lower upper pathSlope (fun _ => C) (by
      intro j _
      exact P.physical_single_scale_cross_packets alt hAlt horder 0 j t (d j) (radius j)
        M K H (hd j) hM (hradius j) (hlocal j) b (hb j) (hbM j) (hsupport j)
        v hv f hf hf1 _ z)
  simpa only [one_mul,Finset.sum_const,nsmul_eq_mul,C] using h

omit P alt hAlt in
/-- Source stopping and the rounded block length absorb every constant
in the physical single-block estimate before a family is chosen. -/
theorem eventually_physical_shifted_residual_norm
    (q D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ K) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ M) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A w : ℝ) (hw : 0 < w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hKb : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
    ∀ (j : ℕ) (pathSlope : ℝ),
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    ‖grid.packetResidual packets (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j) (ShiftedBlocks.endpoint shift (j+1))
      (grid.index (ShiftedBlocks.endpoint shift j) pathSlope)‖ ≤ L^(2*q+3) := by
  filter_upwards [eventually_single_scale_budget q M hM K H,
    eventually_shifted_residual_length_budget,eventually_ge_atTop (max 2 D)]
    with L hconstant hcard hlarge
  have hL : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := by linarith
  have hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ) := by
    have hceil : L ≤ (⌈L⌉₊:ℝ) := Nat.le_ceil L
    have hDL : D ≤ L := (le_max_right _ _).trans hlarge
    push_cast
    linarith
  intro N κ Label Item _ _ P horder hP alt hAlt t d radius hd hradius hlocal
    b hb hbM hsupp v hv f hf hf1 τ grid tops slope precision T A w hw hbranch hKb shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he j pathSlope
  have h := P.physical_masked_residual_norm alt hAlt horder t d radius M K H hd hM hradius
    hlocal b hb hbM hsupp v hv f hf hf1 grid tops slope precision
    (grid.rootWidth/(SourceParameters.branching L)^2) T L A D hL hD hdegree
    hp hKb (grid.sourceBoundaryGap L) phase hz alpha ha ha1 z packets assigned
    (fun i => grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
      (w/P.length i) (div_pos hw (P.length_pos i))) hassigned he
    (ShiftedBlocks.endpoint shift j) (ShiftedBlocks.endpoint shift (j+1)) pathSlope
  refine h.trans ?_
  have hc := hcard N κ Label Item P grid hbranch hKb shift w hw hzero j
  have hbnd := hconstant P.absoluteConstant P.absoluteConstant_pos.le hP
  have habs := P.absoluteConstant_pos
  calc
    _ ≤ L^(2:ℝ)*L^(2*q+1) := mul_le_mul hc hbnd (by positivity)
      (Real.rpow_nonneg hL0.le _)
    _ = L^(2*q+3) := by rw [← Real.rpow_add hL0]; congr 1; ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
