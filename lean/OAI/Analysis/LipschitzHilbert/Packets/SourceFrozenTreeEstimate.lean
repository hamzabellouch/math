import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenTreeGlobal
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedTreeMaximal

namespace OAI

/-! The frozen long-tree estimate with the actual density masks and
reproducing kernels constructed. Its only published analytic input is
scalar Lépingle; the coefficient-size hypothesis is the ordinary tree size. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney

theorem exists_frozen_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (a b tau eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      P.topLength≤tau → 0≤eta → 0≤sigma →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q : P.PacketIndex, 0∈scaledAngularCell (P.width/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤P.width*η ∧ P.width*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*P.width/P.length j) →
      (∀ j l v, c j l v≠0 → cb*P.width/P.length j≤|P.rowSlope j l|) →
      (∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width)≤
        sigma^2*(P.topLength*P.width) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q, P.ordinaryDensity 0 cell grid P.width tau E u q≤eta) →
    ∃ Omega : P.DensityWhitneyCell → Set ℝ,
      (∀ i, MeasurableSet (Omega i)) ∧
      (∀ i, ¬P.HasLongPacket i → Omega i=∅) ∧
      (∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
        scaledAngularCell (P.width/P.topLength) grid q.1.val (cell q.1 q.2.1)⊆Omega i) ∧
      (∀ i n, (volume.prod volume).real
        (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) ∧
      Integrable (P.frozenTreeValue hne c E u Omega) (volume.prod volume) ∧
      (∫ z, ‖P.frozenTreeValue hne c E u Omega z‖ ∂volume.prod volume)≤
        Real.sqrt (C*(B:ℝ))*P.absoluteConstant*eta*sigma*(P.topLength*P.width) := by
  obtain ⟨CV,hCV,hvariation⟩ := exists_supported_transverse_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  let Rx := (CEta*Cb+cStar)/(4*Real.pi)
  let Ry := CEta/(4*Real.pi)
  have hRx : 0≤Rx := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  have hRy : 0≤Ry := div_nonneg hCEta (by positivity)
  obtain ⟨Kx,hKx⟩ := exists_schwartz_reproducing_kernel (Rx+1) (by linarith)
  obtain ⟨Ky,hKy⟩ := exists_schwartz_reproducing_kernel (Ry+1) (by linarith)
  let A := (32*(2:ℝ)^203)^2*
    (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*CV)*
    (9*transverseTailConstant)
  have hA : 0≤A := mul_nonneg (mul_nonneg (sq_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 206)
      (sq_nonneg _)) (by norm_num)) hCV.le))
    (mul_nonneg (by norm_num) transverseTailConstant_nonneg)
  refine ⟨A+1,by linarith,?_⟩
  intro N κ Label Item _ _ P B hcard horder hne c a b tau eta sigma cell grid
    htime heta hsigma hX hY href hspectrum hselector hlower hsize E hE u hu hdensity
  obtain ⟨Omega,hOm,hEmpty,hcontains,hmass⟩ := P.exists_whitney_masks b cell grid tau
    htime hY href E hE u hu eta heta hdensity
  have hZ (j : Fin N) (l : P.labels j) (v : Item j l) : |P.actualZ j l v-b|≤P.width :=
    (hY ⟨j,⟨l,v⟩⟩).trans (by linarith [P.width_pos])
  have hspectrum' : ∀ j l v k ξ η,
      planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+(0+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤P.width*η ∧ P.width*η≤CEta := by
    simpa only [zero_add] using hspectrum
  obtain ⟨hI,hEnergy⟩ := hvariation N κ Label Item P B hcard 0 P.width b
    P.width_pos horder c hZ hspectrum' (fun j l v hv => ⟨hlower j l v hv,hselector j l⟩)
  let mass := ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width
  let E0 := (B:ℝ)*CV*P.absoluteConstant^2*mass
  have hmass0 : 0≤mass := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
    Finset.sum_nonneg fun v _ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (P.length_pos j).le) P.width_pos.le
  have hE0 : 0≤E0 := mul_nonneg (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg B) hCV.le) (sq_nonneg _)) hmass0
  have hbound := P.frozen_tree_integrable_bound hne c a b eta E0 hE0 hX E hE u hu
    Omega hOm hEmpty hmass cStar cEta CEta Cb hcStar hcEta hCEta hCb hspectrum
    hselector
    Kx Ky (fun ξ hξ => hKx ξ (hξ.trans (by dsimp [Rx]; linarith)))
    (fun η hη => hKy η (hη.trans (by dsimp [Ry]; linarith)))
    (by simpa only [zero_mul,sub_zero] using hI)
    (by simpa only [zero_mul,sub_zero,E0,mass] using hEnergy)
  refine ⟨Omega,hOm,hEmpty,hcontains,hmass,hbound.1,hbound.2.trans ?_⟩
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      P.absoluteConstant_pos.le) heta) hsigma) (mul_pos P.topLength_pos P.width_pos).le
  · have harea : 0≤P.topLength*P.width := (mul_pos P.topLength_pos P.width_pos).le
    have hfactor : 0≤(A+1)*(B:ℝ)*P.absoluteConstant^2*eta^2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg B))
        (sq_nonneg _)) (sq_nonneg _)
    calc
      _ = A*(B:ℝ)*P.absoluteConstant^2*eta^2*mass*(P.topLength*P.width) := by
        dsimp only [A,E0]
        simp only [mul_pow]
        simp only [mul_assoc,mul_comm,mul_left_comm]
      _ ≤ (A+1)*(B:ℝ)*P.absoluteConstant^2*eta^2*mass*(P.topLength*P.width) := by
        gcongr; linarith
      _ ≤ (A+1)*(B:ℝ)*P.absoluteConstant^2*eta^2*
          (sigma^2*(P.topLength*P.width))*(P.topLength*P.width) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hfactor)
          (mul_pos P.topLength_pos P.width_pos).le
      _ = _ := by
        rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt
          (mul_nonneg (by linarith : 0≤A+1) (Nat.cast_nonneg B))]
        simp only [pow_two]
        simp only [mul_assoc,mul_comm,mul_left_comm]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
