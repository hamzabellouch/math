import OAI.Analysis.LipschitzHilbert.Trees.SourceDemodulatedLong

namespace OAI

/-! Long-cell energy with constants independent of the carrier locations
and of the ratio between spatial and angular widths. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators FourierTransform ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem finite_demodulated_long_cell_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (s : Finset ((ℤ×ℤ)×ℤ)) (b : ℝ) (q : ℕ)
    (hWhitney : ∀ p∈s, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun a => P.actualX a.1 a.2.1 a.2.2) (fun a => P.length a.1) p.1.1 p.1.2)
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0≤cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l u k ξ η, planarAngularFourier (P.physicalPacket 0 j l u k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l u k ξ η, planarAngularFourier (P.physicalPacket 0 j l u k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ z, 0≤U z) (hUb : ∀ z, ‖U z‖≤B)
    (hU : ∀ z, polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z≤U z) :
    (∑ p∈s, (1+|(p.2:ℝ)|)^(4*q)*
      (packetNormSup (fun a : ℕ×ℕ => P.physicalLongIntervalSchwartz 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2)
        (coordinateBox (center p.1.1 p.1.2) (b+(p.2:ℝ)*P.width)
          (DyadicLineGrid.scale p.1.1/2) (P.width/2)))^2*(DyadicLineGrid.scale p.1.1*P.width))≤
      32^(2*q)*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*
        (1296*∫ z, (U z)^2 ∂volume.prod volume) := by
  let F := fun (p : (ℤ×ℤ)×ℤ) (a : ℕ×ℕ) =>
    P.physicalLongIntervalSchwartz 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2
  have hband (p : (ℤ×ℤ)×ℤ) (a : ℕ×ℕ) :=
    P.physicalLongIntervalSchwartz_demodulated_bands c a.1 a.2 (DyadicLineGrid.scale p.1.1) w
      cStar CEta Cb Cv nu (scale_pos _) hw hcStar hCEta hCb hspectrum hselector hbin
  have hFx : ∀ p∈s, ∀ a y ξ, 𝓕 (vectorHorizontalSlice (verticalDemodulation nu (F p a)) y) ξ≠0 →
      |ξ|≤((cStar+Cb*CEta)/(4*Real.pi))/(DyadicLineGrid.scale p.1.1/2) := by
    intro p _ a y ξ hξ
    have h := (hband p a).1 y ξ hξ
    convert h using 1; field_simp; ring
  have hFy : ∀ p∈s, ∀ a x η, 𝓕 (vectorVerticalSlice (verticalDemodulation nu (F p a)) x) η≠0 →
      |η|≤(Cv/(4*Real.pi))/(P.width/2) := by
    intro p _ a x η hη
    have h := (hband p a).2 x η hη
    convert h using 1; field_simp; ring
  have hFU : ∀ p∈s, ∀ a z, polynomialWeight b (2*P.width) q z.2*‖F p a z‖≤U z := by
    intro p _ a z
    apply le_trans _ (hU z)
    exact mul_le_mul_of_nonneg_left (P.physicalLongIntervalSchwartz_norm 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2 z)
      ((polynomialWeight_one_le b (2*P.width) q z.2).trans' (by norm_num))
  have h := finite_weighted_box_supremum_energy s Kx Ky (fun p a => verticalDemodulation nu (F p a)) q b P.width
    ((cStar+Cb*CEta)/(4*Real.pi)) (Cv/(4*Real.pi)) P.width_pos
    (fun p => center p.1.1 p.1.2) (fun p => DyadicLineGrid.scale p.1.1/2) (fun p => (p.2:ℝ))
    (fun p _ => div_pos (scale_pos _) (by norm_num)) hKx hKy hFx hFy (partitionCell b P.width)
    (fun p _ => partitionCell_measurable b P.width p)
    (fun p _ => partitionCell_finite b P.width p)
    (fun p _ => partitionCell_subset_box b P.width p)
    (partitionCell_disjoint (Finset.univ : Finset P.PacketIndex)
      (fun a => P.actualX a.1 a.2.1 a.2.2) (fun a => P.length a.1)
      b P.width P.width_pos (↑s) hWhitney)
    U hUm hU2 B hB hU0 hUb (by simpa only [verticalDemodulation_norm] using hFU)
  simpa only [packetNormSup_verticalDemodulation,partitionCell_area b P.width _ P.width_pos] using h


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
