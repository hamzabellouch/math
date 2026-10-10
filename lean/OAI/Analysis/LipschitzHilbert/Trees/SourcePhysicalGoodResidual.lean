import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalResidualSquare
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodEvents
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualMask

namespace OAI

/-! At a good physical reference point the original top-masked residual
blocks have a polynomial square bound, with the mask normalization
proved from the actual hierarchy weights. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- The actual good reference event discharges the error/main envelopes;
the exponent is fixed independently of the later mass cutoff. -/
theorem physical_good_reference_residual_square {τ : Type*}
    (horder : 6 ≤ P.order) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k u, ‖b j l k u‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (T : τ → SlopeBox) (L A D q r s : ℝ)
    (hL : 6 ≤ L) (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ))
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hAb : P.absoluteConstant ≤ L^q)
    (hp : ∀ top ∈ tops, 0 ≤ precision top)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (hassigned : ∀ u ∈ packets, assigned u ∈ tops)
    (he : ∀ u ∈ packets, grid.eligible cutoff (precision (assigned u)) (stop u.1))
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope R : ℝ)
    (hR : 0 ≤ R) (hRb : R ≤ L^r)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (hgood : z ∉ P.physicalReferenceBad alt hAlt t a b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (q+8) (2*q+9) s) :
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        value alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        (L^(3*q+r+10))^2 := by
  let weight := fun top z => (T top).weight (L^(A+2)) D z
  have hL0 : 0 < L := by linarith
  have hw (top : τ) (z : ℝ×ℝ) : 0 < weight top z :=
    (T top).weight_pos (Real.rpow_pos_of_pos hL0 _) D z
  have hm (top : τ) (_htop : top ∈ tops) :
      weight top z^(-alpha)*‖((T top).mask L A z:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      (T top).residual_mask_weight_bound (by linarith) hD hdegree ha ha1 z
  have hbounds := P.physicalReferenceBad_compl_bounds alt hAlt t a b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (q+8) (2*q+9) s z hgood
  have hError : P.physicalAngularError t a b v f z ≤ L^(2*q+9) :=
    hbounds.1.le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have hMain : P.physicalMainSquare t a b v f (z.2-t*z.1) z.1 ≤ L^(2*q+9) :=
    hbounds.2.1.le
  have h := P.physical_masked_packet_residual_square_polynomial alt hAlt horder t a
    b hb hb1 v hv f hf hf1 grid tops slope precision cutoff weight hp hw hK gap phase hz
    alpha ha z packets assigned stop T L A hassigned he 1 zero_le_one hm level hlevel count
    pathSlope R hR hcard 0 q (2*q+9) r hL hr (by simp) hAb hRb hError hMain
  simpa only [zero_add,show q+(2*q+9)+r+1 = 3*q+r+10 by ring] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
