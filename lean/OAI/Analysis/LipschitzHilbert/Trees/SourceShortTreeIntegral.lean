import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketShortSum
import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneySummation

namespace OAI

/-! The complete finite-strip short-tree estimate for the original packet
integrals. All density tests, lattice sums and Whitney budgets are actual. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Original packet with its coefficient and original selector. -/
def ordinaryPacketValue (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (q : P.PacketIndex) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun a => coefficient q a*selector q.1 q.2.1 a (u z)*
    P.physicalPacket oldSlope q.1 q.2.1 q.2.2 a z)

/-- Sum of absolute short-packet integrals over any finite family of
actual Whitney strips is bounded by size times density times top area.
The explicit constant depends only on the fixed packet seminorm, label
multiplicity, selector bound, and short/long splitting constant. -/
theorem short_tree_finite_strip_bound (P : SourceLabeledLattice N κ Label Item)
    (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (htime : P.topLength≤tau)
    (hslope : ∀ j l, oldSlope+P.rowSlope j l ∈
      scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (horder : 205≤2*P.order) (M sigma eta : ℝ)
    (hM : 0≤M) (hsigma : 0≤sigma) (heta : 0≤eta)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (hcoefficient : ∀ q, ‖coefficient q‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l a, Measurable (selector j l a))
    (hbound : ∀ j l a s, ‖selector j l a s‖≤M)
    (hsupport : ∀ j l a s, selector j l a s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (hdensity : ∀ q, P.ordinaryDensity oldSlope cell grid w tau E u q≤eta)
    (x y CW : ℝ) (hCW : 1≤CW)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-x|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-y|≤P.width)
    (S : Finset (ℤ×ℤ))
    (hWhitney : ∀ p∈S, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2) :
    (∑ p∈S, ∑ q : P.PacketIndex, if P.length q.1≤CW*DyadicLineGrid.scale p.1 then
      (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 p.1 p.2,
        ‖ordinaryPacketValue P oldSlope coefficient selector u q z‖ ∂volume.prod volume) else 0) ≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*CW*(3:ℝ)^203*P.profileBound*M)*
        sigma*eta*P.topLength*P.width := by
  classical
  have hwidth := P.width_pos
  have hprofile := P.profileBound_pos
  have htop := P.topLength_pos
  let C := (3:ℝ)^203*P.profileBound*M*sigma*eta
  let A := C*(288*(4*Real.pi)^2*B)*CW
  let mass := fun p : ℤ×ℤ => ∑ q : P.PacketIndex,
    if P.length q.1≤CW*DyadicLineGrid.scale p.1 then
      (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 p.1 p.2,
        ‖ordinaryPacketValue P oldSlope coefficient selector u q z‖ ∂volume.prod volume) else 0
  have hC : 0≤C := by dsimp [C]; positivity
  have hCW0 : 0≤CW := zero_le_one.trans hCW
  have hnum : 0≤288*(4*Real.pi)^2*(B:ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hA : 0≤A := mul_nonneg (mul_nonneg hC hnum) hCW0
  have hlength (j : Fin N) : P.length j≤P.topLength :=
    div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hterm (p : ℤ×ℤ) (q : P.PacketIndex) :
      (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 p.1 p.2,
        ‖ordinaryPacketValue P oldSlope coefficient selector u q z‖ ∂volume.prod volume) ≤
      C*(P.length q.1*P.width*P.shortKernel p.1 p.2 q) := by
    have h := P.own_packet_whitney_density_bound oldSlope cell grid w tau q
      ((hlength q.1).trans htime) (hslope q.1 q.2.1) horder M sigma eta hM hsigma
      (coefficient q) (hcoefficient q) (selector q.1 q.2.1)
      (hselector q.1 q.2.1) (hbound q.1 q.2.1) (hsupport q.1 q.2.1)
      u hu E hE (hdensity q) p.1 p.2
    exact h.2.trans_eq (by dsimp [C,shortKernel]; ring)
  have hmass (p : ℤ×ℤ) : mass p≤C*(∑ q : P.PacketIndex,
      if P.length q.1≤CW*DyadicLineGrid.scale p.1 then P.length q.1*P.width*P.shortKernel p.1 p.2 q else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    by_cases h : P.length q.1≤CW*DyadicLineGrid.scale p.1
    · simpa only [ite_eq_left h] using hterm p q
    · simp only [ite_eq_right h,mul_zero,le_refl]
  have hsmall (p : ℤ×ℤ) (hp : p∈S) (_hsize : DyadicLineGrid.scale p.1≤P.topLength) :
      mass p≤A*P.width*DyadicLineGrid.scale p.1 := by
    have h := P.packet_short_mass_sum B hcard y (CW*DyadicLineGrid.scale p.1)
      (mul_nonneg hCW0 (scale_pos p.1).le)
      p.1 p.2 (hWhitney p hp).1 hY
    exact (hmass p).trans ((mul_le_mul_of_nonneg_left h hC).trans_eq (by dsimp [A]; ring))
  have hlarge (p : ℤ×ℤ) (hp : p∈S) (hsize : P.topLength<DyadicLineGrid.scale p.1) :
      mass p≤A*P.width*P.topLength*(P.topLength/DyadicLineGrid.scale p.1)^2 := by
    have hdrop : (∑ q : P.PacketIndex,
        if P.length q.1≤CW*DyadicLineGrid.scale p.1 then P.length q.1*P.width*P.shortKernel p.1 p.2 q else 0) ≤
        ∑ q : P.PacketIndex, P.length q.1*P.width*P.shortKernel p.1 p.2 q := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg (P.length_pos q.1).le P.width_pos.le)
          (by dsimp [shortKernel]; positivity)
    have ht := P.packet_short_mass_decay_sum B hcard y p.1 p.2 (hWhitney p hp).1 hY hsize.le
    have hbase : mass p≤C*(288*(4*Real.pi)^2*B*P.width*P.topLength*(P.topLength/DyadicLineGrid.scale p.1)^2) :=
      (hmass p).trans (mul_le_mul_of_nonneg_left (hdrop.trans ht) hC)
    have hcw := mul_le_mul_of_nonneg_left hCW
      (mul_nonneg hC (mul_nonneg (mul_nonneg (mul_nonneg hnum hwidth.le) htop.le) (sq_nonneg (P.topLength/DyadicLineGrid.scale p.1))))
    exact hbase.trans (by simpa only [mul_one] using hcw) |>.trans_eq (by dsimp [A]; ring)
  have h := sum_short_strip_bounds (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    P.topLength_pos P.width_pos.le hA (fun q _ => hX q) S hWhitney mass hsmall hlarge
  exact h.trans_eq (by dsimp [A,C]; ring)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
