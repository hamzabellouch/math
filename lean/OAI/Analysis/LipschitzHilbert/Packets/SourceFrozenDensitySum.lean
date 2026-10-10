import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenCellIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceLongCellMask
import OAI.Analysis.LipschitzHilbert.Geometry.SourceTransverseTail

namespace OAI

/-! Finite integration of the original frozen long-tree expression over
its common density masks. The exponents and cell volumes are exact. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem finite_frozen_density_integral
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ) (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hWhitney : ∀ p∈S, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2)
    (hscale : ∀ p∈S, DyadicLineGrid.scale p.1≤P.topLength)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : ℤ×ℤ → Set ℝ)
    (hOmega : ∀ p∈S, MeasurableSet (Omega p))
    (hmass : ∀ p∈S×ˢT, (volume.prod volume).real
      (partitionCell b P.width p∩(E∩u ⁻¹' Omega p.1))≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*P.width)
    (henergy : (∑ p∈S×ˢT, (1+|(p.2:ℝ)|)^412*(P.longCellSup c b p)^2*
      (DyadicLineGrid.scale p.1.1*P.width))≤E0) :
    (∀ p∈S×ˢT, IntegrableOn
      ((E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) P.width (u z) c z))
      (partitionCell b P.width p) (volume.prod volume)) ∧
    (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) P.width (u z) c z) z‖
      ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*E0*(9*P.topLength*P.width*transverseTailConstant) := by
  let mask := fun p : (ℤ×ℤ)×ℤ => E∩u ⁻¹' Omega p.1
  let m := fun p : (ℤ×ℤ)×ℤ => DyadicLineGrid.scale p.1.1*P.width
  let d := fun p : (ℤ×ℤ)×ℤ => (volume.prod volume).real (partitionCell b P.width p∩mask p)
  let w := fun p : (ℤ×ℤ)×ℤ => 1+|(p.2:ℝ)|
  have hlocal (p : (ℤ×ℤ)×ℤ) (hp : p∈S×ˢT) :=
    P.frozen_cell_integral P.width P.width_pos.le c u hu b p (mask p)
      (hE.inter ((hOmega p.1 (Finset.mem_product.mp hp).1).preimage hu))
  refine ⟨fun p hp => (hlocal p hp).1,?_⟩
  have hsum : (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(mask p).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) P.width (u z) c z) z‖
      ∂volume.prod volume)≤∑ p∈S×ˢT, P.longCellSup c b p*d p :=
    Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
  have hene : (∑ p∈S×ˢT, (P.longCellSup c b p)^2*m p*(w p)^412)≤E0 := by
    convert henergy using 1
    apply Finset.sum_congr rfl
    intro p _
    dsimp [m,w]
    ac_rfl
  have hvol : (∑ p∈S×ˢT, m p/(w p)^6)≤9*P.topLength*P.width*transverseTailConstant :=
    finite_whitney_transverse_budget (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) a P.topLength P.width
      P.topLength_pos.le P.width_pos.le (fun q _ => hcenter q) S T hWhitney hscale
  have hb := finite_density_supremum_sum (S×ˢT) (P.longCellSup c b) d m w
    (32*(2:ℝ)^203*eta) E0 (9*P.topLength*P.width*transverseTailConstant)
    (fun p _ => P.longCellSup_nonneg c b p) (fun _ _ => measureReal_nonneg)
    (fun p _ => mul_nonneg (DyadicLineGrid.scale_pos _).le P.width_pos.le)
    (fun p _ => by dsimp [w]; positivity) hE0 (by
      intro p hp
      convert hmass p hp using 1
      dsimp [m,w,d,mask]
      simp only [mul_assoc]) hene hvol
  apply le_trans _ hb
  apply pow_le_pow_left₀ _ hsum 2
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
