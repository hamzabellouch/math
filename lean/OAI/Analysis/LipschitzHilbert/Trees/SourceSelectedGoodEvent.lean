import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledSelectedVariation
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodEvents

namespace OAI

/-! The reference event of a fixed selected packet family controls its
actual stopped prefixes and every disjoint unary run at the same point. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

/-- A good reference point bounds the selected physical stopping prefix
at every angular horizon, with its original analyzing coefficients. -/
theorem selectedPhysicalPrefix_good_event_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).physicalReferenceBad (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t a b v g (fun j l u => T j l u.val)
      L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z
      (min k H)) (2*H) ≤ (L^r)^3 := by
  have hgood := (P.restrictPackets Q).physicalReferenceBad_compl_bounds
    (P.restrictedAlternate alt Q) (P.restrictedAlternate_bound alt hAlt Q)
    t a b v g (fun j l u => T j l u.val) L A e s r z hz
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have h := P.selectedPhysicalPrefix_good_bound alt hAlt t b v g T L A Q stop hstop
    (z.2-t*z.1) z.1 H hgood.2.2.le
  simpa only [hpoint] using h

/-- The same selected reference event bounds all disjoint unary runs;
there is no factor counting runs or stopping levels. -/
theorem selectedPhysicalPrefix_unary_good_event_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).physicalReferenceBad (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t a b v g (fun j l u => T j l u.val)
      L A e s r)
    {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (S : ∀ run : R.runs, UnarySegmentPartition n run.val.1 run.val.2)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (H : ℕ) (hend : level finish ≤ H) :
    (∑ i : UnaryRunSegment R S,
      intervalOscillation (P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z)
        H (level i.2.val.1) (level i.2.val.2)^3) ≤ (L^r)^3 := by
  have hgood := (P.restrictPackets Q).physicalReferenceBad_compl_bounds
    (P.restrictedAlternate alt Q) (P.restrictedAlternate_bound alt hAlt Q)
    t a b v g (fun j l u => T j l u.val) L A e s r z hz
  rw [P.selectedPhysicalPrefix_eq_restricted alt hAlt t b v g T L A Q stop z]
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have h := (P.restrictPackets Q).physical_unary_runs_variation_le
    (P.restrictedAlternate alt Q) (P.restrictedAlternate_bound alt hAlt Q)
    t b v g (fun j l u => T j l u.val) L A R S stop hstop
    (z.2-t*z.1) z.1 level hlevel H hend
  rw [hpoint] at h
  exact h.trans (pow_le_pow_left₀ (cubicVariation_nonneg _ _) hgood.2.2.le 3)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
