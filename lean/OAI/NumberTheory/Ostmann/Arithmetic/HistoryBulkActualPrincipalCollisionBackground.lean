import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNumerics
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorActualDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorScaled

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns Filter
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkActualPrincipalBlockFamily
open HistoryBulkPrincipalCollisionError HistoryBulkActualRootReferenceFamily
local instance collisionBackgroundInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def backgroundCollisionMean (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (refs : (bg : Background C l) → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
      ∀p:Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
        Option (PrincipalCollisionReference C outside bg.2 p))
    (mask : Background C l → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
      SelectedBulkSample C l → ∀p:Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → ℝ)
    (corrected mixed guarded : Bool) : ℂ :=
  (backgroundPrior C l).cmean (fun bg=>∑i,
    collisionPrincipalMean C (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      outside bg.2 (refs bg i) (mask bg i) corrected mixed guarded)

def backgroundErrorProperty (d : Decomposition) (Bs BD Bz H : ℝ) (k : ℕ) (L : ℝ) : Prop :=
    ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀l : ℕ,∀(corrected mixed : Bool),(if corrected then l<k else l≤k) →
      ∀outside : List ℕ,outside.length≤bulkSize k L →
      (∀q∈outside,∃p:spectator.Sample,p.val=q ∧ spectator.law.mass p≠0) →
      ∀refs mask,(∀bg i u p b,0 ≤ mask bg i u p b ∧ mask bg i u p b≤1) →
      ‖backgroundCollisionMean (l:=l) C outside refs mask corrected mixed true-
        backgroundCollisionMean (l:=l) C outside refs mask corrected mixed false‖≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖backgroundCollisionMean (l:=l) C outside refs mask corrected mixed true-
        backgroundCollisionMean (l:=l) C outside refs mask corrected mixed false‖≤
          Real.exp (-H*(bulkSize k L:ℝ))

theorem selected_background_collision_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,backgroundErrorProperty d Bs BD Bz H k L := by
  filter_upwards [selected_collisionPrincipalMean_scaled_error_eventually d Bs BD Bz 0 hBs hk,
    selected_index_collision_error_eventually Bs BD Bz H hH (by omega : 0<k)] with L he hn
  intro E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl outside hlen hout refs mask hm
  have hl' : l≤k := by cases corrected <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hl <;> omega
  have hbound : ‖backgroundCollisionMean (l:=l) C outside refs mask corrected mixed true-
      backgroundCollisionMean (l:=l) C outside refs mask corrected mixed false‖≤
      (Fintype.card (Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)):ℝ)*
        Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
    unfold backgroundCollisionMean
    rw [GiantCollisionError.cmean_sub_eq]
    apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
    intro bg hbg
    have ha : (selectedNonbulkPrior C l).mass bg.2≠0 := by
      rw [backgroundPrior_mass] at hbg
      exact (mul_ne_zero_iff.mp hbg).2
    rw [←Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑_i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
          Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := he E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hl
          outside hlen hout bg.2 ha (refs bg i) (mask bg i) (hm bg i)
        simpa only [zero_mul,Real.exp_zero,mul_one] using hh
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact ⟨hbound.trans (hn l hl').1,hbound.trans (hn l hl').2⟩

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
