import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
attribute [local instance] Classical.propDecidable
local instance outerBackgroundMassInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

@[simp] theorem backgroundPrior_mass (bg : Background C l) :
    (backgroundPrior C l).mass bg =
      (∏q : Bool,C.giant.law.mass (bg.1 q))*(selectedNonbulkPrior C l).mass bg.2 := rfl

theorem outerMass_eq_background_mass
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    outerMass C l p o =
      (backgroundPrior C l).mass (outerGiants C l p o,outerNonbulk C l p o) *
        ∏q : Block p,biasedBlockWeight C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q
          (outerBlocks C l p o q) := rfl

@[simp] theorem outerMass_restoreOuterBackground (bg : Background C l)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    outerMass C l p (restoreOuterBackground C l p bg b) =
      (backgroundPrior C l).mass bg *
        ∏q : Block p,biasedBlockWeight C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (b q) := rfl

@[simp] theorem outerBackgroundEquiv_symm_apply (bg : Background C l)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    (outerBackgroundEquiv C l p).symm (bg,b)=restoreOuterBackground C l p bg b := rfl

theorem sum_outer_eq_background_blocks {A : Type*} [AddCommMonoid A]
    (F : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p → A) :
    (∑o,F o)=∑bg : Background C l,∑b,F (restoreOuterBackground C l p bg b) := by
  simpa only [Fintype.sum_prod_type,outerBackgroundEquiv_symm_apply] using
    ((outerBackgroundEquiv C l p).symm.sum_comp F).symm

theorem outer_weighted_sum_eq_background_cmean
    (F : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p → ℂ) :
    (∑o,(outerMass C l p o:ℂ)*F o) =
      (backgroundPrior C l).cmean (fun bg=>∑b,
        ((∏q : Block p,biasedBlockWeight C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (b q)):ℂ)*
          F (restoreOuterBackground C l p bg b)) := by
  rw [sum_outer_eq_background_blocks C l p]
  simp only [outerMass_restoreOuterBackground,FinitePrior.cmean,Complex.ofReal_mul,Complex.ofReal_prod,
    Finset.mul_sum,mul_assoc]

theorem outer_weighted_sum_eq_background_mean
    (F : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p → ℝ) :
    (∑o,outerMass C l p o*F o) =
      (backgroundPrior C l).mean (fun bg=>∑b,
        (∏q : Block p,biasedBlockWeight C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (b q))*
          F (restoreOuterBackground C l p bg b)) := by
  rw [sum_outer_eq_background_blocks C l p]
  simp only [outerMass_restoreOuterBackground,FinitePrior.mean,Finset.mul_sum,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
