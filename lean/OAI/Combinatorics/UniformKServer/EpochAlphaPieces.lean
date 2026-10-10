import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaParameterChanges
import OAI.Combinatorics.UniformKServer.EpochAlpha

namespace OAI

                                       
section

/-! Full-child formulas for the epoch primitives. They make genuinely
 changing active subtypes transparent and prove that a held coordinate has
 unchanged potential piece when A, mark and U are fixed. -/
noncomputable section
namespace UniformKServer.EpochAlphaPieces
open Finset UniformKServer.AdaptiveAlpha UniformKServer.AlphaParameterChanges
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem regular_piece (a : ι → ℝ) (A ell ct C : ℝ) (B v : ι → ℝ)
    (hs : DomainTransport.Supported (EpochParameters.active a) B) (i : EpochParameters.active a) :
    piece (EpochAlpha.regular a A ell ct C) B v i =
      LogPrimitive.primitive (Denominators.regular (SideParameters.height A (a i))) 0
        (C*ell) (∑ j, B j) ((1+ct*SideParameters.height A (a i)/ell)*B i) (v i) := by
  rw [piece_inside (EpochAlpha.regular a A ell ct C) B v i]
  change LogPrimitive.primitive _ _ _ (∑ j : EpochParameters.active a, B j) _ _ = _
  rw [DomainTransport.sum_restrict hs]
  rfl

theorem marked_piece (a : ι → ℝ) (A U ell ct C : ℝ) (o : EpochParameters.active a)
    (B v : ι → ℝ) (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (i : EpochParameters.active a) :
    piece (EpochAlpha.marked a A U ell ct C o) B v i =
      LogPrimitive.primitive
        (fun x => if i.val=o.val then Denominators.marked (U/A) x
          else Denominators.regular (SideParameters.height A (a i)) x)
        (if i.val=o.val then 1 else 0) (C*ell) (∑ j, B j)
        ((1+ct*(if i.val=o.val then U/A else SideParameters.height A (a i))/ell)*B i) (v i) := by
  rw [piece_inside (EpochAlpha.marked a A U ell ct C o) B v i]
  unfold ProportionParameters.component EpochAlpha.marked
  dsimp only
  unfold AlphaTracker.markedG AlphaTracker.markedF
  rw [DomainTransport.sum_restrict hs]
  by_cases hi : i=o
  · subst i
    simp only [ite_true]
  · have hv : i.val ≠ o.val := fun h => hi (Subtype.ext h)
    simp only [ite_eq_right hi,ite_eq_right hv]

theorem regular_same (a b : ι → ℝ) (A ell ct C : ℝ) (B v : ι → ℝ)
    (ha : DomainTransport.Supported (EpochParameters.active a) B)
    (hb : DomainTransport.Supported (EpochParameters.active b) B)
    (i : ι) (hi : a i=b i) :
    piece (EpochAlpha.regular a A ell ct C) B v i=
      piece (EpochAlpha.regular b A ell ct C) B v i := by
  by_cases ha' : i ∈ EpochParameters.active a
  · have hb' : i ∈ EpochParameters.active b := EpochParameters.mem_active.mpr
      (by simpa only [←hi] using EpochParameters.mem_active.mp ha')
    rw [regular_piece a A ell ct C B v ha ⟨i,ha'⟩,
      regular_piece b A ell ct C B v hb ⟨i,hb'⟩]
    simp only [hi]
  · have hb' : i ∉ EpochParameters.active b := by
      simpa only [EpochParameters.mem_active,←hi] using ha'
    rw [piece_outside _ _ _ _ ha',piece_outside _ _ _ _ hb']

theorem marked_same (a b : ι → ℝ) (A U ell ct C : ℝ)
    (oa : EpochParameters.active a) (ob : EpochParameters.active b) (ho : oa.val=ob.val)
    (B v : ι → ℝ) (ha : DomainTransport.Supported (EpochParameters.active a) B)
    (hb : DomainTransport.Supported (EpochParameters.active b) B)
    (i : ι) (hi : a i=b i ∨ i=oa.val) :
    piece (EpochAlpha.marked a A U ell ct C oa) B v i=
      piece (EpochAlpha.marked b A U ell ct C ob) B v i := by
  have hactive : i ∈ EpochParameters.active a ↔ i ∈ EpochParameters.active b := by
    rcases hi with he | he
    · simp only [EpochParameters.mem_active,he]
    · subst i
      exact iff_of_true oa.property (by simpa only [ho] using ob.property)
  by_cases ha' : i ∈ EpochParameters.active a
  · have hb' := hactive.mp ha'
    rw [marked_piece a A U ell ct C oa B v ha ⟨i,ha'⟩,
      marked_piece b A U ell ct C ob B v hb ⟨i,hb'⟩]
    dsimp only
    rw [←ho]
    rcases hi with he | he
    · rw [he]
    · simp only [he,ite_true]
  · rw [piece_outside _ _ _ _ ha',piece_outside _ _ _ _ (mt hactive.mpr ha')]

end UniformKServer.EpochAlphaPieces

end


end

end OAI
