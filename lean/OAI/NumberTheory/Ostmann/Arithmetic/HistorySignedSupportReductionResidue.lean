import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionShape

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSupportReduction
open Construction HistorySignedDecode

theorem reduced_iff_arithmetic {l : ℕ} (V : ℕ→ℕ) (outside : List ℕ)
    (h : SignedHistory l) (hi : h.PositiveIntegral) (hshape : Shape h)
    (he : h.ExactReversals) : Reduced V outside h↔ArithmeticGuards V outside h := by
  induction h with
  | leaf a =>
    simpa only [Reduced,ArithmeticGuards,and_true] using rootData_iff_arithmetic V (.leaf a) hi.1 hi.2
  | @node l a p u hp hm left right il ir =>
    rcases hi with ⟨hpos,hp0,hden,hdiv,hil,hir⟩
    rcases hshape with ⟨hrole,hperm,hlp,hrp,hlm,hrm,hls,hrs,hl,hr⟩
    rcases he with ⟨he,hel,her⟩
    have hn : NodeRelations (l+1) a p u hp hm left.root right.root :=
      ⟨hp0,hrole,hperm,hlp,hrp,hlm,hrm,hls,hrs,he⟩
    rw [Reduced,ArithmeticGuards,rootData_iff_arithmetic V (SignedHistory.node a p u hp hm left right) hpos.1 hpos.2]
    simp only [hn,true_and]
    rw [localTests_iff_arithmetic outside a p u hp hm _ _ hp0.le,
      il hil hl hel,ir hir hr her]

theorem rootCoprime_iff_projection (outside : List ℕ) (a : SignedState) (ha : a.Nonnegative) :
    RootCoprime outside a↔a.toState.Coprime outside := by
  simp only [RootCoprime,State.Coprime,State.values,SignedState.toState,
    natAbs_eq_toNat ha.1,natAbs_eq_toNat ha.2]

theorem guarded_iff_arithmetic_of_positiveIntegral {l : ℕ} (V : ℕ→ℕ) (outside : List ℕ)
    (h : SignedHistory l) (hi : h.PositiveIntegral) (hshape : Shape h)
    (he : h.ExactReversals) : Guarded V outside h↔ArithmeticGuarded V outside h := by
  have hr := rootCoprime_iff_projection outside h.root (root_nonnegative hi.nonnegative)
  have ha := reduced_iff_arithmetic V outside h hi hshape he
  constructor
  · intro hg
    exact ⟨hr.mpr hg.2.1,hi.integralGuard,ha.mp hg.2.2⟩
  · intro hg
    exact ⟨hi,hr.mp hg.1,ha.mpr hg.2.2⟩

theorem supported_iff_positiveIntegral_arithmetic (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (outside : List ℕ) (ha : Template.Matches (Template.current seed l) a.small)
    (hlarge : HistorySupportReduction.LargePrimes V (decodeHistory sources seed V l a.toState c)) :
    (decodeHistory sources seed V l a.toState c).Supported V outside↔
      (signedDecode sources seed V l a c).PositiveIntegral ∧
        ArithmeticGuarded V outside (signedDecode sources seed V l a c) := by
  have hshape := signedDecode_shape sources seed V l a c ha
  constructor
  · intro hs
    have hi := signedDecode_positiveIntegral_of_supported sources seed V l a c outside hs
    refine ⟨hi,?_⟩
    apply (guarded_iff_arithmetic_of_positiveIntegral V outside _ hi hshape
      (signedDecode_exactReversals sources seed V l a c hi)).mp
    exact (supported_iff_guarded sources seed V l a c outside hlarge).mp hs
  · rintro ⟨hi,hg⟩
    apply supported_of_guarded sources seed V l a c outside hlarge
    exact (guarded_iff_arithmetic_of_positiveIntegral V outside _ hi hshape
      (signedDecode_exactReversals sources seed V l a c hi)).mpr hg

theorem supported_iff_positiveIntegral_residue (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (outside : List ℕ) (ha : Template.Matches (Template.current seed l) a.small)
    (hlarge : HistorySupportReduction.LargePrimes V (decodeHistory sources seed V l a.toState c)) :
    (decodeHistory sources seed V l a.toState c).Supported V outside↔
      (signedDecode sources seed V l a c).PositiveIntegral ∧
        Nat.Coprime a.giantPlus.natAbs a.giantMinus.natAbs ∧
        ResidueGuarded V outside (signedDecode sources seed V l a c) := by
  rw [supported_iff_positiveIntegral_arithmetic sources seed V l a c outside ha hlarge,
    arithmeticGuarded_iff_giant_and_residue]
  simp only [signedDecode_root]

end Ostmann.Arithmetic.HistorySignedSupportReduction

end

end OAI
