import OAI.Analysis.KadisonKastler.NormalizerLogarithm
import OAI.Analysis.KadisonKastler.TypeIIICenteredImplementer
import OAI.Analysis.KadisonKastler.TypeIIIUltraproduct
import OAI.Analysis.KadisonKastler.RestrictedInnerDerivation
import OAI.Analysis.KadisonKastler.InfinitesimalExponentiation

namespace OAI

/-! # Small exact normalizers of the type III factors used by stability

Sakai innerness, logarithms, simplicity, finite spectral centering, and
exponential factorization give small exact normalizers.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance smallNormalizerOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance smallNormalizerStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

theorem typeIII_algebra_simple
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (P : VonNeumannAlgebra H) (hP : TypeIIIFactor P) : CStarSimple (Algebra P) := by
  let _ : Nontrivial (Algebra P) := hP.algebraNontrivial
  intro I _
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ a : Algebra P, a ∈ I ∧ a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hI
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using hn a ha
  obtain ⟨a, ha, hane⟩ := hex
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr hane
  obtain ⟨v, hv, hq⟩ := typeIII_positive_compression hSpectral hCompare P hP a hpos le_rfl
  obtain ⟨b, c, _, _, hbc⟩ :=
    exists_fullness_factors_of_positive_compression a v hv (by positivity) hq
  apply I.eq_top
  rw [← hbc]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)

/-- The precise type III local factorization needed in modular correction.
Both constants are absolute. -/
theorem exists_small_typeIII_normalizer_factors
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (P : VonNeumannAlgebra H) (hP : TypeIIIFactor P)
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates (H := H) v P P)
    (hsmall : ‖(v : H →L[ℂ] H) - 1‖ < 1 / 64) :
    ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      v = a * b ∧
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤
        10 * ‖(v : H →L[ℂ] H) - 1‖ := by
  let _ : Nontrivial (Algebra P) := hP.algebraNontrivial
  let _ : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with hs | hn
    · let := hs
      exact (hP.nonzero (Subsingleton.elim _ _)).elim
    · exact hn
  obtain ⟨h, hh, hn, hrange⟩ := exists_small_normalizer_log P v hv hsmall
  obtain ⟨a, ha, hcomm⟩ := exists_selfAdjoint_ambient_correction hSakai
    (typeIII_algebra_simple hSpectral hCompare P hP) P.toStarSubalgebra.subtype
    Subtype.val_injective (h : H →L[ℂ] H) h.property
    (fun x => ⟨⟨_, hrange x x.property⟩, rfl⟩)
  have hb : (h : H →L[ℂ] H) - a.val ∈ P.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro x hx
    exact (hcomm ⟨x, hx⟩).eq.symm
  obtain ⟨a', b', ha', hb', hab, han, hbn⟩ :=
    hP.exists_bounded_selfAdjoint_split h a ha hb
  have hc : Commute (a' : H →L[ℂ] H) (b' : H →L[ℂ] H) :=
    VonNeumannAlgebra.mem_commutant_iff.mp hb' _ ha'
  refine ⟨selfAdjoint.expUnitary a', selfAdjoint.expUnitary b',
    expUnitary_mem_vonNeumann P a' ha', expUnitary_mem_vonNeumann P.commutant b' hb', ?_, ?_⟩
  · rw [← hh, hab, hc.expUnitary_add]
  · have hna := norm_expUnitary_sub_expUnitary_le a' 0
    have hnb := norm_expUnitary_sub_expUnitary_le b' 0
    simp only [selfAdjoint.expUnitary_zero, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      sub_zero] at hna hnb
    linarith

/-- The local statement consumed by normalizer averaging. -/
def SmallNormalizerFactorization (P : VonNeumannAlgebra H) : Prop :=
  ∀ v : unitary (H →L[ℂ] H), Conjugates (H := H) v P P →
    ‖(v : H →L[ℂ] H) - 1‖ < 1 / 64 →
    ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      v = a * b ∧ ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤
        10 * ‖(v : H →L[ℂ] H) - 1‖

theorem typeIII_smallNormalizerFactorization
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (P : VonNeumannAlgebra H) (hP : TypeIIIFactor P) : SmallNormalizerFactorization P :=
  exists_small_typeIII_normalizer_factors hSpectral hCompare hSakai P hP

end

end KadisonKastler

end OAI
