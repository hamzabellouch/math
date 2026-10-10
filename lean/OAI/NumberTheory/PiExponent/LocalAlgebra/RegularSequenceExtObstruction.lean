import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer
import OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt

namespace OAI

noncomputable section
universe u
namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian
open PiExponentSiegelAux

variable {R : Type u} [CommRing R]

section RangeSequences
variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
  [Module R L] [Module R M] [Module R N]

def differentialRangeShortComplex (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.range f).subtype g.rangeRestrict (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (show x.val ∈ LinearMap.ker g from hex ▸ x.property))

theorem differentialRangeShortComplex_shortExact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) :
    (differentialRangeShortComplex f g hex).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (LinearMap.range f).subtype = LinearMap.ker g.rangeRestrict
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict, hex]
  · exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.range f).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr (LinearMap.surjective_rangeRestrict g)

def augmentationRangeShortComplex (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.range f).subtype g (by
    apply LinearMap.ext
    intro x
    exact (show x.val ∈ LinearMap.ker g from hex ▸ x.property))

theorem augmentationRangeShortComplex_shortExact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g) :
    (augmentationRangeShortComplex f g hex).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (LinearMap.range f).subtype = LinearMap.ker g
    rw [Submodule.range_subtype, hex]
  · exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.range f).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr hg

end RangeSequences

theorem ext_subsingleton_of_subsingleton_module
    {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M]
    (X : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext X (ModuleCat.of R M) n) := by
  have hid : 𝟙 (ModuleCat.of R M) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  apply subsingleton_of_forall_eq 0
  intro e
  have he := Ext.comp_mk₀_id e
  rw [hid, Ext.mk₀_zero, Ext.comp_zero] at he
  exact he.symm

def regularSequenceDifferentialRange (rs : List R) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.range ((W30.regularSequenceComplex rs).d (n + 1) n).hom)

theorem regularSequenceDifferentialRange_top_subsingleton (rs : List R) :
    Subsingleton (regularSequenceDifferentialRange rs rs.length) := by
  let := W30.regularSequenceComplex_bounded rs (rs.length + 1) (Nat.lt_succ_self _)
  apply subsingleton_of_forall_eq 0
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

theorem regular_sequence_ext_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (X : ModuleCat.{u} R)
    (hv : ∀ i ≤ rs.length, Subsingleton (Ext X (ModuleCat.of R R) i)) :
    Subsingleton (Ext X (ModuleCat.of R (R ⧸ Ideal.ofList rs)) 0) := by
  have hfree (n : ℕ) (hn : n ≤ rs.length) :
      Subsingleton (Ext X ((W30.regularSequenceComplex rs).X n) n) := by
    let := W30.regularSequenceComplex_free rs n
    let := W30.regularSequenceComplex_finite rs n
    exact W31.ext_subsingleton_of_finite_free X n (hv n hn)
  have hend : Subsingleton
      (Ext X (regularSequenceDifferentialRange rs rs.length) (rs.length + 1)) := by
    let : Subsingleton (LinearMap.range
        ((W30.regularSequenceComplex rs).d (rs.length + 1) rs.length).hom) :=
      regularSequenceDifferentialRange_top_subsingleton rs
    exact ext_subsingleton_of_subsingleton_module X (rs.length + 1)
  have hrange : Subsingleton (Ext X (regularSequenceDifferentialRange rs 0) 1) := by
    apply Nat.decreasingInduction
      (motive := fun n _ =>
        Subsingleton (Ext X (regularSequenceDifferentialRange rs n) (n + 1)))
      (fun n hn ih => ?_) hend (Nat.zero_le rs.length)
    let f := ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom
    let g := ((W30.regularSequenceComplex rs).d (n + 1) n).hom
    have hex : LinearMap.range f = LinearMap.ker g :=
      (W31.regularSequenceAugmentation_spec rs hreg).2.2 n
    exact ext_subsingleton_of_shortExact X (differentialRangeShortComplex f g hex)
      (differentialRangeShortComplex_shortExact f g hex) (n + 1)
      (hfree (n + 1) (Nat.succ_le_of_lt hn)) ih
  let f := ((W30.regularSequenceComplex rs).d 1 0).hom
  let g := W31.regularSequenceAugmentation rs hreg
  have hex : LinearMap.range f = LinearMap.ker g :=
    (W31.regularSequenceAugmentation_spec rs hreg).2.1
  exact ext_subsingleton_of_shortExact X (augmentationRangeShortComplex f g hex)
    (augmentationRangeShortComplex_shortExact f g hex
      (W31.regularSequenceAugmentation_spec rs hreg).1) 0
    (hfree 0 (Nat.zero_le _)) hrange

theorem regular_sequence_associatedPrime_ext_obstruction [IsNoetherianRing R]
    (rs : List R) (hreg : RingTheory.Sequence.IsRegular R rs)
    (P : Ideal R) (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList rs)) :
    ∃ i : ℕ, i ≤ rs.length ∧
      ¬ Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R R) i) := by
  classical
  by_contra h
  have hv (i : ℕ) (hi : i ≤ rs.length) :
      Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R R) i) := by
    by_contra hv
    exact h ⟨i, hi, hv⟩
  exact not_isAssociatedPrime_of_ext_zero P
    (regular_sequence_ext_zero rs hreg (ModuleCat.of R (R ⧸ P)) hv) hP

end PiExponentJets.W18

end

end OAI
