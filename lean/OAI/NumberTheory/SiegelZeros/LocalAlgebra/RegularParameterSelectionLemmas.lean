import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Regular.RegularSequence
import OAI.NumberTheory.SiegelZeros.EntireFunctions.RegularSequenceHomZero
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialLocalRegularParameters
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularParameterSelection
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularPrefixLocalization
import OAI.NumberTheory.SiegelZeros.Structure.FinsuppCandidates
import OAI.NumberTheory.SiegelZeros.Structure.IteratedKoszulExactness
import OAI.NumberTheory.SiegelZeros.Structure.KoszulDualInitial

namespace OAI

noncomputable section

namespace SiegelZeros

section

namespace WeightedTorusJets.RegularSequenceQuotientTail
open RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R]

theorem principal_image_eq_scalar_top (I : Ideal R) (r : R) :
    Submodule.map I.mkQ (Ideal.span ({r} : Set R)) = r • (⊤ : Submodule R (R ⧸ I)) := by
  have h : r • (⊤ : Ideal R) = Ideal.span ({r} : Set R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← h, Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]

def quotientTailEquiv (I : Ideal R) (r : R) :
    QuotSMulTop r (R ⧸ I) ≃ₗ[R] R ⧸ (I ⊔ Ideal.span ({r} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (principal_image_eq_scalar_top I r).symm).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span ({r} : Set R)))

@[simp] theorem quotientTailEquiv_mk (I : Ideal R) (r a : R) :
    quotientTailEquiv I r (Submodule.Quotient.mk (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span ({r} : Set R)) a := rfl

theorem regular_quotient_cons_iff (I : Ideal R) (r : R) (rs : List R) :
    IsRegular (R ⧸ I) (r :: rs) ↔
      IsSMulRegular (R ⧸ I) r ∧
        IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs := by
  rw [isRegular_cons_iff]
  exact and_congr_right' ((quotientTailEquiv I r).isRegular_congr rs)

theorem regular_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsRegular (R ⧸ I) (r :: rs)) :
    IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs :=
  ((regular_quotient_cons_iff I r rs).mp h).2

theorem weaklyRegular_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsWeaklyRegular (R ⧸ I) (r :: rs)) :
    IsWeaklyRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs := by
  exact ((quotientTailEquiv I r).isWeaklyRegular_congr rs).mp
    ((isWeaklyRegular_cons_iff (R ⧸ I) r rs).mp h).2

theorem regular_map_quotient_iff (I : Ideal R) (rs : List R) :
    IsRegular (R ⧸ I) (rs.map (Ideal.Quotient.mk I)) ↔
      IsRegular (R ⧸ I) rs := by
  symm
  apply (AddEquiv.refl (R ⧸ I)).isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  induction z using Submodule.Quotient.induction_on with
  | H z => rfl

theorem regular_mapped_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsRegular (R ⧸ I) ((r :: rs).map (Ideal.Quotient.mk I))) :
    IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R)))
      (rs.map (Ideal.Quotient.mk (I ⊔ Ideal.span ({r} : Set R)))) := by
  apply (regular_map_quotient_iff _ _).mpr
  exact regular_quotient_tail I r rs ((regular_map_quotient_iff I (r :: rs)).mp h)

end WeightedTorusJets.RegularSequenceQuotientTail

section

universe w v u

namespace SiegelZerosAwei.W31
open Module
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

section General
variable {C : Type u} [Category.{v} C] [Abelian C]

def projectiveResolutionOfExact (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    CategoryTheory.ProjectiveResolution M where
  complex := P
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv P M).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
      simpa [ChainComplex.toSingle₀Equiv] using! And.intro hzero hepi
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact hexact n⟩

theorem projectiveResolutionOfExact_complex (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    (projectiveResolutionOfExact P M ε hε hzero hepi hexact hproj).complex = P := rfl

variable [HasExt.{w} C]

def resolutionExtAddEquiv (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Ext M Y n ≃+
      CochainComplex.HomComplex.CohomologyClass P.cochainComplex
        ((CochainComplex.singleFunctor C 0).obj Y) n :=
  P.extAddEquivCohomologyClass

theorem ext_subsingleton_iff_cocycles_are_boundaries
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Subsingleton (Ext M Y (n + 1)) ↔
      ∀ (f : P.complex.X (n + 1) ⟶ Y),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h f hf
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (h.elim _ 0)
  · intro h
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)

theorem ext_subsingleton_of_isZero_resolution_term
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ)
    (hterm : IsZero (P.complex.X n)) : Subsingleton (Ext M Y n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hfzero : f = 0 := hterm.eq_of_src f 0
  subst f
  exact P.extMk_zero (n + 1) rfl

end General

variable {R : Type u} [CommRing R]

theorem module_exactAt_succ_of_range_eq_ker (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ)
    (h : LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom) : P.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

def finiteFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (rank : ℕ → ℕ) (basis : ∀ n : ℕ, Basis (Fin (rank n)) R (P.X n)) :
    ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => ModuleCat.projective_of_free (basis n))

def moduleFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (hfree : ∀ n : ℕ, Module.Free R (P.X n)) : ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => by
      let := hfree n
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X n)))

end SiegelZerosAwei.W31

end

section

universe u
namespace SiegelZerosAwei.W31
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {R : Type u} [CommRing R]

def regularSequenceAugmentation (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    (W30.regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs) :=
  (W30.regularSequenceComplex_exact rs hreg).choose

theorem regularSequenceAugmentation_spec (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    Function.Surjective (regularSequenceAugmentation rs hreg) ∧
    LinearMap.range ((W30.regularSequenceComplex rs).d 1 0).hom =
      LinearMap.ker (regularSequenceAugmentation rs hreg) ∧
    ∀ n, LinearMap.range ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((W30.regularSequenceComplex rs).d (n + 1) n).hom :=
  (W30.regularSequenceComplex_exact rs hreg).choose_spec

def regularSequenceResolution (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList rs)) :=
  moduleFreeResolutionOfExact (W30.regularSequenceComplex rs)
    (ModuleCat.of R (R ⧸ Ideal.ofList rs))
    (ModuleCat.ofHom (regularSequenceAugmentation rs hreg))
    (by
      apply ModuleCat.hom_ext
      exact LinearMap.range_le_ker_iff.mp (regularSequenceAugmentation_spec rs hreg).2.1.le)
    (regularSequenceAugmentation_spec rs hreg).2.1
    (regularSequenceAugmentation_spec rs hreg).1
    (regularSequenceAugmentation_spec rs hreg).2.2
    (W30.regularSequenceComplex_free rs)

theorem regularSequenceResolution_complex (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    (regularSequenceResolution rs hreg).complex = W30.regularSequenceComplex rs := rfl

def regularSequenceQuotientExtAddEquiv (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (regularSequenceResolution rs hreg).cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y) n :=
  (regularSequenceResolution rs hreg).extAddEquivCohomologyClass

theorem regularSequenceQuotientExt_iff_boundaries (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y (n + 1)) ↔
      ∀ f : (W30.regularSequenceComplex rs).X (n + 1) ⟶ Y,
        (W30.regularSequenceComplex rs).d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : (W30.regularSequenceComplex rs).X n ⟶ Y,
          (W30.regularSequenceComplex rs).d (n + 1) n ≫ g = f :=
  ext_subsingleton_iff_cocycles_are_boundaries _ Y (regularSequenceResolution rs hreg) n

theorem regularSequenceQuotientExt_above_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R)
    (n : ℕ) (hn : rs.length < n) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y n) := by
  apply ext_subsingleton_of_isZero_resolution_term _ Y (regularSequenceResolution rs hreg) n
  change IsZero ((W30.regularSequenceComplex rs).X n)
  exact ModuleCat.isZero_iff_subsingleton.mpr (W30.regularSequenceComplex_bounded rs n hn)

theorem regularSequenceQuotientExt_of_dual_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ)
    (hdual : LinearMap.range (((W30.regularSequenceComplex rs).d (n + 1) n).hom.dualMap) =
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap)) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) := by
  apply (regularSequenceQuotientExt_iff_boundaries rs hreg (ModuleCat.of R R) n).mpr
  intro f hf
  have hfker : f.hom ∈
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap) := by
    change f.hom.comp ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom = 0
    exact ModuleCat.hom_ext_iff.mp hf
  rw [← hdual] at hfker
  obtain ⟨g, hg⟩ := hfker
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  exact hg

def residueFieldExtAddEquiv [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (regularSequenceResolution rs hreg).cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y) n := by
  change Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) Y n ≃+ _
  rw [← hmax]
  exact regularSequenceQuotientExtAddEquiv rs hreg Y n

end SiegelZerosAwei.W31

namespace WeightedTorusJets.W18
open CategoryTheory CategoryTheory.Abelian
open SiegelZerosAwei

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

end WeightedTorusJets.W18

end

namespace SiegelZerosAwei.W30

section
open Module
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem iterateScalarCones_dual_low_exact (rs : List R) (n : ℕ)
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R)
    (e : P.X (n + 1) ≃ₗ[R] R)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I)
    (hreg : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    ∀ k, k + 1 < n + 1 + rs.length →
      LinearMap.range ((iterateScalarCones P rs).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((iterateScalarCones P rs).d (k + 2) (k + 1)).hom.dualMap := by
  induction rs generalizing n P I with
  | nil =>
    intro k hk
    exact hlow k (by simpa using hk)
  | cons r rs ih =>
    let P' := scalarConeComplex P r
    let I' := I ⊔ Ideal.span {r}
    let e' : P'.X (n + 2) ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv P r (n + 1) hbound).trans e
    let π : Dual R (P.X (n + 1)) →ₗ[R] (R ⧸ I) :=
      I.mkQ.comp (W31.topDualCoordinate e).toLinearMap
    have hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π :=
      coordinate_quotient_exact _ (W31.topDualCoordinate e) I hI
    have hr : IsSMulRegular (R ⧸ I) r :=
      ((RingTheory.Sequence.isRegular_cons_iff (R ⧸ I) r rs).mp hreg).1
    have htail : RingTheory.Sequence.IsRegular (R ⧸ I') rs :=
      WeightedTorusJets.RegularSequenceQuotientTail.regular_quotient_tail I r rs hreg
    have hbound' : ∀ k, n + 2 < k → Subsingleton (P'.X k) :=
      scalarCone_bounded P r (n + 1) hbound
    have hinj' : Function.Injective (P'.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective P r hinj
    have hlow' : ∀ k, k < n + 1 → LinearMap.range (P'.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P'.d (k + 2) (k + 1)).hom.dualMap :=
      scalarCone_dual_low_exact P r n π hinj hlow hπ hr
    have hI' : LinearMap.range
        ((W31.topDualCoordinate e').toLinearMap.comp (P'.d (n + 2) (n + 1)).hom.dualMap) = I' :=
      scalarCone_top_dual_image P r n hbound e I hI
    have h := ih (n + 1) P' I' e' hbound' hinj' hlow' hI' htail
    intro k hk
    exact h k (by simp only [List.length_cons] at hk; omega)

theorem regularSequenceComplex_dual_low_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    LinearMap.range ((regularSequenceComplex rs).d (n + 1) n).hom.dualMap =
      LinearMap.ker ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap := by
  cases rs with
  | nil => simp at hn
  | cons r rs =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg
    have hJ : r • (⊤ : Submodule R R) = Ideal.span ({r} : Set R) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul]
      exact Ideal.mul_top _
    change RingTheory.Sequence.IsRegular (R ⧸ (r • (⊤ : Submodule R R))) rs at htail
    rw [hJ] at htail
    let E := emptyKoszulComplex (R := R)
    have hb : ∀ k, 0 < k → Subsingleton (E.X k) :=
      fun k hk => regularSequenceComplex_bounded ([] : List R) k hk
    let P := scalarConeComplex E r
    let e : P.X 1 ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv E r 0 hb).trans (LinearEquiv.refl R R)
    have hbound : ∀ k, 1 < k → Subsingleton (P.X k) :=
      scalarCone_bounded E r 0 hb
    have hinj : Function.Injective (P.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective_of_regular E r hr
    have hlow : ∀ k, k < 0 → LinearMap.range (P.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap := by
      intro k hk
      omega
    have hI : LinearMap.range
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d 1 0).hom.dualMap) =
          Ideal.span ({r} : Set R) :=
      scalarCone_first_top_dual_image E r hb (LinearEquiv.refl R R)
    have h := iterateScalarCones_dual_low_exact rs 0 P (Ideal.span {r})
      e hbound hinj hlow hI htail
    exact h n (by simp only [List.length_cons] at hn; omega)

end

section
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R]

theorem regularSequenceQuotientExt_positive_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) :=
  W31.regularSequenceQuotientExt_of_dual_exact rs hreg n
    (regularSequenceComplex_dual_low_exact rs hreg n hn)

theorem regularSequenceQuotientExt_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) 0) := by
  let := regularSequenceQuotient_dual_subsingleton rs hreg hne
  refine ⟨fun a b => Ext.homEquiv₀.injective ?_⟩
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

theorem regularSequenceQuotientExt_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) n) := by
  cases n with
  | zero =>
    apply regularSequenceQuotientExt_zero rs hreg
    intro h
    simp [h] at hn
  | succ n => exact regularSequenceQuotientExt_positive_below_length rs hreg n hn

theorem residueFieldExt_below_regular_length [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of R R) n) := by
  change Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R R) n)
  rw [← hmax]
  exact regularSequenceQuotientExt_below_length rs hreg n hn

end

open CategoryTheory CategoryTheory.Abelian
universe u

theorem polynomialLocal_residueExt_below_height
    (K : Type u) [Field K] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (i : ℕ) (hi : (i : ℕ∞) < Q.height) :
    Subsingleton (Ext
      (ModuleCat.of (Localization.AtPrime Q)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)))
      (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) i) := by
  obtain ⟨h, hh, xs, hlen, hreg, hmax⟩ :=
    WeightedTorusJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height K n Q
  apply residueFieldExt_below_regular_length xs hreg hmax i
  rw [hlen]
  exact ENat.natCast_lt_natCast.mp (by simpa only [hh] using hi)

end SiegelZerosAwei.W30

end

universe u
open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian
namespace W58

variable (k : Type u) [Field k] (n : ℕ)
variable (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]

theorem polynomialLocal_regular_prefix_maximal_not_associated
    (rs : List (Localization.AtPrime P))
    (hreg : IsRegular (Localization.AtPrime P) rs)
    (hshort : (rs.length : ℕ∞) < P.height) :
    ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P ⧸ Ideal.ofList rs) := by
  intro hass
  obtain ⟨i, hi, hnonzero⟩ :=
    WeightedTorusJets.W18.regular_sequence_associatedPrime_ext_obstruction
      rs hreg (maximalIdeal (Localization.AtPrime P)) hass
  have hile : (i : ℕ∞) ≤ rs.length := by exact_mod_cast hi
  have hvanish := SiegelZerosAwei.W30.polynomialLocal_residueExt_below_height
    k n P i (hile.trans_lt hshort)
  change Subsingleton (Ext
    (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P)))
    (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) i) at hvanish
  exact hnonzero hvanish

variable [Infinite k]

theorem polynomialLocal_exists_constant_regular_parameters
    {J : Type*} (generators : J → Localization.AtPrime P)
    (hrad : (Ideal.span (Set.range generators)).radical =
      maximalIdeal (Localization.AtPrime P))
    (h : ℕ) (hheight : P.height = (h : ℕ∞)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular (Localization.AtPrime P)
        (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal (Localization.AtPrime P) := by
  apply exists_constant_regular_parameters_of_no_maximal_associated
    (k := k) generators hrad h
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hheight]
    rfl
  · intro rs hreg hshort
    apply polynomialLocal_regular_prefix_maximal_not_associated k n P rs hreg
    rw [hheight]
    exact_mod_cast hshort

theorem polynomialLocal_exists_constant_regular_parameters_actual_height
    {J : Type*} (generators : J → Localization.AtPrime P)
    (hrad : (Ideal.span (Set.range generators)).radical =
      maximalIdeal (Localization.AtPrime P)) :
    ∃ h : ℕ, P.height = (h : ℕ∞) ∧
      ∃ cs : List (J →₀ k), cs.length = h ∧
        IsRegular (Localization.AtPrime P)
          (cs.map (Finsupp.linearCombination k generators)) ∧
        Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
          Ideal.span (Set.range generators) ∧
        (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
          maximalIdeal (Localization.AtPrime P) := by
  obtain ⟨h, hh, _⟩ :=
    WeightedTorusJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height k n P
  exact ⟨h, hh, polynomialLocal_exists_constant_regular_parameters k n P generators hrad h hh⟩

theorem polynomialLocal_exists_degree_bounded_regular_parameters
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (d h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ d)
    (hheight : P.height = (h : ℕ∞))
    (hrad : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
        maximalIdeal (Localization.AtPrime P)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      let gs := cs.map (Finsupp.linearCombination k f)
      gs.length = h ∧
      (∀ g ∈ gs, g.totalDegree ≤ d) ∧
      Ideal.ofList gs ≤ Ideal.span (Set.range f) ∧
      IsRegular (Localization.AtPrime P)
        (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ∧
      ((Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
          maximalIdeal (Localization.AtPrime P) := by
  let φ : MvPolynomial (Fin n) k →ₐ[k] Localization.AtPrime P :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Localization.AtPrime P)
  have hgen : (Ideal.span (Set.range (φ ∘ f))).radical =
      maximalIdeal (Localization.AtPrime P) := by
    simpa only [φ, IsScalarTower.coe_toAlgHom', Ideal.map_span, ← Set.range_comp] using hrad
  obtain ⟨cs, hlen, hreg, _, hmax⟩ :=
    polynomialLocal_exists_constant_regular_parameters k n P (φ ∘ f) hgen h hheight
  have hmap : (cs.map (Finsupp.linearCombination k f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P)) =
      cs.map (Finsupp.linearCombination k (φ ∘ f)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    exact Finsupp.apply_linearCombination k φ.toLinearMap f c
  refine ⟨cs, hlen, by simpa only [List.length_map] using hlen, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact WeightedTorusJets.W22.linearCombination_totalDegree_le f c hdegree
  · apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact WeightedTorusJets.W22.linearCombination_mem_ideal f c _
      (fun j => Ideal.subset_span (Set.mem_range_self j))
  · rwa [hmap]
  · rwa [Ideal.map_ofList, hmap]

end W58

end SiegelZeros

end

end OAI
