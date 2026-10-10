import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Intersection.LocalIntersectionFormula

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.PolynomialLocalUnmixedness

section RegularPair
variable {S : Type*} [CommRing S]

def pairRelation (f g : S) : (S × S) →ₗ[S] S where
  toFun z := f * z.1 + g * z.2
  map_add' x y := by dsimp; ring
  map_smul' r x := by simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]; ring

def pairBoundary (f g : S) : S →ₗ[S] S × S where
  toFun t := (-g * t, f * t)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' r x := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul] <;> ring

theorem regular_pair_components (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    IsSMulRegular S f ∧ IsSMulRegular (S ⧸ Ideal.span {f}) g := by
  refine ⟨((RingTheory.Sequence.isRegular_cons_iff S f [g]).mp hreg).1, ?_⟩
  have hg := hreg.toIsWeaklyRegular.regular_mod_prev 1 (by simp)
  change IsSMulRegular (S ⧸ (Ideal.ofList [f] • (⊤ : Submodule S S))) g at hg
  have hideal : (Ideal.ofList [f] • (⊤ : Submodule S S)) = Ideal.span {f} := by
    change Ideal.ofList [f] * (⊤ : Ideal S) = Ideal.span {f}
    rw [Ideal.mul_top, Ideal.ofList_singleton]
  exact ((Submodule.quotEquivOfEq _ _ hideal).isSMulRegular_congr g).mp hg

theorem regular_pair_syzygy (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) (a b : S)
    (hab : f * a + g * b = 0) :
    ∃ t : S, a = -g * t ∧ b = f * t := by
  obtain ⟨hf, hg⟩ := regular_pair_components f g hreg
  have hgb : g * b ∈ Ideal.span ({f} : Set S) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-a, ?_⟩
    linear_combination hab
  have hb : b ∈ Ideal.span ({f} : Set S) :=
    mem_of_isSMulRegular_quotient_of_smul_mem hg hgb
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨t, ?_, rfl⟩
  apply hf
  change f * a = f * (-g * t)
  linear_combination hab

theorem regular_pair_range_boundary_eq_kernel (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    LinearMap.range (pairBoundary f g) = LinearMap.ker (pairRelation f g) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨t, rfl⟩
    change f * (-g * t) + g * (f * t) = 0
    ring
  · intro hz
    obtain ⟨t, ha, hb⟩ := regular_pair_syzygy f g hreg z.1 z.2 hz
    exact ⟨t, Prod.ext ha.symm hb.symm⟩

theorem regular_pair_boundary_injective (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    Function.Injective (pairBoundary f g) := by
  intro x y hxy
  apply (regular_pair_components f g hreg).1
  exact congrArg Prod.snd hxy

theorem pair_relation_range (f g : S) :
    LinearMap.range (pairRelation f g) = Ideal.ofList [f, g] := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    have hf : f ∈ Ideal.ofList [f, g] := Ideal.subset_span (by simp)
    have hg : g ∈ Ideal.ofList [f, g] := Ideal.subset_span (by simp)
    change f * a + g * b ∈ Ideal.ofList [f, g]
    exact Ideal.add_mem _ (by simpa [mul_comm] using (Ideal.ofList [f, g]).smul_mem a hf)
      (by simpa [mul_comm] using (Ideal.ofList [f, g]).smul_mem b hg)
  · apply Ideal.span_le.mpr
    intro r hr
    have hr : r = f ∨ r = g := by simpa using hr
    rcases hr with rfl | rfl
    · exact ⟨(1, 0), by simp [pairRelation]⟩
    · exact ⟨(0, 1), by simp [pairRelation]⟩

theorem pair_relation_range_eq_quotient_kernel (f g : S) :
    LinearMap.range (pairRelation f g) = LinearMap.ker (Ideal.ofList [f, g]).mkQ := by
  rw [Submodule.ker_mkQ, pair_relation_range]

def pairToIdeal (f g : S) : (S × S) →ₗ[S] Ideal.ofList [f, g] :=
  (pairRelation f g).codRestrict (Ideal.ofList [f, g]) (fun z => by
    rw [← pair_relation_range]
    exact LinearMap.mem_range_self _ _)

theorem pairToIdeal_surjective (f g : S) : Function.Surjective (pairToIdeal f g) := by
  intro x
  obtain ⟨z, hz⟩ : ∃ z, pairRelation f g z = (x : S) := by
    apply LinearMap.mem_range.mp
    rw [pair_relation_range]
    exact x.property
  exact ⟨z, Subtype.ext hz⟩

theorem regular_pair_range_boundary_eq_kernel_toIdeal (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    LinearMap.range (pairBoundary f g) = LinearMap.ker (pairToIdeal f g) := by
  simpa only [pairToIdeal, LinearMap.ker_codRestrict] using
    regular_pair_range_boundary_eq_kernel f g hreg

theorem ideal_subtype_range_eq_quotient_kernel (f g : S) :
    LinearMap.range (Ideal.ofList [f, g]).subtype =
      LinearMap.ker (Ideal.ofList [f, g]).mkQ := by
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

end RegularPair

section PolynomialLocal
variable (k : Type*) [Field k] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]

abbrev PolynomialLocal := Localization.AtPrime Q

theorem polynomial_local_regular_pair_resolution
    (f g : PolynomialLocal k n Q)
    (hreg : RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g]) :
    Function.Injective (pairBoundary f g) ∧
    LinearMap.range (pairBoundary f g) = LinearMap.ker (pairRelation f g) ∧
    LinearMap.range (pairRelation f g) = LinearMap.ker (Ideal.ofList [f, g]).mkQ ∧
    Function.Surjective (Ideal.ofList [f, g]).mkQ :=
  ⟨regular_pair_boundary_injective f g hreg,
    regular_pair_range_boundary_eq_kernel f g hreg,
    pair_relation_range_eq_quotient_kernel f g, Submodule.mkQ_surjective _⟩

theorem polynomial_local_regular_pair_dimension_drop
    (f g : PolynomialLocal k n Q)
    (hreg : RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g]) :
    ringKrullDim (PolynomialLocal k n Q ⧸ Ideal.ofList [f, g]) + 2 =
      ringKrullDim (PolynomialLocal k n Q) := by
  simpa using ringKrullDim_add_length_eq_ringKrullDim_of_isRegular [f, g] hreg

def PolynomialLocalPairUnmixednessTarget : Prop :=
  ∀ f g : PolynomialLocal k n Q,
    RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g] →
    ∀ P : Ideal (PolynomialLocal k n Q),
      IsAssociatedPrime P (PolynomialLocal k n Q ⧸ Ideal.ofList [f, g]) →
        P.height = 2

end PolynomialLocal
end WeightedTorusJets.PolynomialLocalUnmixedness

end

noncomputable section

universe w v u

namespace WeightedTorusJets.W18
open CategoryTheory CategoryTheory.Abelian

section ExactDimensionShifting
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_shortExact
    (X : C) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    (hmid : Subsingleton (Ext X S.X₂ n))
    (hleft : Subsingleton (Ext X S.X₁ (n + 1))) :
    Subsingleton (Ext X S.X₃ n) := by
  let midSubsingleton := hmid
  let leftSubsingleton := hleft
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ X hS e rfl
    (Subsingleton.elim _ 0)
  rw [Subsingleton.elim a 0, Ext.zero_comp] at ha
  exact ha.symm

theorem ext_zero_of_finite_exact_resolution
    (X : C) (K F : ℕ → C) (r : ℕ)
    (i : ∀ n, K (n + 1) ⟶ F n) (p : ∀ n, F n ⟶ K n)
    (hzero : ∀ n, i n ≫ p n = 0)
    (hexact : ∀ n < r, (ShortComplex.mk (i n) (p n) (hzero n)).ShortExact)
    (hmid : ∀ n < r, Subsingleton (Ext X (F n) n))
    (hend : Subsingleton (Ext X (K r) r)) :
    Subsingleton (Ext X (K 0) 0) := by
  exact Nat.decreasingInduction
    (motive := fun n _ => Subsingleton (Ext X (K n) n))
    (fun n hn ih => ext_subsingleton_of_shortExact X
      (ShortComplex.mk (i n) (p n) (hzero n)) (hexact n hn) n (hmid n hn) ih)
    hend (Nat.zero_le r)

theorem nonzero_ext_forces_resolution_obstruction
    (X : C) (K F : ℕ → C) (r : ℕ)
    (i : ∀ n, K (n + 1) ⟶ F n) (p : ∀ n, F n ⟶ K n)
    (hzero : ∀ n, i n ≫ p n = 0)
    (hexact : ∀ n < r, (ShortComplex.mk (i n) (p n) (hzero n)).ShortExact)
    (e : Ext X (K 0) 0) (he : e ≠ 0) :
    ¬ ((∀ n < r, Subsingleton (Ext X (F n) n)) ∧
      Subsingleton (Ext X (K r) r)) := by
  rintro ⟨hmid, hend⟩
  let zeroExt := ext_zero_of_finite_exact_resolution X K F r i p hzero hexact hmid hend
  exact he (Subsingleton.elim _ _)

theorem lengthTwo_ext_zero
    (X : C) (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (hlink : T.X₃ = S.X₁)
    (hF₀ : Subsingleton (Ext X S.X₂ 0))
    (hF₁ : Subsingleton (Ext X T.X₂ 1))
    (hF₂ : Subsingleton (Ext X T.X₁ 2)) :
    Subsingleton (Ext X S.X₃ 0) := by
  have hK : Subsingleton (Ext X T.X₃ 1) :=
    ext_subsingleton_of_shortExact X T hT 1 hF₁ hF₂
  rw [hlink] at hK
  exact ext_subsingleton_of_shortExact X S hS 0 hF₀ hK

end ExactDimensionShifting

section AssociatedPrime
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

theorem associatedPrime_nonzero_quotient_hom (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ f : R ⧸ P →ₗ[R] M, f ≠ 0 := by
  obtain ⟨hprime, f, hf⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap P M).mp hP
  let primeInstance := hprime
  refine ⟨f, ?_⟩
  intro hz
  have h10 : (1 : R ⧸ P) = 0 := hf (by simp [hz])
  exact one_ne_zero h10

theorem associatedPrime_nonzero_ext_zero (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ e : Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0, e ≠ 0 := by
  obtain ⟨f, hf⟩ := associatedPrime_nonzero_quotient_hom P hP
  refine ⟨Ext.mk₀ (ModuleCat.ofHom f), ?_⟩
  intro he
  have hh := (Ext.mk₀_eq_zero_iff (ModuleCat.ofHom f)).mp he
  exact hf (congrArg (fun g : ModuleCat.of R (R ⧸ P) ⟶ ModuleCat.of R M => g.hom) hh)

theorem not_isAssociatedPrime_of_ext_zero (P : Ideal R)
    (h : Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0)) :
    ¬ IsAssociatedPrime P M := by
  intro hP
  obtain ⟨e, he⟩ := associatedPrime_nonzero_ext_zero P hP
  exact he (h.elim e 0)

theorem associatedPrime_local_nonzero_ext_zero (P : Ideal R) [P.IsPrime]
    (hP : IsAssociatedPrime P M) :
    ∃ e : Ext
      (ModuleCat.of (Localization.AtPrime P)
        (IsLocalRing.ResidueField (Localization.AtPrime P)))
      (ModuleCat.of (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) 0,
      e ≠ 0 := by
  have hlocal : IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (LocalizedModule.AtPrime P M) :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hP
  exact associatedPrime_nonzero_ext_zero
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) hlocal

end AssociatedPrime
end WeightedTorusJets.W18

end

noncomputable section
universe w v u

namespace SiegelZerosAwei.W31
open Module
open CategoryTheory CategoryTheory.Abelian
open scoped BigOperators

section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_finite_identity_factorization
    {ι : Type*} [Fintype ι] (X F G : C) (n : ℕ)
    (p : ι → (F ⟶ G)) (j : ι → (G ⟶ F))
    (htotal : (∑ i, p i ≫ j i) = 𝟙 F)
    (h : Subsingleton (Ext X G n)) : Subsingleton (Ext X F n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (∑ i, (e.comp (Ext.mk₀ (p i)) (add_zero n)).comp
      (Ext.mk₀ (j i)) (add_zero n)) = e := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      ← Ext.comp_sum, ← Ext.mk₀_sum, htotal, Ext.comp_mk₀_id]
  calc
    e = _ := he.symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h.elim (e.comp (Ext.mk₀ (p i)) (add_zero n)) 0, Ext.zero_comp]

end General

section Modules
variable {R : Type u} [CommRing R]
variable {F : Type u} [AddCommGroup F] [Module R F]

theorem ext_subsingleton_of_finite_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R F) (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) := by
  apply ext_subsingleton_of_finite_identity_factorization X (ModuleCat.of R F)
    (ModuleCat.of R R) n
    (fun i => ModuleCat.ofHom (b.coord i))
    (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i))) ?_ h
  apply ModuleCat.hom_ext
  ext x
  simpa only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, Basis.coord_apply, LinearMap.id_apply] using
    b.sum_repr x

theorem ext_subsingleton_of_finite_free [Module.Free R F] [Module.Finite R F]
    (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) :=
  ext_subsingleton_of_finite_basis (Module.Free.chooseBasis R F) X n h

end Modules
end SiegelZerosAwei.W31

end

noncomputable section
namespace WeightedTorusJets.PolynomialLocalUnmixedness
open CategoryTheory

variable {S : Type*} [CommRing S]

def pairQuotientShortComplex (f g : S) : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk (Ideal.ofList [f, g]).subtype (Ideal.ofList [f, g]).mkQ
    (by
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero (Ideal.ofList [f, g])).mpr x.property)

def pairSyzygyShortComplex (f g : S) : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk (pairBoundary f g) (pairToIdeal f g) (by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change f * (-g * t) + g * (f * t) = 0
    ring)

theorem pairQuotientShortComplex_shortExact (f g : S) :
    (pairQuotientShortComplex f g).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact ideal_subtype_range_eq_quotient_kernel f g
  · exact (ModuleCat.mono_iff_injective _).mpr (Ideal.ofList [f, g]).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

theorem pairSyzygyShortComplex_shortExact (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    (pairSyzygyShortComplex f g).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact regular_pair_range_boundary_eq_kernel_toIdeal f g hreg
  · exact (ModuleCat.mono_iff_injective _).mpr (regular_pair_boundary_injective f g hreg)
  · exact (ModuleCat.epi_iff_surjective _).mpr (pairToIdeal_surjective f g)

theorem pair_resolution_shortComplex_link (f g : S) :
    (pairSyzygyShortComplex f g).X₃ = (pairQuotientShortComplex f g).X₁ := rfl

end WeightedTorusJets.PolynomialLocalUnmixedness

end

noncomputable section
universe u
namespace WeightedTorusJets.W18
open CategoryTheory CategoryTheory.Abelian
open WeightedTorusJets.PolynomialLocalUnmixedness

variable {S : Type u} [CommRing S]

theorem regular_pair_ext_zero (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) (X : ModuleCat.{u} S)
    (h₀ : Subsingleton (Ext X (ModuleCat.of S S) 0))
    (h₁ : Subsingleton (Ext X (ModuleCat.of S S) 1))
    (h₂ : Subsingleton (Ext X (ModuleCat.of S S) 2)) :
    Subsingleton (Ext X (ModuleCat.of S (S ⧸ Ideal.ofList [f, g])) 0) := by
  exact lengthTwo_ext_zero X (pairQuotientShortComplex f g)
    (pairSyzygyShortComplex f g) (pairQuotientShortComplex_shortExact f g)
    (pairSyzygyShortComplex_shortExact f g hreg)
    (pair_resolution_shortComplex_link f g) h₀
    (SiegelZerosAwei.W31.ext_subsingleton_of_finite_free (F := S × S) X 1 h₁) h₂

theorem regular_pair_associatedPrime_ext_obstruction [IsNoetherianRing S]
    (f g : S) (hreg : RingTheory.Sequence.IsRegular S [f, g])
    (P : Ideal S) (hP : IsAssociatedPrime P (S ⧸ Ideal.ofList [f, g])) :
    ∃ i : ℕ, i ≤ 2 ∧
      ¬ Subsingleton (Ext (ModuleCat.of S (S ⧸ P)) (ModuleCat.of S S) i) := by
  classical
  by_contra h
  have hv (i : ℕ) (hi : i ≤ 2) :
      Subsingleton (Ext (ModuleCat.of S (S ⧸ P)) (ModuleCat.of S S) i) := by
    by_contra hv
    exact h ⟨i, hi, hv⟩
  have he := regular_pair_ext_zero f g hreg (ModuleCat.of S (S ⧸ P))
    (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide))
  exact not_isAssociatedPrime_of_ext_zero P he hP

end WeightedTorusJets.W18

end

end SiegelZeros

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence
namespace SiegelZeros.W58

section Flat
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem weaklyRegular_map_of_flat [Module.Flat R S] (rs : List R)
    (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) := by
  apply (isWeaklyRegular_map_algebraMap_iff S S rs).mpr
  exact ((TensorProduct.rid R S).isWeaklyRegular_congr rs).mp
    (h.isWeaklyRegular_lTensor (M₂ := S))

theorem regular_map_of_flat_of_mem_maximalIdeal [Module.Flat R S]
    [IsLocalRing S] (rs : List R) (h : IsRegular R rs)
    (hm : ∀ r ∈ rs, algebraMap R S r ∈ maximalIdeal S) :
    IsRegular S (rs.map (algebraMap R S)) := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := S) (rs := rs.map (algebraMap R S)) ?_).mpr
  · exact weaklyRegular_map_of_flat rs h.toIsWeaklyRegular
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact hm r hr

end Flat

section LocalQuotient
variable {R : Type*} [CommRing R]
variable (L : Type*) [CommRing L] [Algebra R L]
variable (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime L P] [IsLocalRing L]

omit [IsLocalRing L] in
theorem localized_ideal_eq_map (I : Ideal R) :
    I.localized' L P.primeCompl (Algebra.linearMap R L) =
      I.map (algebraMap R L) := by
  rw [Submodule.localized'_eq_span]
  rfl

def localizedIdealQuotientEquiv (I : Ideal R) :
    (L ⧸ I.localized' L P.primeCompl (Algebra.linearMap R L)) ≃ₗ[L]
      L ⧸ I.map (algebraMap R L) :=
  Submodule.quotEquivOfEq _ _ (localized_ideal_eq_map L P I)

theorem associatedPrime_quotient_atPrime (I : Ideal R)
    (hP : IsAssociatedPrime P (R ⧸ I)) :
    IsAssociatedPrime (maximalIdeal L) (L ⧸ I.map (algebraMap R L)) := by
  apply (localizedIdealQuotientEquiv L P I).isAssociatedPrime_iff.mp
  apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      P.primeCompl (I.toLocalizedQuotient' L P.primeCompl (Algebra.linearMap R L))
  simpa only [IsLocalization.AtPrime.under_maximalIdeal L P,
    AssociatedPrimes.mem_iff] using hP

omit [P.IsPrime] in
theorem ideal_le_of_quotient_associatedPrime (I : Ideal R)
    (hP : IsAssociatedPrime P (R ⧸ I)) : I ≤ P := by
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
    hP.annihilator_le

theorem regular_list_at_associatedPrime
    (rs : List R) (hreg : IsRegular R rs)
    (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList rs)) :
    IsRegular L (rs.map (algebraMap R L)) := by
  let flatInstance : Module.Flat R L := IsLocalization.flat L P.primeCompl
  apply regular_map_of_flat_of_mem_maximalIdeal rs hreg
  intro r hr
  have hmem := ideal_le_of_quotient_associatedPrime P (Ideal.ofList rs) hP
    (Ideal.subset_span hr)
  change r ∈ (maximalIdeal L).under R
  rwa [IsLocalization.AtPrime.under_maximalIdeal L P]

end LocalQuotient

section Obstruction
variable {R : Type u} [CommRing R]
variable (L : Type u) [CommRing L] [Algebra R L] [IsNoetherianRing L]
variable (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime L P]
variable [IsLocalRing L]

theorem regular_pair_localized_ext_obstruction (f g : R)
    (hreg : IsRegular R [f, g])
    (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList [f, g])) :
    ∃ i : ℕ, i ≤ 2 ∧ ¬ Subsingleton
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of L (L ⧸ maximalIdeal L)) (ModuleCat.of L L) i) := by
  have hr := regular_list_at_associatedPrime L P [f, g] hreg hP
  have ha := associatedPrime_quotient_atPrime L P (Ideal.ofList [f, g]) hP
  rw [Ideal.map_ofList] at ha
  simp only [List.map_cons, List.map_nil] at hr ha
  exact WeightedTorusJets.W18.regular_pair_associatedPrime_ext_obstruction
    (algebraMap R L f) (algebraMap R L g) hr (maximalIdeal L) ha

end Obstruction

end SiegelZeros.W58

end

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.W16

open RingTheory.Sequence

variable {A : Type*} [CommRing A]

theorem weaklyRegular_atPrime_mono
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : IsWeaklyRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T)))) :
    IsWeaklyRegular (Localization.AtPrime Q)
      (gs.map (algebraMap A (Localization.AtPrime Q))) := by
  have hc : T.primeCompl ≤ Q.primeCompl := by
    intro a ha
    exact fun h => ha (hQT h)
  let localizationAlgebra : Algebra (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let localizationTower : IsScalarTower A (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let localizationInstance : IsLocalization
      (Q.primeCompl.map (algebraMap A (Localization.AtPrime T)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let flatInstance : Module.Flat (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.flat (Localization.AtPrime Q)
      (Q.primeCompl.map (algebraMap A (Localization.AtPrime T)))
  have hh := SiegelZeros.W58.weaklyRegular_map_of_flat
    (S := Localization.AtPrime Q)
    (gs.map (algebraMap A (Localization.AtPrime T))) hreg
  have hmaps :
      (gs.map (algebraMap A (Localization.AtPrime T))).map
        (algebraMap (Localization.AtPrime T) (Localization.AtPrime Q)) =
      gs.map (algebraMap A (Localization.AtPrime Q)) := by
    simp only [List.map_map]
    congr 1
    funext a
    exact (IsScalarTower.algebraMap_apply A
      (Localization.AtPrime T) (Localization.AtPrime Q) a).symm
  rw [hmaps] at hh
  exact hh

theorem regularPrefix_quotientMul_injective
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length) :
    Function.Injective
      (W28.LocalIntersection.quotientMul
        ((Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) gs[j])) := by
  have hw := weaklyRegular_atPrime_mono T Q hQT gs hreg.toIsWeaklyRegular
  have hm := hw.regular_mod_prev j (by simpa only [List.length_map] using hj)
  have he :
      (Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) •
        (⊤ : Submodule (Localization.AtPrime Q) (Localization.AtPrime Q))) =
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)) := by
    change Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) *
      (⊤ : Ideal (Localization.AtPrime Q)) = _
    rw [Ideal.mul_top, Ideal.map_ofList, List.map_take]
  have hm' : IsSMulRegular
      (Localization.AtPrime Q ⧸
        (Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) •
          (⊤ : Submodule (Localization.AtPrime Q) (Localization.AtPrime Q))))
      (algebraMap A (Localization.AtPrime Q) gs[j]) := by
    simpa only [List.getElem_map] using hm
  change IsSMulRegular
    (Localization.AtPrime Q ⧸
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)))
    (algebraMap A (Localization.AtPrime Q) gs[j])
  exact ((Submodule.quotEquivOfEq _ _ he).isSMulRegular_congr
    (algebraMap A (Localization.AtPrime Q) gs[j])).mp hm'

end WeightedTorusJets.W16

end

end SiegelZeros

end OAI
