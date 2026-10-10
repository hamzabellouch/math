import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NoetherianResolutionHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRepresentationQuotients
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationFiniteDescent
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

namespace OAI

/-! # Finite generation after normal-subgroup coinvariants

The quotient group acts on the actual coinvariants of each resolution term.
When the quotient is finitely generated abelian, its noetherian group ring
makes homology finite as well. No homological tameness implication is assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem finite_rep_descent {k Q : Type} [CommRing k] [Group Q]
    (B : Rep.{0} k Q) (f : G →* Q)
    [Module.Finite k[G] (Rep.res f B).ρ.asModule] :
    Module.Finite k[Q] B.ρ.asModule := by
  let : Module k B := B.hV2
  let ρ := B.ρ
  let σ := (Rep.res f B).ρ
  have hm : ρ.asAlgebraHom.comp (MonoidAlgebra.mapDomainAlgHom k k f) =
      σ.asAlgebraHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp only [AlgHom.comp_apply, MonoidAlgebra.mapDomainAlgHom_apply,
        MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single_one]
      rfl
    · exact Subsingleton.elim _ _
  let e := σ.asModuleEquiv.trans ρ.asModuleEquiv.symm
  let F : σ.asModule →ₛₗ[MonoidAlgebra.mapDomainRingHom k f] ρ.asModule :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        apply ρ.asModuleEquiv.injective
        change σ.asAlgebraHom a (σ.asModuleEquiv x) =
          ρ.asAlgebraHom (MonoidAlgebra.mapDomain f a) (σ.asModuleEquiv x)
        have hma := AlgHom.congr_fun hm a
        exact (congrArg (fun F : Module.End k B => F (σ.asModuleEquiv x)) hma).symm }
  exact Module.Finite.of_surjective F e.surjective

theorem finite_quotientCoinvariants (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    IntegralRepresentationFinite (G ⧸ N) (A.quotientToCoinvariants N) := by
  have hep : Epi (A.toCoinvariantsMkQ N) :=
    (Rep.epi_iff_surjective _).mpr (Representation.Coinvariants.mk_surjective _)
  have h := hA.of_epi (A.toCoinvariantsMkQ N)
  exact @finite_rep_descent G _ ℤ (G ⧸ N) _ _
    (A.quotientToCoinvariants N) (QuotientGroup.mk' N) h

theorem finite_rep_shortComplex_homology {Q : Type} [CommGroup Q] [Group.FG Q]
    (S : ShortComplex (Rep.{0} ℤ Q)) (h : IntegralRepresentationFinite Q S.X₂) :
    IntegralRepresentationFinite Q S.homology := by
  let := integralAbelianGroupRing_noetherian Q
  let F := Rep.toModuleMonoidAlgebra (k := ℤ) (G := Q)
  let : Module.Finite ℤ[Q] (S.map F).X₂ := h
  have hf := module_finite_shortComplex_homology (S.map F)
  let := hf
  exact Module.Finite.equiv (S.mapHomologyIso F).toLinearEquiv

theorem finite_rep_chain_homology {Q : Type} [CommGroup Q] [Group.FG Q]
    (C : ChainComplex (Rep.{0} ℤ Q) ℕ) (i : ℕ)
    (h : IntegralRepresentationFinite Q (C.X i)) :
    IntegralRepresentationFinite Q (C.homology i) :=
  finite_rep_shortComplex_homology (C.sc i) h

instance quotientCoinvariants_additive :
    (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).Additive where
  map_add := by
    intro X Y f g
    ext x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl

theorem typeFP_quotientCoinvariants_homology
    [IsMulCommutative (G ⧸ N)] [Group.FG (G ⧸ N)] (n : ℕ) (h : TypeFP G n) :
    ∃ P : ProjectiveResolution (trivialIntegral G),
      ∀ i, i ≤ n → IntegralRepresentationFinite (G ⧸ N)
        (((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex |>.homology i) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, fun i hi => ?_⟩
  apply finite_rep_chain_homology (Q := G ⧸ N)
  exact finite_quotientCoinvariants N _ (hP i hi)

end PolycyclicRecognition

end

end OAI
