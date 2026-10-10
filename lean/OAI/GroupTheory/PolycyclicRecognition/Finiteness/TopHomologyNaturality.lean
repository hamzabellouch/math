import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareTopHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ResolutionHomologyNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TopHomologyKernelNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularCoefficientNaturality

namespace OAI

/-! # Coefficient naturality of top-dimensional duality

Use one fixed resolution comparison for all coefficients. This records the
naturality needed to turn a coefficient trace into a top-homology trace.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

private theorem tensor_top_d_zero
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hbound : IsZero (P.complex.X (n + 1))) (A : Rep ℤ G) :
    (P.complex.coinvariantsTensorObj A).d (n + 1) n = 0 := by
  change ((Rep.coinvariantsTensor ℤ G).obj A).map (P.complex.d (n + 1) n) = 0
  rw [hbound.eq_of_src (P.complex.d (n + 1) n) 0, Functor.map_zero]

def naturalTopHomologyEquiv [DecidableEq G]
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hfin : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hbound : IsZero (P.complex.X (n + 1))) (A : Rep ℤ G) :
    groupHomology A n ≃ₗ[ℤ]
      (cokernel (regularDualMap (P.complex.d n (n - 1))) ⟶ A) := by
  let e := (coefficientNaturalHomologyIso P A n).toLinearEquiv.toAddEquiv.trans
    ((topHomologyKernelEquiv (P.complex.coinvariantsTensorObj A) n
      (tensor_top_d_zero P n hbound A)).toAddEquiv.trans
        (regularKernelCokernelEquiv (P.complex.d n (n - 1)) A
          (hfin n) (hfin (n - 1))).toAddEquiv)
  exact { e with map_smul' := fun r x => map_intCast_smul e ℤ ℤ r x }

theorem naturalTopHomologyEquiv_naturality [DecidableEq G]
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hfin : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hbound : IsZero (P.complex.X (n + 1))) {A B : Rep ℤ G}
    (f : A ⟶ B) (x : groupHomology A n) :
    naturalTopHomologyEquiv P n hfin hbound B
        (groupHomology.map (MonoidHom.id G) f n x) =
      naturalTopHomologyEquiv P n hfin hbound A x ≫ f := by
  apply regularKernelCokernelEquiv_coefficient
  have he := congrArg (fun k => k x) (coefficientNaturalHomologyIso_naturality P f n)
  change (coefficientNaturalHomologyIso P B n).hom
      (groupHomology.map (MonoidHom.id G) f n x) =
    homologyMap (coefficientTensorChainMap P.complex f) n
      ((coefficientNaturalHomologyIso P A n).hom x) at he
  change (topHomologyKernelEquiv (P.complex.coinvariantsTensorObj B) n
      (tensor_top_d_zero P n hbound B)
      ((coefficientNaturalHomologyIso P B n).hom
        (groupHomology.map (MonoidHom.id G) f n x))).val =
    (coefficientTensorChainMap P.complex f).f n
      (topHomologyKernelEquiv (P.complex.coinvariantsTensorObj A) n
        (tensor_top_d_zero P n hbound A)
        ((coefficientNaturalHomologyIso P A n).hom x)).val
  rw [he]
  exact topHomologyKernelEquiv_naturality (coefficientTensorChainMap P.complex f) n
    (tensor_top_d_zero P n hbound A) (tensor_top_d_zero P n hbound B)
    ((coefficientNaturalHomologyIso P A n).hom x)

theorem IsIntegralPoincareDualityGroup.topHomology_natural {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ (D : Rep ℤ G) (_ : Nonempty (D.V ≃ₗ[ℤ] ℤ))
      (e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A)),
      ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
        e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f := by
  classical
  obtain ⟨P, _, hfin, _⟩ := hG.1
  let := hG.cohomologicalDimension
  let Q := finiteProjectiveResolution P n
  have hQfin : ∀ i, IntegralRepresentationFinite G (Q.complex.X i) :=
    finiteTruncation_finite P n (fun i _ => hfin i)
  have hQbound : IsZero (Q.complex.X (n + 1)) :=
    finiteTruncation_isZero P n (n + 1) (by omega)
  let D := cokernel (regularDualMap (Q.complex.d n (n - 1)))
  obtain ⟨e⟩ := hG.2.2
  refine ⟨D, ⟨((regularDualCokernelCohomologyIso Q n hQbound).trans e).toLinearEquiv⟩,
    naturalTopHomologyEquiv Q n hQfin hQbound, ?_⟩
  exact fun A B f x => naturalTopHomologyEquiv_naturality Q n hQfin hQbound f x

end PolycyclicRecognition

end

end OAI
