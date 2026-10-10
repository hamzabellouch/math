import OAI.Analysis.KadisonKastler.ProductMatrixStages
import OAI.Analysis.KadisonKastler.PublishedModularSpectral
import OAI.Analysis.KadisonKastler.TwoRatioParameters
import OAI.Analysis.KadisonKastler.PointedMatrixProduct

namespace OAI

/-! # The pointed infinite-product construction used by the application

Blackadar, *Operator Algebras*, III.3.1.1--3 (pp.293--295), constructs
the countable pointed tensor product from the finite-site algebras and
product states. For faithful matrix states the local left and right
orbits are dense. Disjoint finite blocks have product matrix moments;
an unused block with the same site types gives `RemoteProductBlock`.

The site modular action is conjugation by the diagonal density matrix,
and the modular operator of the product is the tensor product of the
site operators: III.4.4.7--9 and III.4.5.8 (pp.316--319). Only the two
off-diagonal eigenoperators are retained below. No centralizer or core
factoriality, type classification, absorption, or stability is assumed.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- Concrete construction data for countably many sites of each of the
two fixed matrix-state types. Finite complement moments, rather than
irreducibility, are the retained input. -/
structure TwoRatioProductModel where
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [nontrivialK : Nontrivial K]
  [separableK : TopologicalSpace.SeparableSpace K]
  stages : ProductMatrixStages (H := K)
  coordinates : PointedMatrixSites stages.algebra stages.vector twoRatioSiteParameter
  lambdaSite : Generator.MatrixUnitSystem (Fin 2) (K →L[ℂ] K)
  muSite : Generator.MatrixUnitSystem (Fin 2) (K →L[ℂ] K)
  lambda_mem : lambdaSite.algebra ≤ stages.algebra.toStarSubalgebra
  mu_mem : muSite.algebra ≤ stages.algebra.toStarSubalgebra
  lambda_eigen : ∀ (m : ModularSpectralResolution stages.algebra stages.vector) (t : ℝ),
    unitaryConj (star (m.group (Multiplicative.ofAdd t))) (lambdaSite.entry 0 1) =
      regularCharacterScalar (Real.log fixedProductLambda) t • lambdaSite.entry 0 1
  mu_eigen : ∀ (m : ModularSpectralResolution stages.algebra stages.vector) (t : ℝ),
    unitaryConj (star (m.group (Multiplicative.ofAdd t))) (muSite.entry 0 1) =
      regularCharacterScalar (Real.log fixedProductMu) t • muSite.entry 0 1

attribute [instance] TwoRatioProductModel.normedK TwoRatioProductModel.innerK
  TwoRatioProductModel.completeK TwoRatioProductModel.nontrivialK TwoRatioProductModel.separableK

/-- Published pointed-product and modular tensor construction, restricted
to the concrete data above. -/
def PublishedTwoRatioProduct : Prop := Nonempty TwoRatioProductModel.{u}

end

end KadisonKastler

end OAI
