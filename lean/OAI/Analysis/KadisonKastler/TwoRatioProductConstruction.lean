import OAI.Analysis.KadisonKastler.TwoRatioPointedConstruction
import OAI.Analysis.KadisonKastler.ModularSiteEigen

namespace OAI

/-! # The two-ratio product

The finite and remote matrix stages are concrete products. The two
off-diagonal modular eigenvalues follow from their finite product moments
and the KMS characterization of the supplied modular resolution.
-/

namespace KadisonKastler

noncomputable section

universe u

def PointedMatrixProduct.toTwoRatioProductModel
    (P : PointedMatrixProduct.{u} twoRatioSiteParameter) : TwoRatioProductModel.{u} where
  K := P.K
  normedK := P.normedK
  innerK := P.innerK
  completeK := P.completeK
  nontrivialK := P.nontrivialK
  separableK := P.separableK
  stages := P.coordinates.twoRatioStages
  coordinates := P.coordinates.twoRatioStages_coordinates
  lambdaSite := P.coordinates.twoRatioStages_coordinates.site (Sum.inl 0)
  muSite := P.coordinates.twoRatioStages_coordinates.site (Sum.inr 0)
  lambda_mem := P.coordinates.twoRatioStages_coordinates.twoRatio_site_algebra_le _
  mu_mem := P.coordinates.twoRatioStages_coordinates.twoRatio_site_algebra_le _
  lambda_eigen := fun m t =>
    P.coordinates.twoRatioStages_coordinates.twoRatio_site_modular_star_eigen m (Sum.inl 0) t
  mu_eigen := fun m t =>
    P.coordinates.twoRatioStages_coordinates.twoRatio_site_modular_star_eigen m (Sum.inr 0) t

def concreteTwoRatioProductModel : TwoRatioProductModel.{u} :=
  twoRatioPointedProduct.toTwoRatioProductModel

/-- Blackadar, III.3.1.1--3 and III.4.4.7--9, in exactly the application scope. -/
theorem publishedTwoRatioProduct : PublishedTwoRatioProduct.{u} :=
  ⟨concreteTwoRatioProductModel⟩

end

end KadisonKastler

end OAI
