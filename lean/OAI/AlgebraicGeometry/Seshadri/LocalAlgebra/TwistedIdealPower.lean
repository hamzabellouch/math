import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPowerDistribution
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.PowerIdeal

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def twistIdealPowerIso (L J : LineBundle X) (a b n : ℕ) :
    (((L.pow a).tensor (J.pow b)).pow n).sheaf ≅
      ((J.pow (b*n)).tensor (L.pow (a*n))).sheaf :=
  lineTwistPower L (J.pow b) a n ≪≫
    moduleTensorIso (Iso.refl _) (linePowerMul J b n) ≪≫
      moduleTensorComm _ _

def twistedIdealPowerInclusion (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (a b n : ℕ) : (((L.pow a).tensor (J.pow b)).pow n).sheaf ⟶ (L.pow (a*n)).sheaf :=
  (twistIdealPowerIso L J a b n).hom ≫
    tensorInclusion (J.pow (b*n)) (L.pow (a*n)) (idealPowerInclusion J ι (b*n))

lemma twistedIdealPowerInclusion_mono (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    [Mono ι] (a b n : ℕ) : Mono (twistedIdealPowerInclusion L J ι a b n) := by
  let := idealPowerInclusion_mono J ι (b*n)
  let := tensorInclusion_mono (J.pow (b*n)) (L.pow (a*n)) (idealPowerInclusion J ι (b*n))
  dsimp [twistedIdealPowerInclusion]
  infer_instance

def twistedIdealPowerFrame (L J : LineBundle X) (a b n : ℕ) (U : X.Opens)
    (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : (L.pow (a*n)).sheaf.restrict U.ι ≅ O U.toScheme) :
    ((((L.pow a).tensor (J.pow b)).pow n).sheaf).restrict U.ι ≅ O U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (twistIdealPowerIso L J a b n) ≪≫
    tensorFrame (J.pow (b*n)) (L.pow (a*n)) U (idealPowerFrame J U e (b*n)) f

lemma affineMapCoefficient_iso_left {M N P : X.Modules} (U : X.affineOpens)
    (c : M ≅ N) (e : N.restrict U.1.ι ≅ O U.1.toScheme)
    (f : P.restrict U.1.ι ≅ O U.1.toScheme) (a : N ⟶ P) :
    affineMapCoefficient U ((Scheme.Modules.restrictFunctor U.1.ι).mapIso c ≪≫ e)
      f (c.hom ≫ a) = affineMapCoefficient U e f a := by
  simp only [affineMapCoefficient,Iso.trans_inv,Functor.mapIso_inv,Functor.map_comp,Category.assoc]
  rw [← Functor.map_comp_assoc,c.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp]

lemma twistedIdealPowerInclusion_ideal (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (a b n : ℕ) (U : X.affineOpens)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : (L.pow (a*n)).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U (twistedIdealPowerFrame L J a b n U.1 e f)
      f (twistedIdealPowerInclusion L J ι a b n)} =
    (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^(b*n) := by
  unfold twistedIdealPowerFrame twistedIdealPowerInclusion
  rw [affineMapCoefficient_iso_left]
  change Ideal.span {U.1.topIso.hom (endValue _)} = _
  rw [tensor_inclusion_ideal]
  exact idealPowerInclusion_ideal J ι U e (b*n)

end
end MaximalSeshadri.Geometry

end


end OAI
