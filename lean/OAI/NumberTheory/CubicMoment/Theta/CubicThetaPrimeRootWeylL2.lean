import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierL2Products
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootLiftL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylFormula
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionSmooth

namespace OAI

/-! The exact Weyl matrix row on genuine square-integrable global
sections, viewed inside the root-cover Hilbert space. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootFiniteWeyl_formula {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFiniteFourier hp j (cubicThetaPrimeRootFiniteWeyl hp
      (cubicThetaPrimeRootFiniteFourier hp k (cubicThetaPrimeRootSmoothRestriction hp F)))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootFiniteFourier hp j
          (cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F))+
          (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
            cubicThetaPrimeRootFiniteFourier hp j
              (cubicThetaPrimeRootSmoothRestriction hp (cubicThetaInversionSmooth F))) := by
  apply Subtype.ext
  change (cubicThetaPrimeRootFiniteFourier hp j (cubicThetaPrimeRootFiniteWeyl hp
      (cubicThetaPrimeRootFiniteFourier hp k (cubicThetaPrimeRootSmoothRestriction hp F)))).val=
    (norm p:ℂ)⁻¹ •
      ((cubicThetaPrimeRootFiniteFourier hp j
        (cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F))).val+
        (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
          (cubicThetaPrimeRootFiniteFourier hp j
            (cubicThetaPrimeRootSmoothRestriction hp (cubicThetaInversionSmooth F))).val)
  have hw (X : cubicThetaPrimeRootFiniteSections hp) :
      (cubicThetaPrimeRootFiniteWeyl hp X).val=cubicThetaPrimeRootWeylSection hp X.val := rfl
  have hs (G : cubicThetaSmoothTests) : (cubicThetaPrimeRootSmoothRestriction hp G).val=
      cubicThetaPrimeRootSectionRestrict G.val := rfl
  simp only [cubicThetaPrimeRootFiniteFourier_val,hw,hs]
  exact cubicThetaPrimeRootWeyl_fourier_formula hp j k F.val

theorem cubicThetaPrimeRootWeylL2_smooth_formula {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFourierL2 hp j (cubicThetaPrimeRootWeylL2 hp
      (cubicThetaPrimeRootFourierL2 hp k
        (cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F))))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootFourierL2 hp j
          (cubicThetaPrimeRootWeylL2 hp
            (cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F)))+
          (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
            cubicThetaPrimeRootFourierL2 hp j
              (cubicThetaPrimeRootFiniteEmbedding hp
                (cubicThetaPrimeRootSmoothRestriction hp (cubicThetaInversionSmooth F)))) := by
  simp only [cubicThetaPrimeRootFourierL2_finite,cubicThetaPrimeRootWeylL2_finite]
  have he := congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
    (cubicThetaPrimeRootFiniteWeyl_formula hp j k F)
  simpa only [map_smul,map_add] using he

end CubicFirstMoment

end

end OAI
