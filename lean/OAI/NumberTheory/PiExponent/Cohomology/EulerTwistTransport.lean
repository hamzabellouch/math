import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def pullbackMixedPowerIso (f : Y ⟶ X) (L M : LineBundle X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj ((L.pow n).tensor M).sheaf ≅
      (((L.pullback f).pow n).tensor (M.pullback f)).sheaf :=
  PiExponentSeshadri.PullbackTensor.iso f (L.pow n) M ≪≫
    moduleTensorIso (PiExponentSeshadri.PullbackTensor.powIso f L n) (Iso.refl _)

def cartierMiddlePowerIso (A L M : LineBundle X) (n : ℕ) :
    (A.tensor ((L.pow n).tensor M)).sheaf ≅
      ((L.pow n).tensor (A.tensor M)).sheaf :=
  (lineTensorAssoc A (L.pow n) M).symm ≪≫
    moduleTensorIso (moduleTensorComm A.sheaf (L.pow n).sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc (L.pow n) A M

def pullbackCartierMiddleIso (f : Y ⟶ X) (A L M : LineBundle X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf ≅
      (((L.pullback f).pow n).tensor ((A.pullback f).tensor (M.pullback f))).sheaf :=
  PiExponentSeshadri.PullbackTensor.iso f A ((L.pow n).tensor M) ≪≫
    moduleTensorIso (Iso.refl _) (pullbackMixedPowerIso f L M n) ≪≫
      cartierMiddlePowerIso (A.pullback f) (L.pullback f) (M.pullback f) n

theorem eulerCharacteristic_pullback_cartierMiddle
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (f : Y ⟶ X)
    (A L M : LineBundle X) (n r : ℕ) :
    eulerCharacteristic (f ≫ p) r
      ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf) =
    eulerCharacteristic (f ≫ p) r
      (((L.pullback f).pow n).tensor ((A.pullback f).tensor (M.pullback f))).sheaf :=
  eulerCharacteristic_iso (f ≫ p) (pullbackCartierMiddleIso f A L M n) r

theorem fwdDiff_eulerCharacteristic_left_pow_eq_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X) (r : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) :
    fwdDiff (1 : ℕ) (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  have he (n : ℕ) : eulerCharacteristic p r ((L.pow n).tensor M).sheaf =
      eulerCharacteristic p r M.sheaf := by
    obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim (L.pow n)
    exact eulerCharacteristic_iso p
      (moduleTensorIso e (Iso.refl M.sheaf) ≪≫ moduleTensorUnit M.sheaf) r
  funext n
  simp only [fwdDiff, he, sub_self, Pi.zero_apply]

end
end PiExponent.NumericalAmpleness

end OAI
