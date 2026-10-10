import OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem exists_common_tensor_generators [IsNoetherian X]
    (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ n : ℕ, ∃ G : (H.pow n).sheaf.GeneratingSections, G.IsFiniteType ∧
      ∃ G' : (L.tensor (H.pow n)).sheaf.GeneratingSections, G'.IsFiniteType := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_power_global_generators H hH
  obtain ⟨N', hN'⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators H hH L.sheaf
  let n := max N N'
  obtain ⟨G, hG⟩ := hN n (le_max_left _ _)
  obtain ⟨G', hG'⟩ := hN' n (le_max_right _ _)
  exact ⟨n, G, hG,
    SheafOfModules.GeneratingSections.equivOfIso (moduleTwistPowerIso H L.sheaf n) G',
    ⟨hG'.finite⟩⟩

end
end PiExponent.NumericalAmpleness

end OAI
