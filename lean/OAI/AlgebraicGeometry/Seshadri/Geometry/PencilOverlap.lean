import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.SectionMaps

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}} {M : X.Modules}

lemma pencil_overlap_basic (s : Bool → (O X ⟶ M)) (i : Bool) :
    (SectionOpens.isoOpen (s i)).ι ⁻¹ᵁ SectionOpens.isoOpen (s (!i)) =
      (SectionOpens.isoOpen (s i)).toScheme.basicOpen
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) :=
  preimage_isoOpen _ _ _

lemma pencil_overlap_reciprocal (s : Bool → (O X ⟶ M)) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    let a := X.homOfLE (show U ⊓ V ≤ U from inf_le_left)
    let b := X.homOfLE (show U ⊓ V ≤ V from inf_le_right)
    a.appTop (coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))) *
      b.appTop (coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))) = 1 := by
  intro U V a b
  obtain ⟨c,hc⟩ := overlap_coefficients U.ι V.ι a b
    (by simp only [a,b, Scheme.homOfLE_ι])
    (sectionFrame (s false)) (sectionFrame (s true))
  have h0 := hc (s false)
  have h1 := hc (s true)
  have hv : b.appTop (coefficient (sectionFrame (s true))
      (restrictSection V.ι (s false))) = c := by
    simpa only [U, sectionFrame_normalized, map_one, mul_one] using h0
  rw [hv, mul_comm]
  simpa only [V, sectionFrame_normalized, map_one] using h1.symm

end
end MaximalSeshadri.Projective
end


end
end

end OAI
