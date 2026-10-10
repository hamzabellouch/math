import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} {M : X.Modules}

def restrictOpenFrame {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    M.restrict V.ι ≅ O V.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma restrictOpenFrame_coefficient_global {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictOpenFrame h e) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold restrictOpenFrame
  rw [coefficient_transport]
  rw [← restrictSection_congr (X.homOfLE_ι h) s, Category.assoc]
  have he : (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app M ≫
      ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm.hom = 𝟙 _ :=
    Iso.hom_inv_id ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M)
  rw [he, Category.comp_id]
  exact coefficient_restrict_comp (X.homOfLE h) U.ι e s

lemma frameChange_restrictOpenFrame {U V W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ O U.toScheme) (f : M.restrict V.ι ≅ O V.toScheme)
    (s : O X ⟶ M) (hs : coefficient e (restrictSection U.ι s) = 1) :
    (frameChange (restrictOpenFrame hWU e) (restrictOpenFrame hWV f) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hWV).appTop (coefficient f (restrictSection V.ι s)) := by
  have h := coefficient_change (restrictOpenFrame hWU e) (restrictOpenFrame hWV f)
    (restrictSection W.ι s)
  rw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
    hs, map_one, mul_one] at h
  exact h.symm

end
end PiExponentSeshadri.Frames

end OAI
