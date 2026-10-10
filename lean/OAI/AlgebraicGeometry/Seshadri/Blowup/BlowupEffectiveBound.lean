import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupForbiddenSection
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.TwistedIdealPower

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

theorem PointBlowup.effective_twist_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} {p : Configuration S r} (B : PointBlowup S r p)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (w : ℝ) (hw : 0 ≤ w)
    (hC : ∀ C : IntegralCurve S,
      w*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (I : LineBundle B.surface.scheme) (τ : I.sheaf ⟶ O B.surface.scheme) [Mono τ]
    (k m b n : ℕ) (hn : 0 < n)
    (s : O B.surface.scheme ⟶
      ((((((L.pullback B.projection).pow k).tensor (J.pow m)).pow 1).tensor (I.pow b)).pow n).sheaf)
    (hs : s ≠ 0) : w*((r*m:ℕ):ℝ) ≤ (k:ℝ)*selfIntersection S L := by
  let P := L.pullback B.projection
  let D := (P.pow k).tensor (J.pow m)
  let ψ := twistedIdealPowerInclusion D I τ 1 b n
  let := twistedIdealPowerInclusion_mono D I τ 1 b n
  have hh : s ≫ ψ ≠ 0 := by
    intro hz
    apply hs
    apply (cancel_mono ψ).mp
    simpa only [zero_comp] using hz
  let eN : (D.pow (1*n)).sheaf ≅ (D.pow n).sheaf :=
    eqToIso (congrArg (fun t => (D.pow t).sheaf) (Nat.one_mul n))
  let sD : O B.surface.scheme ⟶ (D.pow n).sheaf := (s ≫ ψ) ≫ eN.hom
  have hsD : sD ≠ 0 := by
    intro hz
    apply hh
    apply (cancel_mono eN.hom).mp
    simpa only [zero_comp] using hz
  let e : (D.pow n).sheaf ≅
      ((J.pow (m*n)).tensor ((L.pow (k*n)).pullback B.projection)).sheaf :=
    twistIdealPowerIso P J k m n ≪≫
      moduleTensorIso (Iso.refl _) (PullbackTensor.powIso B.projection L (k*n)).symm
  have hsJ : sD ≫ e.hom ≠ 0 := by
    intro hz
    apply hsD
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hz
  have h := B.section_curve_bound S L hL J ι hJ w hw hC (k*n) (m*n)
    (sD ≫ e.hom) hsJ
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  push_cast at h ⊢
  nlinarith only [h,hnR]

end
end MaximalSeshadri.Geometry

end


end OAI
