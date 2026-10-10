import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveH0Finite
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PlaneModules

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme.{0}}

abbrev chartRes (k : K →+* Γ(X,⊤)) (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :=
  chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
    (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)

lemma chartRes_comp (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V W : X.Opens}
    (h : W ≤ V) (g : V ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartRes k M h (chartRes k M g m) = chartRes k M (h.trans g) m := by
  apply (chartTop k M W).injective
  rw [chartTop_nested,chartTop_nested,chartTop_nested,res_comp]

lemma chartRes_injective [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) {U W : X.Opens} (h : W ≤ U) [Nonempty W] :
    Function.Injective (chartRes k L.sheaf h) := by
  intro x y hxy
  apply (chartTop k L.sheaf U).injective
  apply L.restriction_injective (homOfLE h)
  change res k L.sheaf h (chartTop k L.sheaf U x) = res k L.sheaf h (chartTop k L.sheaf U y)
  rw [← chartTop_nested,← chartTop_nested,hxy]

lemma chartRes_range_le (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V W : X.Opens}
    (h : W ≤ V) (g : V ≤ U) :
    (chartRes k M (h.trans g)).range ≤ (chartRes k M h).range := by
  rintro _ ⟨m,rfl⟩
  exact ⟨chartRes k M g m,chartRes_comp k M h g m⟩

theorem chartRes_cross_clearing (k : K →+* Γ(X,⊤)) (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) [IsAffine U.toScheme] (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(U.toScheme,⊤))
    (ha : (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).opensRange = U.toScheme.basicOpen a)
    (m : Sections (W.ι.appTop.hom.comp k) (M.restrict W.ι) ⊤)
    (hm : m ∈ (chartRes k M hV).range) :
    ∃ n : ℕ, (X.homOfLE hU).appTop a ^ n • m ∈ (chartRes k M hU).range := by
  obtain ⟨v,rfl⟩ := hm
  let P := U ⊓ V
  have hP : W ≤ P := le_inf hU hV
  let f := X.homOfLE (show P ≤ U from inf_le_left)
  let g := X.homOfLE (show P ≤ V from inf_le_right)
  let w := chartRes k M (show P ≤ V from inf_le_right) v
  obtain ⟨n,u,hu⟩ := chartMap_clearing (U.ι.appTop.hom.comp k) (P.ι.appTop.hom.comp k)
    f (nestedBase k inf_le_left) (M.restrict U.ι) (nestedRestriction M inf_le_left) a ha w
  refine ⟨n,u,?_⟩
  have he := congrArg (chartRes k M hP) hu
  rw [chartRes_comp,chartMap_smul,map_pow,chartRes_comp] at he
  have har : (X.homOfLE hP).appTop (f.appTop a) = (X.homOfLE hU).appTop a := by
    rw [← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop]
    rw [show X.homOfLE hP ≫ f = X.homOfLE hU from Scheme.homOfLE_homOfLE X hP inf_le_left]
  simpa only [har] using he

end
end MaximalSeshadri.Geometry.BaseSections

end



end OAI
