import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.IdealSectionLifting

namespace OAI


                                                    
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma IdealSheafData.mem_map_of_local (I : Y.IdealSheafData) (f : Y ⟶ X)
    [QuasiCompact f] (V : X.affineOpens) (a : Γ(X,V.1))
    (h : ∀ y : Y, f y ∈ V.1 → ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ hUV : U.1 ≤ f ⁻¹ᵁ V.1, f.appLE V.1 U.1 hUV a ∈ I.ideal U) :
    a ∈ (I.map f).ideal V := by
  rw [Scheme.IdealSheafData.map,Scheme.Hom.ker_apply,RingHom.mem_ker]
  apply I.subscheme.IsSheaf.section_ext
  intro z hz
  obtain ⟨U,hzU,hUV,ha⟩ := h (I.subschemeι z) hz
  refine ⟨I.subschemeι ⁻¹ᵁ U.1,I.subschemeι.preimage_mono hUV,hzU,?_⟩
  simp only [homOfLE_leOfHom,map_zero]
  have hh : I.subschemeι.app U.1 (f.appLE V.1 U.1 hUV a) = 0 := by
    rw [← RingHom.mem_ker,I.ker_subschemeι_app U]
    exact ha
  change ((I.subschemeι ≫ f).appLE V.1 (I.subschemeι ⁻¹ᵁ U.1)
    (I.subschemeι.preimage_mono hUV)) a = 0
  have hcomp : (I.subschemeι ≫ f).appLE V.1 (I.subschemeι ⁻¹ᵁ U.1)
      (I.subschemeι.preimage_mono hUV) =
      f.appLE V.1 U.1 hUV ≫ I.subschemeι.app U.1 := by
    rw [I.subschemeι.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE I.subschemeι f V.1 U.1
      (I.subschemeι ⁻¹ᵁ U.1) hUV le_rfl).symm
  rw [hcomp]
  exact hh

theorem descended_section_ideal_power (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ)
    (hc : ((I.comap f)^n).map f = I^n)
    (M : LineBundle X) (s : O X ⟶ M.sheaf)
    (q : O Y ⟶ ((J.pow n).tensor (M.pullback f)).sheaf)
    (hq : q ≫ tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) =
      pullbackSection f s)
    (V : X.affineOpens) (eV : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme) :
    affineCoefficient V eV s ∈ I.ideal V^n := by
  change affineCoefficient V eV s ∈ (I^n).ideal V
  rw [← hc]
  apply IdealSheafData.mem_map_of_local
  obtain ⟨eF,heF⟩ := pullback_affine_coefficient f V eV
  intro y hy
  obtain ⟨W,hyW,⟨eW⟩⟩ := J.locallyRankOne y
  obtain ⟨U₀,hU₀,hyU,hUW⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ W ⊓ f ⁻¹ᵁ V.1 from ⟨hyW,hy⟩)
  let U : Y.affineOpens := ⟨U₀,hU₀⟩
  let hUV : U.1 ≤ f ⁻¹ᵁ V.1 := hUW.trans inf_le_right
  let d : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
    frameOnSmaller eW U.1 (hUW.trans inf_le_left)
  let e : (M.pullback f).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
    frameOnSmaller eF U.1 hUV
  refine ⟨U,hyU,hUV,?_⟩
  change _ ∈ ((I.comap f).ideal U)^n
  rw [IdealPullback.comap_ideal I f U V hUV,← Ideal.map_pow,
    ← ideal_power_tensor_equation f I J ι hJ (M.pullback f) n U V hUV d e,
    ← heF U hUV s,← hq]
  let inclusion : ((J.pow n).tensor (M.pullback f)).sheaf ⟶ (M.pullback f).sheaf :=
    tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n)
  let tensorLocalFrame :=
    tensorFrame (J.pow n) (M.pullback f) U.1 (idealPowerFrame J U.1 d n) e
  change affineCoefficient U e (q ≫ inclusion) ∈
    Ideal.span {affineMapCoefficient U tensorLocalFrame e inclusion}
  rw [affineCoefficient_map U tensorLocalFrame e q inclusion]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

end
end MaximalSeshadri.Geometry

end

end OAI
