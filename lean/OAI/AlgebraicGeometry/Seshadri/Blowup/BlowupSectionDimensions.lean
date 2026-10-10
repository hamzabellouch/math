import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupSectionDescent
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupLineDescent
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.PointIdealMembership
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PullbackSectionLinear
import OAI.AlgebraicGeometry.Seshadri.Jets.SectionJetDimensions

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

lemma finrank_bound_of_kernel_in_range {V W Q : Type*}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup Q]
    [Module ℂ V] [Module ℂ W] [Module ℂ Q] [Module.Finite ℂ V] [Module.Finite ℂ W]
    [Module.Finite ℂ Q] (D : W →ₗ[ℂ] V) (T : V →ₗ[ℂ] Q)
    (hD : Function.Injective D) (hT : T.ker ≤ D.range) :
    Module.finrank ℂ V ≤ Module.finrank ℂ W + Module.finrank ℂ Q := by
  have h₁ := Submodule.finrank_mono hT
  rw [LinearMap.finrank_range_of_inj hD] at h₁
  have h₂ : Module.finrank ℂ T.range ≤ Module.finrank ℂ Q := T.range.finrank_le
  have h₃ := T.finrank_range_add_finrank_ker
  omega

def sectionPostcompose {X : Scheme.{0}} (g : X ⟶ complexBase) {M N : X.Modules}
    (φ : M ⟶ N) :
    letI (P : X.Modules) : Module ℂ (O X ⟶ P) := complexSectionModule g P
    (O X ⟶ M) →ₗ[ℂ] (O X ⟶ N) := by
  let (P : X.Modules) : Module ℂ (O X ⟶ P) := complexSectionModule g P
  refine { toFun := fun s => s ≫ φ
           map_add' := fun s t => Preadditive.add_comp _ _ _ s t φ
           map_smul' := fun c s => ?_ }
  exact Linear.smul_comp _ _ _ (baseScalars g c) s φ

theorem Surface.exceptional_twist_sections_bounds (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    (A : LineBundle T.scheme) (hA : A.IsAmple)
    {r : ℕ} (p : Configuration S r) (f : T.scheme ⟶ S.scheme)
    (hf : f ≫ S.structureMap = T.structureMap)
    (hbl : IsBlowup (centreIdeal S r p) f)
    (J : LineBundle T.scheme) (ι : J.sheaf ⟶ O T.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) f J ι)
    (M : LineBundle S.scheme) (n : ℕ) :
    cohomologyDimension T.structureMap ((J.pow n).tensor (M.pullback f)).sheaf 0 ≤
      cohomologyDimension S.structureMap M.sheaf 0 ∧
    2*cohomologyDimension S.structureMap M.sheaf 0 ≤
      2*cohomologyDimension T.structureMap ((J.pow n).tensor (M.pullback f)).sheaf 0 + r*n*(n+1) := by
  classical
  have : IsProper (f ≫ S.structureMap) := by rw [hf]; infer_instance
  have : IsProper f := IsProper.of_comp f S.structureMap
  have := S.blowup_structureMap_isIso p hbl
  have hmono : Mono (C := T.scheme.Modules) (idealPowerInclusion J ι n) :=
    @idealPowerInclusion_mono T.scheme J ι hJ.1 n
  have : Mono (C := T.scheme.Modules)
      (tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n)) :=
    @tensorInclusion_mono T.scheme (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) hmono
  let B := (J.pow n).tensor (M.pullback f)
  let φ := tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n)
  let (P : S.scheme.Modules) : Module ℂ (O S.scheme ⟶ P) := complexSectionModule S.structureMap P
  let (P : T.scheme.Modules) : Module ℂ (O T.scheme ⟶ P) := complexSectionModule T.structureMap P
  have : Module.Finite ℂ (O S.scheme ⟶ M.sheaf) := S.sections_finite L hL M
  have : Module.Finite ℂ (O T.scheme ⟶ B.sheaf) := T.sections_finite A hA B
  let E := LinearEquiv.ofBijective (pullbackSectionLinear S.structureMap T.structureMap f hf M)
    (M.pullbackSection_bijective f)
  let D : (O T.scheme ⟶ B.sheaf) →ₗ[ℂ] (O S.scheme ⟶ M.sheaf) :=
    E.symm.toLinearMap.comp (sectionPostcompose T.structureMap φ)
  have hD : Function.Injective D := E.symm.injective.comp (fun a b h => (cancel_mono φ).mp h)
  have hS : Module.finrank ℂ (O S.scheme ⟶ M.sheaf) = cohomologyDimension S.structureMap M.sheaf 0 := S.sections_finrank M
  have hT : Module.finrank ℂ (O T.scheme ⟶ B.sheaf) = cohomologyDimension T.structureMap B.sheaf 0 := T.sections_finrank B
  have hup := LinearMap.finrank_le_finrank_of_injective hD
  rw [hS,hT] at hup
  refine ⟨hup,?_⟩
  choose U hp hU e t het using fun i : Fin r => S.etale_line_frame_inside M ⊤
    (p.val i).image (by trivial)
  choose ρ hρ using fun i => affineComplexPoint_factor S.structureMap (U i) (p.val i) (hp i)
  let (i : Fin r) : Algebra ℂ Γ(S.scheme,(U i).1) := (openScalars S.structureMap (U i).1).toAlgebra
  choose K hK using fun i => finite_affine_jet_test (t i) (het i) (ρ i) n
  let F : (O S.scheme ⟶ M.sheaf) →ₗ[ℂ] (Fin r → JetIndex (Fin 2) n → ℂ) :=
    LinearMap.pi fun i => (K i).comp (affineCoefficientLinear S.structureMap (U i) (e i))
  have hker : F.ker ≤ D.range := by
    intro s hs
    have hs' : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^n := by
      intro i
      apply (hK i _).mp
      exact congrFun hs i
    obtain ⟨q,hq,-⟩ := lift_section_of_local_ideal_power f (centreIdeal S r p) J ι hJ M n s
      (centre_local_power_membership S p M n s U e ρ hρ hs')
    refine ⟨q,?_⟩
    exact (congrArg E.symm.toFun hq).trans (E.symm_apply_apply s)
  have H := finrank_bound_of_kernel_in_range D F hD hker
  rw [hS,hT] at H
  have hdim : 2*Module.finrank ℂ (Fin r → JetIndex (Fin 2) n → ℂ) = r*n*(n+1) := by
    let : Fintype (JetIndex (Fin 2) n) := Fintype.ofFinite _
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn := card_binaryJet n
    simp only [Nat.card_eq_fintype_card] at hn
    nlinarith
  change 2*cohomologyDimension S.structureMap M.sheaf 0 ≤
    2*cohomologyDimension T.structureMap B.sheaf 0 + r*n*(n+1)
  omega

end
end MaximalSeshadri.Geometry

end

end OAI
