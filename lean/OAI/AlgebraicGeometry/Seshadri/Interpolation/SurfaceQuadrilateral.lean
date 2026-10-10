import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.AllSectionQuadrilateral
import OAI.AlgebraicGeometry.Seshadri.Nodal.FramedNodalDivisor

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem Surface.exists_all_section_quadrilateral (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
        ∃ hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0,
        (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
          (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
          Function.Surjective ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
          (analyticTaylor q hq).toRingHom)) ∧
        Function.Injective (analyticTaylor q hq) ∧
        (∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V) ∧
        ∀ (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
          (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
          (w : ℝ) (_ : 0 < w) (p : Exponent),
          LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
          ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
            ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
            ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d) := by
  obtain ⟨d,hd,N,s,hs,y,U,hyU,hU,eL,v,hy,hint,hdim,hcart,hsup,hsne,hsm,q,
    hR,hprime,hfn,hf0,hq0,hq,u,hu,hu0,hnode,hder,hjets,hinj,hV⟩ :=
    S.ample_integral_nodal_section_framed L hL
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  have hjets' := hjets
  rw [← hq0] at hjets'
  refine ⟨d*4,by omega,y,U,hyU,eL,q,hq0,hq,hjets',hinj,hV,?_⟩
  have hc : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) =
      sectionCombination k (doublePointQuartics s) v := by
    rw [sectionCombination_extend_zero]
    rfl
  have hn : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) ≠ 0 := by rwa [hc]
  let eM := sectionFrameOn (powerSection (s none) 4) U.1
    (hU.trans (sectionOpen_le_powerSection (s none) 4))
  have H := @generated_nodal_all_section_quadrilateral S L hL ((L.pow d).pow 4) (d*4)
    (by omega) (linePowerMul L d 4) (Option (QuarticIndex (Fin N))) inferInstance k
    (augmentedQuartics s) (augmentedQuartics_cover s hs) (fun j => j.elim 0 v) hn hint
    hdim U y hyU hsup eL eM hR q hq hjets' u hu hu0
  have coefficient_eq := congrArg
    (affineCoefficient (M := ((L.pow d).pow 4).sheaf) U eM) hc
  refine H ?_ ?_
  · filter_upwards [hnode] with point hpoint
    exact (congrArg (q point) coefficient_eq).trans hpoint
  · exact (congrArg (q 0) coefficient_eq).trans hf0
end
end MaximalSeshadri.Geometry

end

end OAI
