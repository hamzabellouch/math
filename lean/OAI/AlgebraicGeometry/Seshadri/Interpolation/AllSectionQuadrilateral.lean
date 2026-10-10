import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfacePositiveSquare
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalNumericalDegree
import OAI.AlgebraicGeometry.Seshadri.Divisors.MaximalCartierIso
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalAssociated

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.NodalLocal
open MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison
open scoped Topology

theorem generated_nodal_all_section_quadrilateral (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hDim : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1)
    (hyI : y ∈ (sectionIdeal k s hs v).support)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let g := affineCoefficient U eM (sectionCombination k s v)
    ∀ (q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
      (hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0)
      (_ : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
        Function.Surjective ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
      (u : (ℂ × ℂ) → ℂ) (_ : AnalyticAt ℂ u 0) (_ : u 0 ≠ 0)
      (_ : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (_ : q 0 g = 0)
      (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
      (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (w : ℝ) (_ : 0 < w) (p : Exponent),
      LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
      ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
        ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
        ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d) := by
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  let g := affineCoefficient U eM (sectionCombination k s v)
  dsimp only
  intro q hq hjets u hu hu0 hg hg0 a ha t ht eA w hw p hp
  let I := sectionIdeal k s hs v
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  have hy : y ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hyI
  obtain ⟨z,hz⟩ := hy
  let : Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme :=
    ⟨⟨z,by change I.subschemeι z ∈ U.1; rwa [hz]⟩⟩
  have hIp : I.ideal U = Ideal.span {g} := sectionIdeal_on_any_frame k s hs v U eM
  let : (Ideal.span {g}).IsPrime := by
    rw [← hIp]
    exact ideal_prime_of_integral_subscheme I U y hyU hyI
  have hgn : g ≠ 0 := affineCoefficient_ne_zero M U eM _ hne
  have hnu : ¬ IsUnit g := by
    intro h
    have H := h.map (q 0).toRingHom
    change IsUnit (q 0 (affineCoefficient U eM (sectionCombination k s v))) at H
    rw [hg0] at H
    exact not_isUnit_zero H
  obtain ⟨j,n,han,b,hb,hbv,hassoc⟩ := maximal_cartier_extraction_of_iso
    S.structureMap L M d hd E k s hs v hne U eL eM hnu a t ht eA
  let f := affineCoefficient U (localPowerFrame U.1 eL n) b
  have hf : f ∉ Ideal.span {g} := by
    intro h
    apply hbv
    apply (pullback_section_zero_iff_local_coefficient S.structureMap I (L.pow n) b U
      (localPowerFrame U.1 eL n)).mpr
    rw [hIp]
    exact h
  have hker := nodal_branch_kernels hR q hq (hjets 2).2 g hgn u hu hu0 hg
  have hx : restrictX ℂ (bivariateTaylor q hq f) ≠ 0 := by
    intro h
    apply hf
    rw [← hker.1]
    exact h
  have hz : restrictZ ℂ (bivariateTaylor q hq f) ≠ 0 := by
    intro h
    apply hf
    rw [← hker.2]
    exact h
  have hc := nodal_ideal_branch_sum_le_degree S L hL I hDim (L.pow n) b U y hyU hyI
    (localPowerFrame U.1 eL n) hR q hq hjets g hgn hIp u hu hu0 hg hf
  have hdeg := generated_curveDegree_of_power_iso S L hL M d E k s hs v hne hDim
  change curveDegree S L (IntegralCurve.ofIdeal S I hDim) = (d:ℤ)*selfIntersection S L at hdeg
  rw [curveDegree_pow S L hL,hdeg] at hc
  have hbound : (Module.finrank ℂ (Bivariate ℂ ⧸
      intersectionIdeal ℂ (bivariateTaylor q hq f)) : ℝ) ≤
      (n:ℝ)*(d:ℝ)*(selfIntersection S L:ℝ) := by
    rw [nodal_intersection_colength _ _ hx hz]
    change (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat+
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ):ℝ) ≤ _
    dsimp only at hc
    rw [← mul_assoc] at hc
    exact_mod_cast hc
  obtain ⟨u',hu',hg'⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hassoc' := hassoc.map (bivariateTaylor q hq).toMonoidHom
  change Associated ((bivariateTaylor q hq) (g^j*f))
    ((bivariateTaylor q hq) (affineCoefficient U eA t)) at hassoc'
  rw [map_mul,map_pow,hg'] at hassoc'
  exact nodal_associated_quadrilateral u' (bivariateTaylor q hq f)
    (bivariateTaylor q hq (affineCoefficient U eA t)) j d (selfIntersection S L) w a n
    (by exact_mod_cast hd) (by exact_mod_cast S.selfIntersection_pos L hL) hw
    (by exact_mod_cast ha) hu' hx hz hbound (by exact_mod_cast (by omega : n+j*d=a))
    hassoc' p hp
end
end MaximalSeshadri.Geometry

end

end OAI
