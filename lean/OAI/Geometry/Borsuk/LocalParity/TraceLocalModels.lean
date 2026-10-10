import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.TraceSphere
import OAI.Geometry.Borsuk.Simplicial.Supports
import OAI.Geometry.Borsuk.MatrixGeometry.FinitePositiveBound

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains Set
section TraceLocalModels
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
  [Fintype κ] [DecidableEq κ]
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι
omit [Nonempty ν] in
lemma trace_odd_local_models
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (H : ℝ × traceSphere ν → Y)
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ univ))
    (hHz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A : traceSphere ν, H (t,A) ≠ 0)
    (hHo : ∀ A B : traceSphere ν, B.val = -A.val → H (0,B) = -H (0,A))
    (G : κ → traceSphere ν → Y) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
    (U : κ → Set (traceSphere ν)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a A, A ∈ U a → H (1,A) = G a A)
    {y : Y} (hy : y ≠ 0)
    (hcover : ∀ A : traceSphere ν, (∃ d : ℝ, 0 < d ∧ H (1,A) = d • y) → ∃ a, A ∈ U a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card κ : F₂) = 1 := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let b : Fin n → Bool := fun _ => false
  let R := Submodule.reflection (ℝ ∙ (ebL (unitRadial y) - facetCenter n b))ᗮ
  let L : Y ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := ebL.trans R
  have hRy : L (unitRadial y) = facetCenter n b :=
    Submodule.reflection_sub ((ebL.norm_map _).trans (unitRadial_norm hy) |>.trans (facetCenter_norm n b).symm)
  have hray (v : Y) (hv : v ≠ 0) (he : unitRadial (L v) = facetCenter n b) :
      ∃ d : ℝ, 0 < d ∧ v = d • y := by
    have hu : unitRadial v = unitRadial y := by
      apply L.injective
      rw [hRy]
      simpa only [unitRadial,map_smul,L.norm_map] using he
    refine ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),?_⟩
    have hh := congrArg (fun z : Y => ‖v‖ • z) hu
    simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul,div_eq_mul_inv] using hh
  let A : EuclideanSpace ℝ (Fin n) → M := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    exact annulus_ne_zero n (by omega) hx (eaL.symm.injective (h0.trans (map_zero _).symm))
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val) (fun x => hAz _ x.property)
  have hNneg (x) (hx : x ∈ annulus n) (hxn : -x ∈ annulus n) :
      (N ⟨-x,hxn⟩).val = -(N ⟨x,hx⟩).val := by simp only [N,A,map_neg,traceRadial_neg]
  let H' : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then L (H (p.1,N ⟨p.2,hx⟩)) else 0
  have hH' : ContinuousOn H' (Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hH.comp_continuous (continuous_subtype_val.fst.prodMk hcN) (fun p : S => ⟨p.property.1,mem_univ _⟩)
    apply (L.continuous.comp hg).congr
    intro p
    simp only [Set.domRestrict_apply,Function.comp_apply,H',dite_eq_left p.property.2]
  have hHz' : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H' p ≠ 0 := by
    intro p hp hz
    exact hHz _ hp.1 _ (L.injective (by simpa only [H',dite_eq_left hp.2,map_zero] using hz))
  have hHo' : ∀ x ∈ annulus n, H' (0,-x) = -H' (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H',dite_eq_left hx,dite_eq_left hxn,hHo _ _ (hNneg x hx hxn),map_neg]
  let G' : κ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun a x =>
    if hx : x ∈ annulus n then L (G a (N ⟨x,hx⟩)) else 0
  have hG' (a) : ContinuousOn (G' a) (annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (L.continuous.comp ((hG a).comp hN)).congr
    intro x
    simp only [Set.domRestrict_apply,Function.comp_apply,G',dite_eq_left x.property]
  have hGz' (a x) (hx : x ∈ annulus n) : G' a x ≠ 0 := by
    intro hz
    exact hGz a _ (L.injective (by simpa only [G',dite_eq_left hx,map_zero] using hz))
  have hGo' (a x) (hx : x ∈ annulus n) : G' a (-x) = -G' a x := by
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [G',dite_eq_left hx,dite_eq_left hxn,hGo a _ _ (hNneg x hx hxn),map_neg]
  apply odd_homotopy_local_models n hn b H' hH' hHz' hHo' G' hG' hGz' hGo'
    (fun a => N ⁻¹' U a) (fun a => (hU a).preimage hN)
  · intro a x hx
    simp only [H',G',dite_eq_left x.property,heq a _ hx]
  · intro x hx
    apply hcover (N x)
    apply hray _ (hHz _ ⟨zero_le_one,le_rfl⟩ _)
    simpa only [H',dite_eq_left x.property] using hx
  · intro a x hx
    apply hroot a (N x)
    apply hray _ (hGz a _)
    simpa only [G',dite_eq_left x.property] using hx
  · intro a a' haa
    exact (hdis haa).preimage N
end TraceLocalModels
end BorsukNine

end OAI
