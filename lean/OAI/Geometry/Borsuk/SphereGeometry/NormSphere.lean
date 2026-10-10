import Mathlib
import OAI.Geometry.Borsuk.Simplicial.Supports
import OAI.Geometry.Borsuk.Simplicial.NullHomotopyLocalModels

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
noncomputable def normSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {u | ‖u‖ = 1}
section SphereNullModels
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => normSphere n
lemma sphere_null_local_models (hn : 1 < n)
    (H C : ℝ × S → E)
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ univ))
    (hHz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : S, H (t,u) ≠ 0)
    (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ univ))
    (hCz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : S, C (t,u) ≠ 0)
    (hC1 : ∀ u, C (1,u) = H (0,u))
    (G : κ → S → E) (hG : ∀ a, Continuous (G a)) (hGz : ∀ a u, G a u ≠ 0)
    (hGo : ∀ a (u v : S), v.val = -u.val → G a v = -G a u)
    (U : κ → Set S) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a u, u ∈ U a → H (1,u) = G a u)
    {y : E} (hy : y ≠ 0)
    (hmiss : ∀ u : S, ¬ ∃ d : ℝ, 0 < d ∧ C (0,u) = d • y)
    (hcover : ∀ u : S, (∃ d : ℝ, 0 < d ∧ H (1,u) = d • y) → ∃ a, u ∈ U a)
    (hroot : ∀ a u, (∃ d : ℝ, 0 < d ∧ G a u = d • y) → u ∈ U a)
    (hdis : Pairwise (fun a b => Disjoint (U a) (U b))) : (Fintype.card κ : F₂) = 0 := by
  classical
  let : NeZero n := ⟨by omega⟩
  let b : Fin n → Bool := fun _ => false
  let L := Submodule.reflection (ℝ ∙ (unitRadial y - facetCenter n b))ᗮ
  have hRy : L (unitRadial y) = facetCenter n b :=
    Submodule.reflection_sub ((unitRadial_norm hy).trans (facetCenter_norm n b).symm)
  have hray (v : E) (hv : v ≠ 0) (he : unitRadial (L v) = facetCenter n b) :
      ∃ d : ℝ, 0 < d ∧ v = d • y := by
    have hu : unitRadial v = unitRadial y := by
      apply L.injective
      rw [hRy]
      simpa only [unitRadial,map_smul,L.norm_map] using he
    refine ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),?_⟩
    have hh := congrArg (fun z : E => ‖v‖ • z) hu
    simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul,div_eq_mul_inv] using hh
  let N : annulus n → S := fun x => ⟨unitRadial x.val,unitRadial_norm (annulus_ne_zero n (by omega) x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact (unitRadial_continuousOn (fun _ hx => annulus_ne_zero n (by omega) hx)).domRestrict
  have hNneg (x) (hx : x ∈ annulus n) (hxn : -x ∈ annulus n) : (N ⟨-x,hxn⟩).val = -(N ⟨x,hx⟩).val := unitRadial_neg x
  let extH (P : ℝ × S → E) : ℝ × E → E := fun p => if hx : p.2 ∈ annulus n then L (P (p.1,N ⟨p.2,hx⟩)) else 0
  have hext (P : ℝ × S → E) (hP : ContinuousOn P (Icc (0:ℝ) 1 ×ˢ univ)) :
      ContinuousOn (extH P) (Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let Q := Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : Q => N ⟨p.val.2,p.property.2⟩) := hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hP.comp_continuous (continuous_subtype_val.fst.prodMk hcN) (fun p : Q => ⟨p.property.1,mem_univ _⟩)
    apply (L.continuous.comp hg).congr
    intro p
    simp only [Set.domRestrict_apply,Function.comp_apply,extH,dite_eq_left p.property.2]
  have hextz (P : ℝ × S → E) (hPz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, P (t,u) ≠ 0) :
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, extH P p ≠ 0 := by
    intro p hp hz
    exact hPz _ hp.1 _ (L.injective (by simpa only [extH,dite_eq_left hp.2,map_zero] using hz))
  let G' : κ → E → E := fun a x => if hx : x ∈ annulus n then L (G a (N ⟨x,hx⟩)) else 0
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
  refine null_homotopy_local_models n hn b (extH H) (hext H hH) (hextz H hHz) (extH C) (hext C hC) (hextz C hCz)
    (fun x => by simp only [extH,hC1]) ?_ G' hG' hGz' hGo'
    (fun a => N ⁻¹' U a) (fun a => (hU a).preimage hN) ?_ ?_ ?_ ?_
  · intro x hx he
    apply hmiss (N ⟨x,hx⟩)
    apply hray _ (hCz _ ⟨le_rfl,zero_le_one⟩ _)
    simpa only [extH,dite_eq_left hx] using he
  · intro a x hx
    simp only [extH,G',dite_eq_left x.property,heq a _ hx]
  · intro x hx
    apply hcover (N x)
    apply hray _ (hHz _ ⟨zero_le_one,le_rfl⟩ _)
    simpa only [extH,dite_eq_left x.property] using hx
  · intro a x hx
    apply hroot a (N x)
    apply hray _ (hGz a _)
    simpa only [G',dite_eq_left x.property] using hx
  · intro a a' haa
    exact (hdis haa).preimage N
end SphereNullModels
end BorsukNine

end OAI
