import Mathlib
import OAI.Geometry.Borsuk.Simplicial.FineCrossMap

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

section GeneralTarget
variable {W : Type*} [DecidableEq W]

noncomputable def fineMap (n r : ℕ) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) : Chain (cross n) →ₗ[F₂] Chain L :=
  (mapChains (hemisphereComplex (n:ℝ)) L f).comp (fineCrossMap n r)

def FineTo (n r : ℕ) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) : Prop :=
  ∀ s ∈ cross n, ∀ t ∈ (fineCrossMap n r (simplex (cross n) s)).support,
    t.val.image f ∈ L

lemma fineMap_boundary (n r : ℕ) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) (hf : FineTo n r L f) :
    (boundary L).comp (fineMap n r L f) = (fineMap n r L f).comp (boundary (cross n)) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : boundary L (fineMap n r L f (simplex (cross n) s.val)) =
      fineMap n r L f (boundary (cross n) (simplex (cross n) s.val)) := by
    change boundary L (mapChains (hemisphereComplex (n:ℝ)) L f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_boundary_of_support _ L f _ (hf s.val s.property)]
    have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
    rw [hb]
    rfl
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]

lemma fineMap_degree (n r d : ℕ) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) :
    degreeChains (cross n) d ≤ (degreeChains L d).comap (fineMap n r L f) := by
  intro c hc
  exact mapChains_degree_all _ L f d (fineCrossMap_degree n r d hc)

lemma mapChains_id (L : PreAbstractSimplicialComplex W) :
    mapChains L L (Equiv.refl W) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : mapChains L L (Equiv.refl W) (simplex L s.val) = simplex L s.val := by
    simpa only [Equiv.coe_refl, Finset.image_id] using
      mapChains_equiv_simplex_all L (Equiv.refl W) (by simp) s.val
  rw [simplex_of_mem L s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [ha, map_smul, hh, LinearMap.id_apply]

lemma normMap_id (L : PreAbstractSimplicialComplex W) : normMap L (Equiv.refl W) = 0 := by
  rw [normMap, mapChains_id]
  ext c s
  exact CharTwo.add_self_eq_zero _

lemma fineMap_even_norm (n r : ℕ) (hn : 0 < n) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) (hf : ∀ x ∈ annulus n, f (-x) = f x) :
    (fineMap n r L f).comp (normMap (cross n) flip) = 0 := by
  have hu : (normMap L (Equiv.refl W)).comp (mapChains (hemisphereComplex (n:ℝ)) L f) =
      (mapChains (hemisphereComplex (n:ℝ)) L f).comp
        (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)) := by
    apply mapChains_norm _ L (Equiv.neg _) (Equiv.refl W) (hemisphere_neg (n:ℝ))
      (by simp) f
    intro s hs x hx
    exact hf x (hemisphere_vertex_annulus n hn hs hx)
  rw [normMap_id, LinearMap.zero_comp] at hu
  rw [fineMap, LinearMap.comp_assoc, ← fineCrossMap_norm, ← LinearMap.comp_assoc,
    ← hu, LinearMap.zero_comp]

noncomputable def projectiveCycle (n r : ℕ) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) : Chain L :=
  fineMap n r L f (crossTower n (n-1))

lemma projectiveCycle_degree (n r : ℕ) (hn : 0 < n) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) : projectiveCycle n r L f ∈ degreeChains L n := by
  have hc := crossTower_degree n (n-1)
  rw [Nat.sub_add_cancel hn] at hc
  exact fineMap_degree n r n L f hc

lemma projectiveCycle_boundary (n r : ℕ) (hn : 1 < n) (L : PreAbstractSimplicialComplex W)
    (f : EuclideanSpace ℝ (Fin n) → W) (hf : FineTo n r L f)
    (he : ∀ x ∈ annulus n, f (-x) = f x) : boundary L (projectiveCycle n r L f) = 0 := by
  unfold projectiveCycle
  rw [← LinearMap.comp_apply, fineMap_boundary n r L f hf, LinearMap.comp_apply]
  have heq : n-1 = (n-2)+1 := by omega
  rw [heq, crossTower_boundary n (n-2) (by omega), ← LinearMap.comp_apply,
    fineMap_even_norm n r (by omega) L f he, LinearMap.zero_apply]

end GeneralTarget

end BorsukNine.SimplicialChains

end OAI
