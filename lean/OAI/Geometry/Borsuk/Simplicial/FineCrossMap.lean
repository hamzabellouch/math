import Mathlib
import OAI.Geometry.Borsuk.Simplicial.CrossEmbedding
import OAI.Geometry.Borsuk.Simplicial.Refinement
import OAI.Geometry.Borsuk.Simplicial.MaxIndex

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

noncomputable def fineCrossMap (n r : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreAbstractSimplicialComplex (EuclideanSpace ℝ (Fin n))) :=
  (refinement (n:ℝ) r).comp (crossGeometricMap n)

lemma fineCrossMap_boundary (n r : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (boundary (cross n)) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_boundary,
    LinearMap.comp_assoc, crossGeometricMap_boundary, ← LinearMap.comp_assoc]

lemma fineCrossMap_augmentation (n r : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) = augmentation (cross n) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_augmentation,
    crossGeometricMap_augmentation]

lemma fineCrossMap_norm (n r : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (normMap (cross n) flip) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_norm,
    LinearMap.comp_assoc, crossGeometricMap_norm, ← LinearMap.comp_assoc]

lemma fineCrossMap_degree (n r d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (fineCrossMap n r) := by
  intro c hc
  change refinement (n:ℝ) r (crossGeometricMap n c) ∈ degreeChains (hemisphereComplex (n:ℝ)) d
  exact refinement_degree (E := EuclideanSpace ℝ (Fin n)) (n:ℝ) r d
    (crossGeometricMap_degree n d hc)

lemma fineCrossMap_simplex_mesh (n r : ℕ) {s : Finset SignedVertex} (hs : s ∈ cross n)
    {t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  apply refinement_mesh_uniform (n:ℝ) r n s.card (cross_card n s hs)
    (crossGeometricMap_degree n s.card (simplex_mem_degree _ hs)) ht

def annulus (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (1:ℝ)/n ≤ ‖x‖ ∧ ‖x‖ ≤ 1}

lemma annulus_compact (n : ℕ) : IsCompact (annulus n) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

lemma hemisphere_vertex_annulus (n : ℕ) (hn : 0 < n)
    {s : Finset (EuclideanSpace ℝ (Fin n))} (hs : s ∈ hemisphereComplex (n:ℝ))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) : x ∈ annulus n := by
  obtain ⟨_,w,hw,hh⟩ := hs
  refine ⟨?_,(hh x hx).1⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := real_inner_le_norm w x
  rw [(hh x hx).2] at h
  calc
    1 ≤ ‖w‖ * ‖x‖ := h
    _ ≤ (n:ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)
    _ = ‖x‖ * (n:ℝ) := mul_comm _ _

lemma annular_odd_dimension_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) : n ≤ m := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast hm))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  let K : PreAbstractSimplicialComplex (EuclideanSpace ℝ (Fin n)) := hemisphereComplex (n:ℝ)
  let f : EuclideanSpace ℝ (Fin n) → SignedVertex := fun x => sphereLabel (g x)
  let U : Chain K →ₗ[F₂] Chain (cross m) := mapChains K (cross m) f
  let T : Chain (cross n) →ₗ[F₂] Chain (cross m) := U.comp (fineCrossMap n r)
  have hfine (s : Finset SignedVertex) (hs : s ∈ cross n)
      (t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ K})
      (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) : t.val.image f ∈ cross m := by
    refine ⟨t.property.1.image _, ?_, ?_⟩
    · intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact sphereLabel_bound (g x)
    · intro v hv w hw he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have hxa := hemisphere_vertex_annulus n hn t.property hx
      have hya := hemisphere_vertex_annulus n hn t.property hy
      apply sphereLabel_compatible (g x) (g y) (hgn x hxa) (hgn y hya) _ he
      exact hclose x hxa y hya ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hmeshδ)
  have hdb : (boundary (cross m)).comp T = T.comp (boundary (cross n)) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : boundary (cross m) (T (simplex (cross n) s.val)) =
        T (boundary (cross n) (simplex (cross n) s.val)) := by
      change boundary (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_boundary_of_support K (cross m) f _ (hfine s.val s.property)]
      have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
      rw [hb]
      rfl
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have haug : (augmentation (cross m)).comp T = augmentation (cross n) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : augmentation (cross m) (T (simplex (cross n) s.val)) =
        augmentation (cross n) (simplex (cross n) s.val) := by
      change augmentation (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_augmentation_of_support K (cross m) f _ (hfine s.val s.property)]
      exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have hnorm : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip) := by
    have hu : (normMap (cross m) flip).comp U = U.comp (normMap K (Equiv.neg _)) := by
      apply mapChains_norm K (cross m) (Equiv.neg _) flip
        (hemisphere_neg (n:ℝ)) (cross_flip m) f
      intro s hs x hx
      have hxa := hemisphere_vertex_annulus n hn hs hx
      change sphereLabel (g (-x)) = flip (sphereLabel (g x))
      rw [hgo x hxa, sphereLabel_neg _ (hgn x hxa)]
    change (normMap (cross m) flip).comp (U.comp (fineCrossMap n r)) =
      (U.comp (fineCrossMap n r)).comp (normMap (cross n) flip)
    rw [← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
      fineCrossMap_norm, ← LinearMap.comp_assoc]
  apply cross_chain_dimension_bound n m T hdb hnorm haug
  intro d c hc
  change mapChains K (cross m) f (fineCrossMap n r c) ∈ degreeChains (cross m) d
  exact mapChains_degree_all K (cross m) f d (fineCrossMap_degree n r d hc)

end BorsukNine.SimplicialChains

end OAI
