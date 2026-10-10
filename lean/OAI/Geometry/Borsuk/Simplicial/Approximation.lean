import Mathlib
import OAI.Geometry.Borsuk.Simplicial.FineCrossMap
import OAI.Geometry.Borsuk.Simplicial.BoolCubeConstant
import OAI.Geometry.Borsuk.Simplicial.ContigSimplexBoundary

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def approximation (n m r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → SignedVertex) : Chain (cross n) →ₗ[F₂] Chain (cross m) :=
  (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp (fineCrossMap n r)

def IsFineLabel (n m r : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex) : Prop :=
  ∀ (s : Finset SignedVertex), s ∈ cross n →
    ∀ (t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}),
      t ∈ (fineCrossMap n r (simplex (cross n) s)).support → t.val.image f ∈ cross m

lemma approximation_boundary (n m r : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (boundary (cross m)).comp (approximation n m r f) =
      (approximation n m r f).comp (boundary (cross n)) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : boundary (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      approximation n m r f (boundary (cross n) (simplex (cross n) s.val)) := by
    change boundary (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_boundary_of_support _ (cross m) f _ (hf s.val s.property)]
    have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
    rw [hb]
    rfl
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]

lemma approximation_augmentation (n m r : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (augmentation (cross m)).comp (approximation n m r f) = augmentation (cross n) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : augmentation (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      augmentation (cross n) (simplex (cross n) s.val) := by
    change augmentation (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_augmentation_of_support _ (cross m) f _ (hf s.val s.property)]
    exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]

lemma approximation_norm (n m r : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hf : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    (normMap (cross m) flip).comp (approximation n m r f) =
      (approximation n m r f).comp (normMap (cross n) flip) := by
  have hu : (normMap (cross m) flip).comp (mapChains (hemisphereComplex (n:ℝ)) (cross m) f) =
      (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp
        (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)) := by
    apply mapChains_norm _ (cross m) (Equiv.neg _) flip (hemisphere_neg (n:ℝ)) (cross_flip m) f
    intro s hs x hx
    exact hf x (hemisphere_vertex_annulus n hn hs hx)
  rw [approximation, ← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
    fineCrossMap_norm, ← LinearMap.comp_assoc]

lemma approximation_degree (n m r d : ℕ) (f : EuclideanSpace ℝ (Fin n) → SignedVertex) :
    degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap (approximation n m r f) := by
  intro c hc
  exact mapChains_degree_all _ (cross m) f d (fineCrossMap_degree n r d hc)

lemma cross_equivariant_fundamental (n : ℕ) (hn : 1 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n))
    (hTd : ∀ c ∈ degreeChains (cross n) n, T c ∈ degreeChains (cross n) n) :
    T (crossFundamental n) = crossFundamental n := by
  have hc := hTd _ (crossFundamental_degree n (by omega))
  have hb : boundary (cross n) (T (crossFundamental n)) = 0 := by
    rw [← LinearMap.comp_apply, hTbd, LinearMap.comp_apply,
      crossFundamental_boundary n (by omega), map_zero]
  have hd : T (crossFundamental n) ⟨crossFacet n (fun _ => false),
      crossFacet_mem n (by omega) (fun _ => false)⟩ = 1 := by
    rw [← cross_characteristicDegree_eq_coeff n hn _ hc hb]
    exact cross_equivariant_degree_one n (by omega) T hTbd hTN hTa
  rw [cross_top_cycle_eq n hn _ hc hb (fun _ => false), hd, one_smul]

lemma approximation_odd_fundamental (n r : ℕ) (hn : 1 < n)
    (f : EuclideanSpace ℝ (Fin n) → SignedVertex) (hf : IsFineLabel n n r f)
    (ho : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    approximation n n r f (crossFundamental n) = crossFundamental n := by
  apply cross_equivariant_fundamental n hn _ (approximation_boundary n n r f hf)
    (approximation_norm n n r (by omega) f ho) (approximation_augmentation n n r f hf)
  intro c hc
  exact approximation_degree n n r n f hc

lemma exists_fine_sphereLabel (n m : ℕ) (hn : 0 < n) [NeZero m]
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1) :
    ∃ r : ℕ, IsFineLabel n m r (fun x => sphereLabel (g x)) := by
  classical
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  refine ⟨r,?_⟩
  intro s hs t ht
  refine ⟨t.property.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact sphereLabel_bound (g x)
  · intro v hv w hw he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    have hx' := hemisphere_vertex_annulus n hn t.property hx
    have hy' := hemisphere_vertex_annulus n hn t.property hy
    apply sphereLabel_compatible (g x) (g y) (hgn x hx') (hgn y hy') _ he
    exact hclose x hx' y hy' ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hmeshδ)

lemma odd_sphere_simplicial_degree (n : ℕ) (hn : 1 < n) [NeZero n]
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) :
    ∃ r, IsFineLabel n n r (fun x => sphereLabel (g x)) ∧
      approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) = crossFundamental n := by
  obtain ⟨r,hr⟩ := exists_fine_sphereLabel n n (by omega) g hg hgn
  refine ⟨r,hr,approximation_odd_fundamental n r hn _ hr ?_⟩
  intro x hx
  rw [hgo x hx, sphereLabel_neg _ (hgn x hx)]

lemma approximation_agree_top (n m r : ℕ) (hn : 0 < n)
    (f g : EuclideanSpace ℝ (Fin n) → SignedVertex)
    (hcard : m ≤ n)
    (hfg : ∀ s ∈ (fineCrossMap n r (crossFundamental n)).support,
      s.val.image f ∪ s.val.image g ∈ cross m) :
    approximation n m r f (crossFundamental n) = approximation n m r g (crossFundamental n) := by
  apply contig_maps_agree_top _ (cross m) f g n _
    (fineCrossMap_degree n r n (crossFundamental_degree n hn)) _ hfg
    (fun s hs => (cross_card m s hs).trans hcard)
  rw [← LinearMap.comp_apply, fineCrossMap_boundary, LinearMap.comp_apply,
    crossFundamental_boundary n hn, map_zero]

end BorsukNine.SimplicialChains

end OAI
