import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.OddSphereMap
import OAI.Geometry.Borsuk.SmithTheory.Involution
import OAI.Geometry.Borsuk.Simplicial.Equivariance

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def normMap (K : PreAbstractSimplicialComplex V) (e : V ≃ V) :
    Chain K →ₗ[F₂] Chain K := LinearMap.id + mapChains K K e

lemma normMap_eq (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) :
    normMap K e = SmithTheory.involutionNorm (faceEquiv K e he) := by
  unfold normMap SmithTheory.involutionNorm
  rw [mapChains_equiv K e he]

lemma boundary_normMap (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (boundary K).comp (normMap K e) = (normMap K e).comp (boundary K) := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_id, LinearMap.id_comp,
    mapChains_boundary K K e he]

lemma augmentation_normMap (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (augmentation K).comp (normMap K e) = 0 := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.comp_id, mapChains_augmentation K K e he]
  ext c
  exact CharTwo.add_self_eq_zero _

lemma antipodal_tower_augmentation_zero (K : PreAbstractSimplicialComplex V)
    (e : V ≃ V) (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (n : ℕ) (c : ℕ → Chain K)
    (htower : ∀ i < n, boundary K (c (i+1)) = normMap K e (c i))
    (htop : normMap K e (c n) = 0) : augmentation K (c 0) = 0 := by
  apply SmithTheory.tower_augmentation_zero (boundary K) (normMap K e)
    (boundary_sq K) (boundary_normMap K e (fun s hs => (he s).mp hs))
    _ n (augmentation K) (augmentation_normMap K e (fun s hs => (he s).mp hs))
    (augmentation_boundary K) c htower htop
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)

noncomputable def degreeChains (K : PreAbstractSimplicialComplex V) (d : ℕ) :
    Submodule F₂ (Chain K) := Finsupp.supported F₂ F₂ {s | s.val.card = d}

omit [DecidableEq V] in
lemma simplex_mem_degree (K : PreAbstractSimplicialComplex V) {s : Finset V}
    (hs : s ∈ K) : simplex K s ∈ degreeChains K s.card := by
  rw [simplex_of_mem K hs]
  exact Finsupp.single_mem_supported _ _ rfl

omit [DecidableEq V] [DecidableEq W] in
lemma grade_map (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (d e : ℕ)
    (hT : ∀ s ∈ K, s.card = d → T (simplex K s) ∈ degreeChains L e) :
    degreeChains K d ≤ (degreeChains L e).comap T := by
  rw [degreeChains, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  change T (Finsupp.single s 1) ∈ degreeChains L e
  rw [← simplex_of_mem K s.property]
  exact hT s.val s.property hs

omit [DecidableEq V] in
lemma mapChains_degree (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree L (hf s hs)
  · exact Submodule.zero_mem _

omit [DecidableEq V] in
lemma degreeChains_eq_bot_of_card_bound (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hK : ∀ s ∈ K, s.card < d) : degreeChains K d = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply Finsupp.ext
  intro s
  have hne : s.val.card ≠ d := ne_of_lt (hK s.val s.property)
  exact (Finsupp.mem_supported' F₂ c).mp hc s hne

omit [DecidableEq V] in
lemma augmentation_eq_zero_of_degree (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hd : d ≠ 1) {c : Chain K} (hc : c ∈ degreeChains K d) : augmentation K c = 0 := by
  have hle : degreeChains K d ≤ LinearMap.ker (augmentation K) := by
    rw [degreeChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change augmentation K (Finsupp.single s 1) = 0
    rw [← simplex_of_mem K s.property, augmentation_simplex K s.property]
    simp [show s.val.card ≠ 1 by simpa only [Set.mem_ofPred_eq] using hs ▸ hd]
  exact hle hc

end BorsukNine.SimplicialChains

end OAI
