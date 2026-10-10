import Mathlib
import OAI.Geometry.Borsuk.Simplicial.LabelRegion

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma compact_additive_locality {X A : Type*} [MetricSpace X] [CompactSpace X]
    [Fintype A] [DecidableEq A] {m : ℕ} [NeZero m]
    (b : Fin m → Bool) (f : X → EuclideanSpace ℝ (Fin m))
    (g : A → X → EuclideanSpace ℝ (Fin m)) (hf : Continuous f) (hg : ∀ a, Continuous (g a))
    (U : A → Set X) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a x, x ∈ U a → f x = g a x)
    (hcover : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) → ∃ a, x ∈ U a)
    (hroot : ∀ a x, (∀ i, g a x ∈ labelRegion i (b i)) → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) :
    ∃ δ > 0, ∀ x : X,
      (∃ i : Fin m, (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        ∀ a, ∃ j : Fin m, ∀ y, dist y x < δ → sphereLabel (g a y) ≠ (j.val,b j)) ∨
      ∃ a, (∀ y, dist y x < δ → f y = g a y) ∧
        ∀ a' ≠ a, ∃ j : Fin m, ∀ y, dist y x < δ → sphereLabel (g a' y) ≠ (j.val,b j) := by
  classical
  let c : Option A × (Option A → Fin m) → Set X := fun p => match p.1 with
    | none => (f ⁻¹' labelRegion (p.2 none) (b (p.2 none)))ᶜ ∩
        ⋂ a, (g a ⁻¹' labelRegion (p.2 (some a)) (b (p.2 (some a))))ᶜ
    | some a => U a ∩ ⋂ a' : {a' : A // a' ≠ a},
        (g a'.val ⁻¹' labelRegion (p.2 (some a'.val)) (b (p.2 (some a'.val))))ᶜ
  have hopen : ∀ p, IsOpen (c p) := by
    intro p
    cases ho : p.1 with
    | none =>
      simp only [c,ho]
      exact (((labelRegion_closed _ _).preimage hf).isOpen_compl).inter
        (isOpen_iInter_of_finite (fun a => ((labelRegion_closed _ _).preimage (hg a)).isOpen_compl))
    | some a =>
      simp only [c,ho]
      exact (hU a).inter (isOpen_iInter_of_finite
        (fun a' => ((labelRegion_closed _ _).preimage (hg a'.val)).isOpen_compl))
  have hc : (Set.univ : Set X) ⊆ ⋃ p, c p := by
    intro x _
    by_cases hx : ∃ a, x ∈ U a
    · obtain ⟨a,ha⟩ := hx
      have hm : ∀ a' : {a' : A // a' ≠ a}, ∃ j, g a'.val x ∉ labelRegion j (b j) := by
        intro a'
        apply not_forall.mp
        intro hh
        exact Set.disjoint_left.mp (hdis a'.property) (hroot a'.val x hh) ha
      choose j hj using hm
      let ji : Option A → Fin m := fun o => match o with
        | none => ⟨0,NeZero.pos m⟩
        | some a' => if h : a' ≠ a then j ⟨a',h⟩ else ⟨0,NeZero.pos m⟩
      refine Set.mem_iUnion.mpr ⟨(some a,ji),ha,Set.mem_iInter.mpr ?_⟩
      intro a'
      simpa only [ji,dite_eq_left a'.property,Set.mem_compl_iff,Set.mem_preimage] using hj a'
    · have hm : ∀ o : Option A, ∃ j, (match o with | none => f x | some a => g a x) ∉ labelRegion j (b j) := by
        intro o
        apply not_forall.mp
        intro hh
        cases o with
        | none => exact hx (hcover x hh)
        | some a => exact hx ⟨a,hroot a x hh⟩
      choose j hj using hm
      exact Set.mem_iUnion.mpr ⟨(none,j),hj none,Set.mem_iInter.mpr (fun a => hj (some a))⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hc
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨⟨o,j⟩,hj⟩ := hball x (Set.mem_univ _)
  cases o with
  | none =>
    refine Or.inl ⟨j none,?_,?_⟩
    · intro y hy he
      exact (hj hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro a
      refine ⟨j (some a),?_⟩
      intro y hy he
      exact Set.mem_iInter.mp (hj hy).2 a (sphereLabel_mem_region _ _ _ he)
  | some a =>
    refine Or.inr ⟨a,fun y hy => heq a y (hj hy).1,?_⟩
    intro a' ha'
    refine ⟨j (some a'),?_⟩
    intro y hy he
    exact Set.mem_iInter.mp (hj hy).2 ⟨a',ha'⟩ (sphereLabel_mem_region _ _ _ he)

lemma additive_approximation_coeff {A : Type*} [Fintype A] [DecidableEq A]
    (n m : ℕ) (hn : 0 < n) [NeZero m] (b : Fin m → Bool)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ∀ a, ContinuousOn (g a) (annulus n))
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → f x.val = g a x.val)
    (hcover : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), (∀ i, g a x.val ∈ labelRegion i (b i)) → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      ∑ a, approximation n m r (fun x => sphereLabel (g a x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_additive_locality b (fun x : annulus n => f x.val)
    (fun a (x : annulus n) => g a x.val) hf.domRestrict (fun a => (hg a).domRestrict)
    U hU heq hcover hroot hdis
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := EuclideanSpace ℝ (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : A → Chain K →ₗ[F₂] F₂ := fun a =>
    (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g a x)))
  change T (fineCrossMap n r (crossFundamental n)) = ∑ a, R a (fineCrossMap n r (crossFundamental n))
  rw [← LinearMap.sum_apply]
  apply linearMap_eq_of_support T (∑ a, R a) _
  intro s hs
  rw [LinearMap.sum_apply]
  have heT : T (simplex K s.val) = mapSimplex (cross m) (fun x => sphereLabel (f x)) s.val t := by
    exact congrArg (fun c : Chain (cross m) => c t) (mapChains_simplex K (cross m) _ s.property)
  have heR (a : A) : R a (simplex K s.val) = mapSimplex (cross m) (fun x => sphereLabel (g a x)) s.val t := by
    exact congrArg (fun c : Chain (cross m) => c t) (mapChains_simplex K (cross m) _ s.property)
  simp only [heT,heR]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  have hball (y) (hy : y ∈ s.val) : dist (⟨y,ha y hy⟩ : annulus n) ⟨x,ha x hx⟩ < δ :=
    (hmesh y hy x hx).trans_lt hr
  rcases hlocal ⟨x,ha x hx⟩ with ⟨i,hi,hgmiss⟩ | ⟨a,heq,hgmiss⟩
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
      (image_ne_crossFacet_of_missing s.val _ b i (fun y hy => hi ⟨y,ha y hy⟩ (hball y hy)))]
    symm
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨j,hj⟩ := hgmiss a
    exact mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
      (image_ne_crossFacet_of_missing s.val _ b j (fun y hy => hj ⟨y,ha y hy⟩ (hball y hy)))
  · rw [Finset.sum_eq_single a]
    · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g a y)) := by
        apply Finset.image_congr
        intro y hy
        exact congrArg sphereLabel (heq ⟨y,ha y hy⟩ (hball y hy))
      simp only [mapSimplex,himg]
    · intro a' _ ha'
      obtain ⟨j,hj⟩ := hgmiss a' ha'
      exact mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
        (image_ne_crossFacet_of_missing s.val _ b j (fun y hy => hj ⟨y,ha y hy⟩ (hball y hy)))
    · simp

end BorsukNine.SimplicialChains

end OAI
