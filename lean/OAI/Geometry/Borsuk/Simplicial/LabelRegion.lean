import Mathlib
import OAI.Geometry.Borsuk.Simplicial.FineCrossMapMesh

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def labelRegion {m : ℕ} (i : Fin m) (b : Bool) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {y | (∀ j, |y j| ≤ |y i|) ∧ if b then y i ≤ 0 else 0 ≤ y i}

lemma labelRegion_closed {m : ℕ} (i : Fin m) (b : Bool) : IsClosed (labelRegion i b) := by
  have hc (j : Fin m) : Continuous (fun y : EuclideanSpace ℝ (Fin m) => y j) :=
    PiLp.continuous_apply 2 _ j
  apply IsClosed.inter
  · change IsClosed {y : EuclideanSpace ℝ (Fin m) | ∀ j, |y j| ≤ |y i|}
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (hc j).abs (hc i).abs)
  · cases b
    · exact isClosed_le continuous_const (hc i)
    · exact isClosed_le (hc i) continuous_const

lemma sphereLabel_mem_region {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m))
    (i : Fin m) (b : Bool) (hy : sphereLabel y = (i.val,b)) : y ∈ labelRegion i b := by
  have hi : peakIndex y = i := Fin.ext (congrArg Prod.fst hy)
  have hb : decide (y (peakIndex y) < 0) = b := congrArg Prod.snd hy
  refine ⟨?_,?_⟩
  · intro j
    rw [← hi]
    exact maxIndex_le (fun j => |y j|) j
  · rw [← hb, hi]
    by_cases h : y i < 0
    · simp only [h, decide_true, ↓reduceIte]
      exact h.le
    · simp only [h, decide_false]
      exact le_of_not_gt h

lemma compact_label_locality {X : Type*} [MetricSpace X] [CompactSpace X]
    {m : ℕ} [NeZero m] (b : Fin m → Bool)
    (f g : X → EuclideanSpace ℝ (Fin m)) (hf : Continuous f) (hg : Continuous g)
    (U : Set X) (hU : IsOpen U)
    (heq : ∀ x ∈ U, f x = g x)
    (hfull : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) ∨
      (∀ i, g x ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ x : X,
      (∀ y, dist y x < δ → f y = g y) ∨
      ∃ i j : Fin m,
        (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        (∀ y, dist y x < δ → sphereLabel (g y) ≠ (j.val,b j)) := by
  let c : Option (Fin m × Fin m) → Set X := fun o => match o with
    | none => U
    | some (i,j) => (f ⁻¹' labelRegion i (b i))ᶜ ∩ (g ⁻¹' labelRegion j (b j))ᶜ
  have hc : ∀ i, IsOpen (c i) := by
    intro o
    cases o with
    | none => exact hU
    | some p =>
      exact ((labelRegion_closed p.1 (b p.1)).preimage hf).isOpen_compl.inter
        ((labelRegion_closed p.2 (b p.2)).preimage hg).isOpen_compl
  have hcover : (Set.univ : Set X) ⊆ ⋃ o, c o := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨none,hx⟩
    · have hnf : ¬ ∀ i, f x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inl hh))
      have hng : ¬ ∀ i, g x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inr hh))
      obtain ⟨i,hi⟩ := not_forall.mp hnf
      obtain ⟨j,hj⟩ := not_forall.mp hng
      exact Set.mem_iUnion.mpr ⟨some (i,j),hi,hj⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨o,ho⟩ := hball x (Set.mem_univ _)
  cases o with
  | none => exact Or.inl (fun y hy => heq y (ho hy))
  | some p =>
    refine Or.inr ⟨p.1,p.2,?_,?_⟩
    · intro y hy he
      exact (ho hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro y hy he
      exact (ho hy).2 (sphereLabel_mem_region _ _ _ he)

lemma mapSimplex_coeff_zero_of_ne {V W : Type*} [DecidableEq V] [DecidableEq W]
    (L : PreAbstractSimplicialComplex W) (f : V → W) (s : Finset V)
    (t : {s : Finset W // s ∈ L}) (hne : s.image f ≠ t.val) :
    mapSimplex L f s t = 0 := by
  rw [mapSimplex]
  split_ifs <;> simp_all [simplex_coeff]

lemma image_ne_crossFacet_of_missing {V : Type*} [DecidableEq V] {m : ℕ}
    (s : Finset V) (f : V → SignedVertex) (b : Fin m → Bool)
    (i : Fin m) (hi : ∀ x ∈ s, f x ≠ (i.val,b i)) : s.image f ≠ crossFacet m b := by
  intro h
  have hm : (i.val,b i) ∈ s.image f := by
    rw [h]
    exact (mem_crossFacet m b _).mpr ⟨i,rfl⟩
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
  exact hi x hx he

lemma localized_approximation_coeff (n m : ℕ) (hn : 0 < n) [NeZero m]
    (b : Fin m → Bool)
    (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ContinuousOn g (annulus n))
    (U : Set (annulus n)) (hU : IsOpen U)
    (heq : ∀ x : annulus n, x ∈ U → f x.val = g x.val)
    (hfull : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) ∨
      (∀ i, g x.val ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      approximation n m r (fun x => sphereLabel (g x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_label_locality b (fun x : annulus n => f x.val)
    (fun x : annulus n => g x.val) hf.domRestrict hg.domRestrict U hU heq hfull
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := EuclideanSpace ℝ (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g x)))
  change T (fineCrossMap n r (crossFundamental n)) = R (fineCrossMap n r (crossFundamental n))
  apply linearMap_eq_of_support T R _
  intro s hs
  change mapChains K (cross m) (fun x => sphereLabel (f x)) (simplex K s.val) t =
    mapChains K (cross m) (fun x => sphereLabel (g x)) (simplex K s.val) t
  rw [mapChains_simplex K (cross m) _ s.property,mapChains_simplex K (cross m) _ s.property]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  rcases hlocal ⟨x,ha x hx⟩ with he | ⟨i,j,hi,hj⟩
  · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g y)) := by
      apply Finset.image_congr
      intro y hy
      exact congrArg sphereLabel (he ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr))
    simp only [mapSimplex,himg]
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t, mapSimplex_coeff_zero_of_ne (cross m) _ s.val t]
    · apply image_ne_crossFacet_of_missing s.val _ b j
      intro y hy
      exact hj ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)
    · apply image_ne_crossFacet_of_missing s.val _ b i
      intro y hy
      exact hi ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)

end BorsukNine.SimplicialChains

end OAI
