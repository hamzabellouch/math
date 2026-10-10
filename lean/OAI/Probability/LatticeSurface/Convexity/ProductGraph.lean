import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ShiftData

namespace OAI

open Set MeasureTheory intervalIntegral

universe u v

namespace FeasibleShift

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ShiftData

variable {W : Type v} [Fintype W] [DecidableEq W]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

variable (S : ShiftData (V := V) W n D Db B ρ sstar L M N)

end ShiftData

end FeasibleShift

namespace FeasibleShift

namespace DisjointUnion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : ι → Type u} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

noncomputable def graph (G : ∀ i, SimpleGraph (V i)) : SimpleGraph (Sigma V) where
  Adj x y := ∃ e : x.1 = y.1, (G y.1).Adj (e ▸ x.2) y.2
  symm := ⟨by rintro ⟨i,x⟩ ⟨j,y⟩ ⟨h,hh⟩; cases h; exact ⟨rfl,hh.symm⟩⟩
  loopless := ⟨by rintro ⟨i,x⟩ ⟨h,hh⟩; exact (G i).irrefl hh⟩

omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (V index)]
  [∀ index, DecidableEq (V index)] in
@[simp] lemma graph_adj_same (G : ∀ i, SimpleGraph (V i)) (i : ι) (x y : V i) :
    (graph G).Adj ⟨i,x⟩ ⟨i,y⟩ ↔ (G i).Adj x y := by
  simp [graph]

omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (V index)]
  [∀ index, DecidableEq (V index)] in
lemma graph_adj_index {G : ∀ i, SimpleGraph (V i)} {x y : Sigma V}
    (h : (graph G).Adj x y) : x.1 = y.1 := h.1

noncomputable def sites (F : ∀ i, Finset (V i)) : Finset (Sigma V) :=
  Finset.univ.sigma F

omit [DecidableEq ι] [∀ index, Fintype (V index)] [∀ index, DecidableEq (V index)] in
@[simp] lemma mem_sites (F : ∀ i, Finset (V i)) (i : ι) (x : V i) :
    (⟨i,x⟩ : Sigma V) ∈ sites F ↔ x ∈ F i := by simp [sites]

omit [DecidableEq ι] [∀ index, Fintype (V index)] [∀ index, DecidableEq (V index)] in
lemma sites_card (F : ∀ i, Finset (V i)) : (sites F).card = ∑ i, (F i).card := by
  simp [sites, Finset.card_sigma]

noncomputable def inclusion (G : ∀ i, SimpleGraph (V i)) (i : ι) :
    G i ↪g graph G where
  toFun x := ⟨i,x⟩
  inj' := sigma_mk_injective
  map_rel_iff' := by simp

omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (V index)]
  [∀ index, DecidableEq (V index)] in
lemma reachable_index {G : ∀ i, SimpleGraph (V i)} {x y : Sigma V}
    (h : (graph G).Reachable x y) : x.1 = y.1 := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (graph_adj_index h).trans ih

omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (V index)]
  [∀ index, DecidableEq (V index)] in
lemma reachable_same (G : ∀ i, SimpleGraph (V i)) (i : ι) (x y : V i) :
    (graph G).Reachable ⟨i,x⟩ ⟨i,y⟩ ↔ (G i).Reachable x y := by
  constructor
  · rintro ⟨p⟩
    have aux : ∀ {a b : Sigma V} (p : (graph G).Walk a b),
      ∃ e : a.1 = b.1, (G b.1).Reachable (e ▸ a.2) b.2 := by
      intro a b p
      induction p with
      | nil => exact ⟨rfl, SimpleGraph.Reachable.refl _⟩
      | @cons a b c h p ih =>
        rcases a with ⟨i,a⟩; rcases b with ⟨j,b⟩; rcases c with ⟨k,c⟩
        obtain ⟨hij,hab⟩ := h
        obtain ⟨hjk,hbc⟩ := ih
        cases hij; cases hjk
        exact ⟨rfl, hab.reachable.trans hbc⟩
    obtain ⟨e,he⟩ := aux p
    exact he
  · intro h
    exact h.map (inclusion G i).toHom

lemma component_same (G : ∀ i, SimpleGraph (V i)) (i : ι) (x : V i) :
    component (graph G) ⟨i,x⟩ = (component (G i) x).map
      (Function.Embedding.sigmaMk i) := by
  classical
  ext y
  rcases y with ⟨j,y⟩
  by_cases hij : i = j
  · subst j
    simp [component, reachable_same, Function.Embedding.sigmaMk_apply]
  · have hn : ¬ (graph G).Reachable ⟨i,x⟩ ⟨j,y⟩ := fun h => hij (reachable_index h)
    simp [component, hn, hij, Function.Embedding.sigmaMk_apply]

noncomputable def freeEquiv (pins : ∀ i, Finset (V i)) :
    FreeSites (sites pins) ≃ Sigma (fun i => FreeSites (pins i)) where
  toFun x := ⟨x.1.1, ⟨x.1.2, by simpa [sites] using x.2⟩⟩
  invFun x := ⟨⟨x.1,x.2.1⟩, by simpa using x.2.2⟩
  left_inv := by rintro ⟨⟨i,x⟩,hx⟩; rfl
  right_inv := by rintro ⟨i,⟨x,hx⟩⟩; rfl

noncomputable def heightEquiv (pins : ∀ i, Finset (V i)) :
    (FreeSites (sites pins) → ℝ) ≃ᵐ (∀ i, FreeSites (pins i) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (freeEquiv pins)).trans
    (MeasurableEquiv.piCurry (fun (i : ι) (_ : FreeSites (pins i)) => ℝ))

omit [DecidableEq ι] [∀ index, Fintype (V index)] [∀ index, DecidableEq (V index)] in
@[simp] lemma heightEquiv_apply (pins : ∀ i, Finset (V i))
    (h : FreeSites (sites pins) → ℝ) (i : ι) (x : FreeSites (pins i)) :
    heightEquiv pins h i x = h ⟨⟨i,x⟩, by simpa using x.2⟩ := rfl

omit [∀ index, Fintype (V index)] in
lemma extendHeight_same (pins : ∀ i, Finset (V i)) (β : ∀ i, V i → ℝ)
    (h : FreeSites (sites pins) → ℝ) (i : ι) (x : V i) :
    extendHeight (sites pins) (fun y => β y.1 y.2) h ⟨i,x⟩ =
      extendHeight (pins i) (β i) (heightEquiv pins h i) x := by
  classical
  by_cases hx : x ∈ pins i <;> simp [extendHeight, hx]

omit [∀ index, Fintype (V index)] in
lemma polytope_same (G : ∀ i, SimpleGraph (V i)) (pins walls : ∀ i, Finset (V i))
    (β : ∀ i, V i → ℝ) (I : ∀ i, V i → Set ℝ) :
    heightPolytope (graph G) (sites pins) (sites walls) (fun x => β x.1 x.2)
      (fun x => I x.1 x.2) = heightEquiv pins ⁻¹'
        Set.pi Set.univ (fun i => heightPolytope (G i) (pins i) (walls i) (β i) (I i)) := by
  ext h
  constructor
  · rintro ⟨hg,hw⟩ i _
    exact ⟨fun x y hxy => by simpa [extendHeight_same] using hg ⟨i,x⟩ ⟨i,y⟩ ((graph_adj_same G i x y).mpr hxy),
      fun x hx => by simpa [extendHeight_same] using hw ⟨i,x⟩ ((mem_sites walls i x).mpr hx)⟩
  · intro hh
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ ⟨hij,hxy⟩
      cases hij
      simpa [extendHeight_same] using (hh i (Set.mem_univ _)).1 x y hxy
    · rintro ⟨i,x⟩ hx
      simpa [extendHeight_same] using (hh i (Set.mem_univ _)).2 x ((mem_sites walls i x).mp hx)

omit [Fintype ι] [DecidableEq ι] [∀ index, Fintype (V index)]
  [∀ index, DecidableEq (V index)] in
lemma contactGraph_same (G : ∀ i, SimpleGraph (V i)) (h : (Sigma V) → ℝ) (s : ℝ) :
    contactGraph (graph G) h s = graph (fun i => contactGraph (G i) (fun x => h ⟨i,x⟩) s) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  constructor
  · rintro ⟨⟨hij,hxy⟩,hc⟩
    cases hij; exact ⟨rfl,hxy,hc⟩
  · rintro ⟨hij,hxy,hc⟩
    cases hij; exact ⟨⟨rfl,hxy⟩,hc⟩

omit [DecidableEq ι] [∀ index, Fintype (V index)] [∀ index, DecidableEq (V index)] in
lemma shiftGraph_same (G : ∀ i, SimpleGraph (V i)) (ground : ∀ i, Finset (V i)) :
    shiftGraph (graph G) (sites ground) = graph (fun i => shiftGraph (G i) (ground i)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  constructor
  · rintro ⟨⟨hij,hxy⟩,hc⟩
    cases hij; exact ⟨rfl,hxy,by simpa using hc⟩
  · rintro ⟨hij,hxy,hc⟩
    cases hij; exact ⟨⟨rfl,hxy⟩,by simpa using hc⟩

lemma prescription_same (G : ∀ i, SimpleGraph (V i)) (ground : ∀ i, Finset (V i))
    (f : ∀ i, V i → ℝ) (i : ι) (x : V i) :
    prescription (graph G) (sites ground) (fun y => f y.1 y.2) ⟨i,x⟩ =
      prescription (G i) (ground i) (f i) x := by
  classical
  have hd : Disjoint ((component (G i) x).map (Function.Embedding.sigmaMk i)) (sites ground) ↔
      Disjoint (component (G i) x) (ground i) := by
    simp [Finset.disjoint_left]
  simp only [prescription, component_same, hd, Finset.sum_map, Finset.card_map]
  rfl

lemma averagedShift_same (G : ∀ i, SimpleGraph (V i)) (ground : ∀ i, Finset (V i))
    (f : ∀ i, V i → ℝ) (h : Sigma V → ℝ) (s₀ s₁ : ℝ) (i : ι) (x : V i) :
    averagedShift (graph G) (sites ground) (fun y => f y.1 y.2) h s₀ s₁ ⟨i,x⟩ =
      averagedShift (G i) (ground i) (f i) (fun y => h ⟨i,y⟩) s₀ s₁ x := by
  simp only [averagedShift, contactGraph_same, prescription_same]

omit [DecidableEq ι] [∀ index, DecidableEq (V index)] in
lemma neighbors_same (G : ∀ i, SimpleGraph (V i)) (i : ι) (x : V i) :
    neighbors (graph G) ⟨i,x⟩ = (neighbors (G i) x).map (Function.Embedding.sigmaMk i) := by
  classical
  ext y
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, Function.Embedding.sigmaMk_apply]
  constructor
  · rcases y with ⟨j,y⟩
    rintro ⟨hij,hxy⟩
    cases hij
    exact ⟨y,hxy,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨rfl,hy⟩

lemma localSites_same (G : ∀ i, SimpleGraph (V i)) (ground : ∀ i, Finset (V i)) :
    localSites (graph G) (sites ground) = sites (fun i => localSites (G i) (ground i)) := by
  classical
  ext ⟨i,x⟩
  simp only [mem_sites, localSites, Finset.mem_filter, Finset.mem_univ, true_and, mem_sites]
  constructor
  · rintro (h | ⟨⟨j,y⟩,hy,⟨hij,hxy⟩⟩)
    · exact Or.inl h
    · cases hij
      exact Or.inr ⟨y,by simpa using hy,hxy⟩
  · rintro (h | ⟨y,hy,hxy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨i,y⟩,by simpa using hy,⟨rfl,hxy⟩⟩

lemma freeShift_same (G : ∀ i, SimpleGraph (V i)) (ground pins : ∀ i, Finset (V i))
    (β f : ∀ i, V i → ℝ) (s₀ s₁ : ℝ) (h : FreeSites (sites pins) → ℝ)
    (i : ι) (x : FreeSites (pins i)) :
    heightEquiv pins (freeShift (shiftGraph (graph G) (sites ground)) (sites ground)
      (sites pins) (fun y => β y.1 y.2) (fun y => f y.1 y.2) s₀ s₁ h) i x =
    freeShift (shiftGraph (G i) (ground i)) (ground i) (pins i) (β i) (f i)
      s₀ s₁ (heightEquiv pins h i) x := by
  simp only [heightEquiv_apply, freeShift, shiftGraph_same, averagedShift_same,
    extendHeight_same]

end DisjointUnion

end FeasibleShift

end OAI
