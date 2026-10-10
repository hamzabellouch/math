import OAI.Geometry.KahlerSplitting.Model

namespace OAI

section

noncomputable section
open Set
namespace RectangleGrid
variable {P Q X : Type*}

def band (k i j : ℕ) : Prop := i ≤ j+k ∧ j ≤ i+k

structure Band (T : Set (P × Q → X)) (D : ℕ → P × Q → X)
    (lo hi : ℕ → P) (bot top : ℕ → Q) (k : ℕ) where
  tile : ℕ → ℕ → P × Q → X
  member : ∀ i j, band k i j → tile i j ∈ T
  diagonal : ∀ i, tile i i=D i
  hseam : ∀ i j, band k i j → band k (i+1) j →
    ∀ y, tile i j (hi i,y)=tile (i+1) j (lo (i+1),y)
  vseam : ∀ i j, band k i j → band k i (j+1) →
    ∀ x, tile i j (x,top j)=tile i (j+1) (x,bot (j+1))

theorem band_extend (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (horizontal : ∀ f ∈ T, ∀ q, (fun p ↦ f (p,q)) ∈ H)
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (D : ℕ → P × Q → X) (lo hi : ℕ → P) (bot top : ℕ → Q)
    (join : ∀ i, D i (hi i,top i)=D (i+1) (lo (i+1),bot (i+1)))
    (k : ℕ) (G : Band T D lo hi bot top k) :
    ∃ F : Band T D lo hi bot top (k+1), ∀ i j, band k i j → F.tile i j=G.tile i j := by
  classical
  have up (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : i < j) :
      ∃ f ∈ T, (∀ x, f (x,bot j)=G.tile i (j-1) (x,top (j-1))) ∧
        (∀ y, f (hi i,y)=G.tile (i+1) j (lo (i+1),y)) := by
    have b₁ : band k i (j-1) := by unfold band at *; omega
    have b₂ : band k (i+1) j := by unfold band at *; omega
    apply fill _ (horizontal _ (G.member _ _ b₁) _) _ (vertical _ (G.member _ _ b₂) _)
    by_cases he : j=i+1
    · subst j
      simpa only [Nat.add_sub_cancel,G.diagonal] using join i
    · have b₃ : band k (i+1) (j-1) := by unfold band at *; omega
      have e₁ := G.hseam i (j-1) b₁ b₃ (top (j-1))
      have e₂ := G.vseam (i+1) (j-1) b₃ (by simpa only [Nat.sub_add_cancel (by omega : 1≤ j)] using b₂) (lo (i+1))
      exact e₁.trans (by simpa only [Nat.sub_add_cancel (by omega : 1≤ j)] using e₂)
  have down (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : j < i) :
      ∃ f ∈ T, (∀ x, f (x,top j)=G.tile i (j+1) (x,bot (j+1))) ∧
        (∀ y, f (lo i,y)=G.tile (i-1) j (hi (i-1),y)) := by
    have b₁ : band k i (j+1) := by unfold band at *; omega
    have b₂ : band k (i-1) j := by unfold band at *; omega
    apply fill _ (horizontal _ (G.member _ _ b₁) _) _ (vertical _ (G.member _ _ b₂) _)
    by_cases he : i=j+1
    · subst i
      simpa only [Nat.add_sub_cancel,G.diagonal] using (join j).symm
    · have b₃ : band k (i-1) (j+1) := by unfold band at *; omega
      have e₁ := G.hseam (i-1) (j+1) b₃ (by simpa only [Nat.sub_add_cancel (by omega : 1≤ i)] using b₁) (bot (j+1))
      have e₂ := G.vseam (i-1) j b₂ b₃ (hi (i-1))
      simp only [Nat.sub_add_cancel (by omega : 1≤ i)] at e₁
      exact e₁.symm.trans e₂.symm
  let f (i j : ℕ) : P × Q → X :=
    if h : band k i j then G.tile i j else
    if hb : band (k+1) i j then
      if hij : i < j then (up i j hb h hij).choose
      else (down i j hb h (by unfold band at *; omega)).choose
    else D 0
  have old (i j : ℕ) (h : band k i j) : f i j=G.tile i j := by simp only [f,dite_eq_left h]
  have upper (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : i < j) :
      f i j ∈ T ∧ (∀ x, f i j (x,bot j)=G.tile i (j-1) (x,top (j-1))) ∧
        (∀ y, f i j (hi i,y)=G.tile (i+1) j (lo (i+1),y)) := by
    simpa only [f,dite_eq_right hn,dite_eq_left h,dite_eq_left hij] using (up i j h hn hij).choose_spec
  have lower (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : j < i) :
      f i j ∈ T ∧ (∀ x, f i j (x,top j)=G.tile i (j+1) (x,bot (j+1))) ∧
        (∀ y, f i j (lo i,y)=G.tile (i-1) j (hi (i-1),y)) := by
    simpa only [f,dite_eq_right hn,dite_eq_left h,dite_eq_right (not_lt.mpr (Nat.le_of_lt hij))] using
      (down i j h hn hij).choose_spec
  refine ⟨⟨f,?_,?_,?_,?_⟩,old⟩
  · intro i j h
    by_cases ho : band k i j
    · rw [old i j ho]; exact G.member i j ho
    · by_cases hij : i < j
      · exact (upper i j h ho hij).1
      · exact (lower i j h ho (by unfold band at *; omega)).1
  · intro i
    rw [old i i (by unfold band; omega),G.diagonal]
  · intro i j ha hb y
    by_cases hA : band k i j
    · rw [old i j hA]
      by_cases hB : band k (i+1) j
      · rw [old (i+1) j hB]; exact G.hseam i j hA hB y
      · have e := (lower (i+1) j hb hB (by unfold band at *; omega)).2.2 y
        simpa only [Nat.add_sub_cancel] using e.symm
    · have hB : band k (i+1) j := by unfold band at *; omega
      rw [old (i+1) j hB]
      exact (upper i j ha hA (by unfold band at *; omega)).2.2 y
  · intro i j ha hb x
    by_cases hA : band k i j
    · rw [old i j hA]
      by_cases hB : band k i (j+1)
      · rw [old i (j+1) hB]; exact G.vseam i j hA hB x
      · have e := (upper i (j+1) hb hB (by unfold band at *; omega)).2.1 x
        simpa only [Nat.add_sub_cancel] using e.symm
    · have hB : band k i (j+1) := by unfold band at *; omega
      rw [old i (j+1) hB]
      exact (lower i j ha hA (by unfold band at *; omega)).2.1 x

theorem diagonal_grid (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (horizontal : ∀ f ∈ T, ∀ q, (fun p ↦ f (p,q)) ∈ H)
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (D : ℕ → P × Q → X) (hD : ∀ i, D i ∈ T)
    (lo hi : ℕ → P) (bot top : ℕ → Q)
    (join : ∀ i, D i (hi i,top i)=D (i+1) (lo (i+1),bot (i+1))) :
    ∃ f : ℕ → ℕ → P × Q → X, (∀ i j, f i j ∈ T) ∧
      (∀ i, f i i=D i) ∧
      (∀ i j y, f i j (hi i,y)=f (i+1) j (lo (i+1),y)) ∧
      (∀ i j x, f i j (x,top j)=f i (j+1) (x,bot (j+1))) := by
  classical
  let seed : Band T D lo hi bot top 0 :=
    ⟨fun i _ ↦ D i,fun i _ _ ↦ hD i,fun _ ↦ rfl,
      fun i j ha hb ↦ by unfold band at ha hb; omega,
      fun i j ha hb ↦ by unfold band at ha hb; omega⟩
  have ext := band_extend H V T horizontal vertical fill D lo hi bot top join
  let seq : (k : ℕ) → Band T D lo hi bot top k :=
    Nat.rec seed (fun k G ↦ (ext k G).choose)
  have stable (k i j : ℕ) (h : band k i j) :
      (seq (k+1)).tile i j=(seq k).tile i j := (ext k (seq k)).choose_spec i j h
  have stable' (k l : ℕ) (hkl : k≤ l) (i j : ℕ) (h : band k i j) :
      (seq l).tile i j=(seq k).tile i j := by
    induction l, hkl using Nat.le_induction with
    | base => rfl
    | succ l hkl ih =>
      exact (stable l i j (by unfold band at *; omega)).trans ih
  let f (i j : ℕ) := (seq (i+j)).tile i j
  have atBand (k i j : ℕ) (h : i+j≤ k) : f i j=(seq k).tile i j :=
    (stable' (i+j) k h i j (by unfold band; omega)).symm
  refine ⟨f,fun i j ↦ (seq (i+j)).member i j (by unfold band; omega),
    fun i ↦ (seq (i+i)).diagonal i,?_,?_⟩
  · intro i j y
    rw [atBand (i+j+1) i j (by omega),atBand (i+j+1) (i+1) j (by omega)]
    exact (seq (i+j+1)).hseam i j (by unfold band; omega) (by unfold band; omega) y
  · intro i j x
    rw [atBand (i+j+1) i j (by omega),atBand (i+j+1) i (j+1) (by omega)]
    exact (seq (i+j+1)).vseam i j (by unfold band; omega) (by unfold band; omega) x

end RectangleGrid
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace IntervalChain
variable {X : Type*}

def cell (t : ℕ → I) (i : ℕ) := Icc (t i) (t (i+1))

lemma overlap (t : ℕ → I) (ht : Monotone t)
    (f : ∀ i, cell t i → X)
    (seam : ∀ i, f i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩ =
      f (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩)
    (i j : ℕ) (x : I) (hi : x ∈ cell t i) (hj : x ∈ cell t j) :
    f i ⟨x,hi⟩=f j ⟨x,hj⟩ := by
  have half : ∀ j i, i ≤ j → ∀ (x : I) (hi : x ∈ cell t i) (hj : x ∈ cell t j),
      f i ⟨x,hi⟩=f j ⟨x,hj⟩ := by
    intro j
    induction j with
    | zero => intro i hij x hi hj; have he : i=0 := Nat.eq_zero_of_le_zero hij; subst i; rfl
    | succ j ih =>
      intro i hij x hi hj
      by_cases he : i=j+1
      · subst i; rfl
      have hij' : i ≤ j := by omega
      have hx : x=t (j+1) := le_antisymm (hi.2.trans (ht (by omega))) hj.1
      subst x
      exact (ih i hij' _ hi ⟨ht (Nat.le_succ j),le_rfl⟩).trans (seam j)
  rcases le_total i j with h|h
  · exact half j i h x hi hj
  · exact (half i j h x hj hi).symm

lemma covers (t : ℕ → I) (ht0 : t 0=0) (ht : Monotone t)
    (N : ℕ) (hN : t N=1) (x : I) : ∃ i ≤ N, x ∈ cell t i := by
  by_cases hx : x=1
  · subst x
    refine ⟨N,le_rfl,?_,?_⟩
    · simp only [hN,le_refl]
    · exact (hN ▸ ht (Nat.le_succ N))
  have hx1 : x < 1 := lt_of_le_of_ne le_top hx
  have hm : ∃ i, x < t (i+1) := ⟨N,lt_of_lt_of_le hx1 (hN ▸ ht (Nat.le_succ N))⟩
  let i := Nat.find hm
  have hiN : i ≤ N := Nat.find_min' hm (lt_of_lt_of_le hx1 (hN ▸ ht (Nat.le_succ N)))
  refine ⟨i,hiN,?_,(Nat.find_spec hm).le⟩
  cases hi : i with
  | zero => simp [ht0]
  | succ j =>
    have hn := Nat.find_min hm (show j < i from by omega)
    exact le_of_not_gt (by simpa only [hi] using hn)

end IntervalChain
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace PathSubdivision
variable {P X : Type*} [TopologicalSpace P]

theorem parameterize (α : I → X) (Q : (P → X) → Prop)
    (local_param : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
      ∃ f : P → X, Q f ∧ ∃ a : U → P, Continuous a ∧ ∀ y, f (a y)=α y) :
    ∃ t : ℕ → I, t 0=0 ∧ Monotone t ∧ (∃ N, ∀ m ≥ N, t m=1) ∧
      ∃ f : ℕ → P → X, (∀ i, Q (f i)) ∧
      ∃ a : ∀ i, IntervalChain.cell t i → P, (∀ i, Continuous (a i)) ∧
        ∀ i y, f i (a i y)=α y := by
  classical
  choose U hU hx f hf a ha he using local_param
  have cover : univ ⊆ ⋃ x, U x := fun x _ ↦ mem_iUnion.mpr ⟨x,hx x⟩
  obtain ⟨t,ht0,ht,hN,hsub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval hU cover
  choose k hk using hsub
  refine ⟨t,ht0,ht,hN,fun i ↦ f (k i),fun i ↦ hf (k i),
    fun i y ↦ a (k i) ⟨y,hk i y.property⟩,?_,?_⟩
  · intro i
    exact (ha (k i)).comp (continuous_subtype_val.subtype_mk _)
  · intro i y
    exact he (k i) _

end PathSubdivision
end
end

section

noncomputable section
open Set
namespace RectangleGrid
variable {P Q X : Type*}

theorem row (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (a : ℕ → P → X) (ha : ∀ i, a i ∈ H) (lo hi : ℕ → P)
    (join : ∀ i, a i (hi i)=a (i+1) (lo (i+1)))
    (b : Q → X) (hb : b ∈ V) (q : Q) (corner : a 0 (lo 0)=b q) :
    ∃ f : ℕ → P × Q → X, (∀ i, f i ∈ T) ∧
      (∀ i x, f i (x,q)=a i x) ∧ (∀ y, f 0 (lo 0,y)=b y) ∧
      (∀ i y, f i (hi i,y)=f (i+1) (lo (i+1),y)) := by
  classical
  let State (i : ℕ) := {c : Q → X // c ∈ V ∧ a i (lo i)=c q}
  have exist (i : ℕ) (c : State i) := fill (a i) (ha i) c.val c.property.1 (lo i) q c.property.2
  let tile (i : ℕ) (c : State i) : P × Q → X := (exist i c).choose
  have tileT (i : ℕ) (c : State i) : tile i c ∈ T := (exist i c).choose_spec.1
  have bottom (i : ℕ) (c : State i) (x : P) : tile i c (x,q)=a i x :=
    (exist i c).choose_spec.2.1 x
  have left (i : ℕ) (c : State i) (y : Q) : tile i c (lo i,y)=c.val y :=
    (exist i c).choose_spec.2.2 y
  let next (i : ℕ) (c : State i) : State (i+1) :=
    ⟨fun y ↦ tile i c (hi i,y),vertical _ (tileT i c) _,((bottom i c (hi i)).trans (join i)).symm⟩
  let seq : (i : ℕ) → State i := Nat.rec ⟨b,hb,corner⟩ next
  refine ⟨fun i ↦ tile i (seq i),fun i ↦ tileT i _,fun i x ↦ bottom i _ x,left 0 _,?_⟩
  intro i y
  exact (left (i+1) (seq (i+1)) y).symm

theorem grid (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (horizontal : ∀ f ∈ T, ∀ q, (fun p ↦ f (p,q)) ∈ H)
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (a : ℕ → P → X) (ha : ∀ i, a i ∈ H) (lo hi : ℕ → P)
    (joinA : ∀ i, a i (hi i)=a (i+1) (lo (i+1)))
    (b : ℕ → Q → X) (hb : ∀ j, b j ∈ V) (bot top : ℕ → Q)
    (joinB : ∀ j, b j (top j)=b (j+1) (bot (j+1)))
    (corner : a 0 (lo 0)=b 0 (bot 0)) :
    ∃ f : ℕ → ℕ → P × Q → X, (∀ i j, f i j ∈ T) ∧
      (∀ i x, f i 0 (x,bot 0)=a i x) ∧
      (∀ j y, f 0 j (lo 0,y)=b j y) ∧
      (∀ i j y, f i j (hi i,y)=f (i+1) j (lo (i+1),y)) ∧
      (∀ i j x, f i j (x,top j)=f i (j+1) (x,bot (j+1))) := by
  classical
  let State (j : ℕ) := {c : ℕ → P → X //
    (∀ i, c i ∈ H) ∧ (∀ i, c i (hi i)=c (i+1) (lo (i+1))) ∧ c 0 (lo 0)=b j (bot j)}
  have exist (j : ℕ) (c : State j) :=
    row H V T vertical fill c.val c.property.1 lo hi c.property.2.1
      (b j) (hb j) (bot j) c.property.2.2
  let tiles (j : ℕ) (c : State j) := (exist j c).choose
  have ht (j : ℕ) (c : State j) (i : ℕ) : tiles j c i ∈ T := (exist j c).choose_spec.1 i
  have bottom (j : ℕ) (c : State j) (i : ℕ) (x : P) :
      tiles j c i (x,bot j)=c.val i x := (exist j c).choose_spec.2.1 i x
  have left (j : ℕ) (c : State j) (y : Q) :
      tiles j c 0 (lo 0,y)=b j y := (exist j c).choose_spec.2.2.1 y
  have seam (j : ℕ) (c : State j) (i : ℕ) (y : Q) :
      tiles j c i (hi i,y)=tiles j c (i+1) (lo (i+1),y) :=
    (exist j c).choose_spec.2.2.2 i y
  let next (j : ℕ) (c : State j) : State (j+1) :=
    ⟨fun i x ↦ tiles j c i (x,top j),fun i ↦ horizontal _ (ht j c i) _,
      fun i ↦ seam j c i _,(left j c (top j)).trans (joinB j)⟩
  let seq : (j : ℕ) → State j := Nat.rec ⟨a,ha,joinA,corner⟩ next
  refine ⟨fun i j ↦ tiles j (seq j) i,fun i j ↦ ht j _ i,
    bottom 0 _,fun j y ↦ left j _ y,fun i j y ↦ seam j _ i y,?_⟩
  intro i j x
  exact (bottom (j+1) (seq (j+1)) i x).symm

end RectangleGrid
end
end

end OAI
