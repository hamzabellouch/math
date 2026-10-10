import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory

namespace OAI

section

/-! # Full initial oriental faces from positive chains

The chain support proof determines every table entry from the initial
segment containing its two object boundaries. No atom-generation theorem
is used in this initial-face specialization.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory
open scoped BigOperators

/-- Degree zero of a cell is the named vertex of its object boundary. -/
theorem table_zero_eq_vertex (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (a : Bool) :
    x.table a 0 = Finsupp.single (vertexBasis (objectIndex h a x)) 1 := by
  have he := congrArg Subtype.val
    ((objectsEquiv h m).symm_apply_apply ((h.object m).boundaryObject a x))
  have ht := congrArg (fun y : h.object m => y.table false 0) he
  exact ht.symm

/-- Every positive chain in the table is supported below the two endpoints. -/
theorem table_support_below (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (q : Fin (m+1))
    (hs : objectIndex h false x ≤ q) (ht : objectIndex h true x ≤ q) :
    ∀ p a (b : Basis m p), q < b (Fin.last p) → x.table a p b = 0 := by
  classical
  intro p
  induction p with
  | zero =>
    intro a b hb
    rw [table_zero_eq_vertex h x a]
    apply Finsupp.single_eq_of_ne
    intro he
    have hv := congrArg (fun c : Basis m 0 => c 0) he
    have ha : objectIndex h a x ≤ q := by cases a <;> assumption
    exact (not_le_of_gt hb) (hv ▸ ha)
  | succ p ih =>
    intro a b hb
    apply positive_support_below_of_boundary q (x.table a (p+1)) (x.positive a (p+1)) _ b hb
    intro t hqt
    have he := congrArg (fun c : Chains m p => c t) (x.boundary a p)
    exact he.trans (by simp only [Finsupp.sub_apply, ih true t hqt, ih false t hqt, sub_self])

/-- A vertex map fixing the vertices of a basis simplex fixes its chain. -/
theorem mapBasis_eq_self_of_fixes {m p : ℕ} (f : Fin (m+1) →o Fin (m+1))
    (b : Basis m p) (hf : ∀ i, f (b i) = b i) :
    mapBasis f p b = Finsupp.single b 1 := by
  have hm : StrictMono (fun i => f (b i)) := by
    intro i j hij
    change f (b i) < f (b j)
    rw [hf i, hf j]
    exact b.strictMono hij
  rw [mapBasis, dite_eq_left hm]
  congr 1
  exact DFunLike.ext _ _ hf

/-- A chain supported on fixed basis simplices is fixed by the induced map. -/
theorem mapChains_eq_self_of_fixes {m p : ℕ} (f : Fin (m+1) →o Fin (m+1))
    (c : Chains m p) (hf : ∀ b ∈ c.support, ∀ i, f (b i) = b i) :
    mapChains f p c = c := by
  classical
  simp only [mapChains, Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    _ = ∑ b ∈ c.support, Finsupp.single b (c b) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [mapBasis_eq_self_of_fixes f b (hf b hb)]
      simp
    _ = c := Finsupp.sum_single c

/-- Clamping to an initial segment fixes an entire cell whose endpoints
already lie in that segment. -/
theorem initialClamp_fixes_cell (h : NormalizedSimplexIdentities) {q m : ℕ}
    (hqm : q ≤ m) (x : h.object m)
    (hs : (objectIndex h false x).val ≤ q) (ht : (objectIndex h true x).val ≤ q) :
    (h.map ((initialFace hqm).toOrderHom.comp (initialClamp hqm))).toFun x = x := by
  apply DirectedComplex.Cell.ext
  funext a p
  change mapChains ((initialFace hqm).toOrderHom.comp (initialClamp hqm)) p (x.table a p) = _
  apply mapChains_eq_self_of_fixes
  intro b hb i
  have hlast : (b (Fin.last p)).val ≤ q := by
    by_contra hn
    have he := table_support_below h x (⟨q, by omega⟩ : Fin (m+1)) hs ht p a b (Nat.lt_of_not_ge hn)
    exact (Finsupp.mem_support_iff.mp hb) he
  have hi : (b i).val ≤ q :=
    (show (b i).val ≤ (b (Fin.last p)).val from b.monotone (Fin.le_last i)).trans hlast
  apply Fin.ext
  exact min_eq_left hi

/-- Every cell with both endpoints in an initial face lies in its actual image. -/
theorem initialFace_full (h : NormalizedSimplexIdentities) {q m : ℕ}
    (hqm : q ≤ m) (x : h.object m)
    (hs : (objectIndex h false x).val ≤ q) (ht : (objectIndex h true x).val ≤ q) :
    x ∈ Set.range (h.map (initialFace hqm).toOrderHom).toFun := by
  refine ⟨(h.map (initialClamp hqm)).toFun x, ?_⟩
  have he := congrArg (fun f : h.object m ⟶ h.object m => f.toFun x)
    (h.map_comp (initialClamp hqm) (initialFace hqm).toOrderHom)
  exact he.symm.trans (initialClamp_fixes_cell h hqm x hs ht)

end Thomason.Construction.SimplexComplex

end

section

/-! # Full final oriental faces from positive chain support

No atom-generation hypothesis is used: the lower support bound propagates
through the signed table equations, and the final clamp fixes every chain.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory

/-- Every chain in the cell table is supported above both object boundaries. -/
theorem table_support_above (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (q : Fin (m + 1))
    (hs : q ≤ objectIndex h false x) (ht : q ≤ objectIndex h true x) :
    ∀ p a (b : Basis m p), b 0 < q → x.table a p b = 0 := by
  classical
  intro p
  induction p with
  | zero =>
    intro a b hb
    rw [table_zero_eq_vertex h x a]
    apply Finsupp.single_eq_of_ne
    intro he
    have hv := congrArg (fun c : Basis m 0 => c 0) he
    have ha : q ≤ objectIndex h a x := by cases a <;> assumption
    exact (not_le_of_gt hb) (hv ▸ ha)
  | succ p ih =>
    intro a b hb
    apply positive_support_above_of_boundary q (x.table a (p + 1)) (x.positive a (p + 1)) _ b hb
    intro t hqt
    have he := congrArg (fun c : Chains m p => c t) (x.boundary a p)
    exact he.trans (by simp only [Finsupp.sub_apply, ih true t hqt, ih false t hqt, sub_self])

/-- Clamping into the final face fixes every cell whose endpoints lie there. -/
theorem finalClamp_fixes_cell (h : NormalizedSimplexIdentities) {q m : ℕ}
    (hqm : q ≤ m) (x : h.object m)
    (hs : m - q ≤ (objectIndex h false x).val) (ht : m - q ≤ (objectIndex h true x).val) :
    (h.map ((finalFace hqm).toOrderHom.comp (finalClamp hqm))).toFun x = x := by
  apply DirectedComplex.Cell.ext
  funext a p
  change mapChains ((finalFace hqm).toOrderHom.comp (finalClamp hqm)) p (x.table a p) = _
  apply mapChains_eq_self_of_fixes
  intro b hb i
  have hfirst : m - q ≤ (b 0).val := by
    by_contra hn
    have he := table_support_above h x (⟨m - q, by omega⟩ : Fin (m + 1)) hs ht p a b
      (Nat.lt_of_not_ge hn)
    exact (Finsupp.mem_support_iff.mp hb) he
  have hi : m - q ≤ (b i).val :=
    hfirst.trans (show (b 0).val ≤ (b i).val from b.monotone (Fin.zero_le i))
  apply Fin.ext
  change m - q + ((b i).val - (m - q)) = (b i).val
  exact Nat.add_sub_of_le hi

/-- The actual final ordinal face is full on its endpoint vertices. -/
theorem finalFace_full (h : NormalizedSimplexIdentities) {q m : ℕ}
    (hqm : q ≤ m) (x : h.object m)
    (hs : m - q ≤ (objectIndex h false x).val) (ht : m - q ≤ (objectIndex h true x).val) :
    x ∈ Set.range (h.map (finalFace hqm).toOrderHom).toFun := by
  refine ⟨(h.map (finalClamp hqm)).toFun x, ?_⟩
  have he := congrArg (fun f : h.object m ⟶ h.object m => f.toFun x)
    (h.map_comp (finalClamp hqm) (finalFace hqm).toOrderHom)
  exact he.symm.trans (finalClamp_fixes_cell h hqm x hs ht)

end Thomason.Construction.SimplexComplex

end

section

/-!
# The actual fibres of binary labels on orientals

The fibre on a value of a monotone vertex label is the full strict
subcategory on those vertices, with an isomorphism that commutes with its
ambient inclusion. Thus the proved full-face calculation applies to the
same fibre functors that preserve colimits.
-/

namespace Thomason.Construction.SimplexComplex

open CategoryTheory StrictOmegaCategory

/-- A binary vertex label extends to a strict walking-arrow label. -/
noncomputable def binaryLabel (h : NormalizedSimplexIdentities) {m : ℕ}
    (b : Fin (m + 1) →o Fin 2) : h.object m ⟶ StrictPoset.category (Fin 2) :=
  h.ordinalLabel m ≫ StrictPoset.map b

/-- On every cell, a binary fibre is detected on both object boundaries. -/
theorem binaryLabel_fullCell_iff (h : NormalizedSimplexIdentities) {m : ℕ}
    (b : Fin (m + 1) →o Fin 2) (e : Fin 2) (x : h.object m) :
    (h.object m).FullCell {z | (binaryLabel h b).toFun z = StrictPoset.identity e} x ↔
      FullOnVertices h {i | b i = e} x := by
  rw [fullCell_label_iff]
  constructor
  · intro he
    exact ⟨congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) he,
      congrArg (fun z : StrictPoset.Cell (Fin 2) => z.last) he⟩
  · rintro ⟨hs, ht⟩
    apply StrictPoset.Cell.ext
    · exact hs
    · exact ht

/-- Forget only the definitional description of fibre membership. -/
noncomputable def labelFiberToVertices (h : NormalizedSimplexIdentities) {m : ℕ}
    (b : Fin (m + 1) →o Fin 2) (e : Fin 2) :
    labelFiber (binaryLabel h b) e ⟶ vertexFullSubcategory h {i | b i = e} where
  toFun x := ⟨x.val, (fullCell_vertices_iff h _ _).mpr
    ((binaryLabel_fullCell_iff h b e x.val).mp x.property)⟩
  map_face _ _ _ := Subtype.ext rfl
  map_comp _ _ _ _ _ := Subtype.ext rfl

/-- The label fibre is isomorphic to the actual full subcategory on its vertices. -/
noncomputable def labelFiberVerticesIso (h : NormalizedSimplexIdentities) {m : ℕ}
    (b : Fin (m + 1) →o Fin 2) (e : Fin 2) :
    labelFiber (binaryLabel h b) e ≅ vertexFullSubcategory h {i | b i = e} :=
  isoOfBijective (labelFiberToVertices h b e)
    ⟨by
        intro x y he
        have hv := congrArg (fun z : vertexFullSubcategory h {i | b i = e} => z.val) he
        exact Subtype.ext hv,
      fun y =>
      ⟨⟨y.val, (binaryLabel_fullCell_iff h b e y.val).mpr
        ((fullCell_vertices_iff h _ _).mp y.property)⟩, rfl⟩⟩

/-- The fibre isomorphism commutes with the given ambient inclusion. -/
theorem labelFiberVerticesIso_inclusion (h : NormalizedSimplexIdentities) {m : ℕ}
    (b : Fin (m + 1) →o Fin 2) (e : Fin 2) :
    (labelFiberVerticesIso h b e).hom ≫
      (h.object m).fullInclusion {x | objectIndex h false x ∈ {i | b i = e}} =
      labelFiberInclusion (binaryLabel h b) e := by
  apply StrictOmegaCategory.Hom.ext
  rfl

/-- The zero-labelled vertices always form an initial segment. -/
theorem binaryLabel_zero_initial {m : ℕ} (b : Fin (m + 1) →o Fin 2) :
    IsLowerSet {i | b i = 0} := by
  intro i j hij hj
  exact le_antisymm ((b.monotone hij).trans_eq hj) (Fin.zero_le _)

/-- The one-labelled vertices always form a final segment. -/
theorem binaryLabel_one_final {m : ℕ} (b : Fin (m + 1) →o Fin 2) :
    IsUpperSet {i | b i = 1} := by
  intro i j hij hi
  apply le_antisymm
  · exact Fin.le_last _
  · exact hi ▸ b.monotone hij

/-- Nonempty zero-fibres are precisely smaller orientals. -/
theorem zeroFiber_oriental {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {m : ℕ} (b : Fin (m + 1) →o Fin 2) (hne : Set.Nonempty {i | b i = 0}) :
    ∃ q : Fin (m + 1), Nonempty (h.object q.val ≅ labelFiber (binaryLabel h b) 0) := by
  obtain ⟨q, ⟨e⟩⟩ := initialSegment_oriental a (binaryLabel_zero_initial b) hne
  exact ⟨q, ⟨e ≪≫ (labelFiberVerticesIso h b 0).symm⟩⟩

/-- Nonempty one-fibres are precisely smaller orientals. -/
theorem oneFiber_oriental {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)
    {m : ℕ} (b : Fin (m + 1) →o Fin 2) (hne : Set.Nonempty {i | b i = 1}) :
    ∃ q : Fin (m + 1), Nonempty (h.object q.val ≅ labelFiber (binaryLabel h b) 1) := by
  obtain ⟨q, ⟨e⟩⟩ := finalSegment_oriental a (binaryLabel_one_final b) hne
  exact ⟨q, ⟨e ≪≫ (labelFiberVerticesIso h b 1).symm⟩⟩

/-- The fibre over an absent vertex label has no cells. -/
theorem labelFiber_empty (h : NormalizedSimplexIdentities) {m : ℕ}
    (b : Fin (m + 1) →o Fin 2) (e : Fin 2) (he : ¬Set.Nonempty {i | b i = e}) :
    IsEmpty (labelFiber (binaryLabel h b) e) := by
  constructor
  intro x
  have hx := (binaryLabel_fullCell_iff h b e x.val).mp x.property
  exact he ⟨objectIndex h false x.val, hx.1⟩

end Thomason.Construction.SimplexComplex

end

end OAI
