import Mathlib
import OAI.CategoryTheory.Thomason.RankedAtoms

namespace OAI

/-! Finite Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory CategoryTheory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

lemma positive_add_zero {p : ℕ} {x y : K.Chain p}
    (hx : x ∈ K.positive p) (hy : y ∈ K.positive p) (h : x+y=0) : x=0 ∧ y=0 := by
  have he (b : A.Index) : A.coefficient b p x = 0 ∧ A.coefficient b p y = 0 := by
    have hh := congrArg (A.coefficient b p) h
    rw [map_add,map_zero] at hh
    have hx' := (A.positive p x).mp hx b
    have hy' := (A.positive p y).mp hy b
    omega
  exact ⟨A.ext p x 0 (fun b => (he b).1.trans (map_zero _).symm),
    A.ext p y 0 (fun b => (he b).2.trans (map_zero _).symm)⟩

lemma comp_dimension_factors {k n : ℕ} (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (hz : truncate n false (comp k x y h) = comp k x y h) :
    truncate n false x = x ∧ truncate n false y = y := by
  have habove (p : ℕ) (hp : max n k < p) (b : Bool) :
      x.row p b = 0 ∧ y.row p b = 0 := by
    have he := row_above_fixed (comp k x y h) hz (by omega : n < p) b
    rw [comp_row] at he
    simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false] at he
    exact A.positive_add_zero (x.positive p b) (y.positive p b) he
  have hx := dimension_of_rows_above_zero x (fun p hp b => (habove p hp b).1)
  have hy := dimension_of_rows_above_zero y (fun p hp b => (habove p hp b).2)
  by_cases hkn : k ≤ n
  · simpa only [max_eq_left hkn] using And.intro hx hy
  · have hnk : n ≤ k := by omega
    rw [max_eq_right hnk] at hx hy
    have hz' : truncate k false (comp k x y h) = comp k x y h :=
      K.nu.source_fixed_upwards hnk hz
    have hz'' : truncate k true (comp k x y h) = comp k x y h :=
      K.nu.target_eq_self_of_source_eq_self hz'
    have hzx : comp k x y h = x := by rw [← hz', source_comp_le k k le_rfl, hx]
    have hzy : comp k x y h = y := by
      rw [← hz'', target_comp_le k k le_rfl]
      exact K.nu.target_eq_self_of_source_eq_self hy
    exact ⟨hzx ▸ hz, hzy ▸ hz⟩

lemma atom_dimension_le {n : ℕ} (b : A.Index)
    (h : truncate n false (A.atom b) = A.atom b) : A.dim b ≤ n := by
  by_contra hn
  have hz := row_above_fixed (A.atom b) h (by omega : n < A.dim b) false
  have ht := A.top b b false
  rw [hz,map_zero] at ht
  simp at ht

inductive BoundedPasting (n : ℕ) : Table K → Prop
  | atom (b : A.Index) : A.dim b ≤ n → BoundedPasting n (A.atom b)
  | compose (k : ℕ) (hk : k < n) (x y)
      (h : truncate k true x = truncate k false y) :
      BoundedPasting n x → BoundedPasting n y → BoundedPasting n (comp k x y h)

lemma bounded_pasting (n : ℕ) (x : Table K) (hx : truncate n false x = x) :
    A.BoundedPasting n x := by
  have hh := A.all_atomic x
  induction hh with
  | atom b => exact .atom b (A.atom_dimension_le b hx)
  | compose k x y h hx' hy' ihx ihy =>
    obtain ⟨hdx,hdy⟩ := A.comp_dimension_factors x y h hx
    by_cases hk : k < n
    · exact .compose k hk x y h (ihx hdx) (ihy hdy)
    · have he : comp k x y h = y := K.nu.comp_of_left_source_fixed k x y h
        (K.nu.source_fixed_upwards (by omega : n ≤ k) hdx)
      rw [he]
      exact ihy hdy

lemma functor_ext {C : OmegaCategory.{w}} (F G : OmegaCategory.Functor K.nu C)
    (h : ∀ b, F.map (A.atom b) = G.map (A.atom b)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext x
  induction A.all_atomic x with
  | atom b => exact h b
  | compose k x y hxy hx hy ihx ihy =>
    change F.map (K.nu.comp k x y hxy) = G.map (K.nu.comp k x y hxy)
    rw [F.map_comp k x y hxy (F.map_composable hxy),
      G.map_comp k x y hxy (G.map_composable hxy)]
    congr 1

lemma surjective_onCells_of_lower_injective {C : OmegaCategory.{w}}
    (F : OmegaCategory.Functor C K.nu) (n : ℕ)
    (hlower : ∀ k, k < n → Function.Injective (F.onCells k))
    (hatom : ∀ b, A.dim b ≤ n → ∃ x : C.Cells n, F.map x.val = A.atom b) :
    Function.Surjective (F.onCells n) := by
  have hlift (t : Table K) (hp : A.BoundedPasting n t) :
      ∃ y : C.Cells n, F.map y.val = t := by
    induction hp with
    | atom b hb => exact hatom b hb
    | compose k hk x y hxy hpx hpy ihx ihy =>
      obtain ⟨a,ha⟩ := ihx
      obtain ⟨b,hb⟩ := ihy
      have hm : C.target k a.val = C.source k b.val := by
        exact congrArg Subtype.val
          (hlower k hk (a₁ := ⟨C.target k a.val,C.source_target_self k a.val⟩)
            (a₂ := ⟨C.source k b.val,C.source_source_self k b.val⟩)
            (Subtype.ext (by change F.map _ = F.map _; rw [F.map_target,F.map_source,ha,hb]; exact hxy)))
      refine ⟨C.gradedComp hk a b hm, ?_⟩
      change F.map (C.comp k a.val b.val hm) = _
      rw [F.map_comp k a.val b.val hm (F.map_composable hm)]
      change K.nu.comp k (F.map a.val) (F.map b.val) _ = K.nu.comp k x y hxy
      congr 1
  intro x
  obtain ⟨y,hy⟩ := hlift x.val (A.bounded_pasting n x.val x.property)
  exact ⟨y,Subtype.ext hy⟩

lemma epi_of_atoms_in_range {C : OmegaCategory.{u}}
    (F : C ⟶ K.nu) (hatom : ∀ b, ∃ x : C.Cell, F.map x = A.atom b) : Epi F where
  left_cancellation G H he := by
    apply A.functor_ext G H
    intro b
    obtain ⟨x,hx⟩ := hatom b
    have h := congrArg (fun f : C ⟶ _ => f.map x) he
    change G.map (F.map x) = H.map (F.map x) at h
    rw [hx] at h
    exact h

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{w}}

def transport (A : RankedAtoms.{u,v} K) (f : Hom K L) (g : Hom L K)
    (hfg : Hom.comp f g = Hom.id K) (hgf : Hom.comp g f = Hom.id L) :
    RankedAtoms.{w,v} L where
  Index := A.Index
  finite := A.finite
  dim := A.dim
  rank := A.rank
  atom b := f.table (A.atom b)
  bounded b := by rw [← Hom.table_truncate,A.bounded]
  coefficient b p := (A.coefficient b p).comp (g.map p)
  homogeneous b p x := A.homogeneous b p (g.map p x)
  ext p x y he := by
    have hh : g.map p x = g.map p y := A.ext p _ _ he
    have hi (z : L.Chain p) : f.map p (g.map p z) = z :=
      congrArg (fun h : Hom L L => h.map p z) hgf
    exact (hi x).symm.trans ((congrArg (f.map p) hh).trans (hi y))
  positive p x := by
    constructor
    · intro hx
      exact (A.positive p _).mp (g.map_positive p x hx)
    · intro hx
      have hh := f.map_positive p _ ((A.positive p _).mpr hx)
      change f.map p (g.map p x) ∈ _ at hh
      have hi : f.map p (g.map p x) = x := congrArg (fun h : Hom L L => h.map p x) hgf
      rwa [hi] at hh
  top b c e := by
    change A.coefficient c (A.dim b) (g.map _ (f.map _ ((A.atom b).row (A.dim b) e))) = _
    have hi (z : K.Chain (A.dim b)) : g.map _ (f.map _ z) = z :=
      congrArg (fun h : Hom K K => h.map (A.dim b) z) hfg
    rw [hi,A.top]
  ranked b p hp e c hc := by
    change A.coefficient c p (g.map _ (f.map _ ((A.atom b).row p e))) ≠ 0 at hc
    have hi (z : K.Chain p) : g.map _ (f.map _ z) = z :=
      congrArg (fun h : Hom K K => h.map p z) hfg
    rw [hi] at hc
    exact A.ranked b p hp e c hc

end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex

lemma complexMap_orderIso_inverse {P : Type u} {Q : Type v}
    [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) :
    Hom.comp (complexMap (e : P →o Q)) (complexMap (e.symm : Q →o P)) = Hom.id (complex P) := by
  rw [← complexMap_comp]
  have he : (e.symm : Q →o P).comp (e : P →o Q) = OrderHom.id := by
    ext x; exact e.symm_apply_apply x
  rw [he,complexMap_id]

namespace Prism.Basis

def ofOrderIso {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) :
    RankedAtoms (complex P).cylinder :=
  (rankedAtoms N).transport (complexMap (e : Fin (N+1) →o P)).cylinder
    (complexMap (e.symm : P →o Fin (N+1))).cylinder
    (by rw [← Hom.cylinder_comp,complexMap_orderIso_inverse,Hom.cylinder_id])
    (by rw [← Hom.cylinder_comp, ← Hom.cylinder_id];
        congr 1; exact complexMap_orderIso_inverse e.symm)

end Prism.Basis
end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

variable {N : ℕ} {P : Type u} [LinearOrder P]

lemma chainComparison_atom_lift (e : Fin (N+1) ≃o P)
    (b : (Prism.Basis.ofOrderIso e).Index) :
    ∃ x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cells
      ((Prism.Basis.ofOrderIso e).dim b),
      (chainComparison (NormalizedChains.complex P)).map x.val = (Prism.Basis.ofOrderIso e).atom b := by
  let M := NormalizedChains.complex P
  let f := complexMap (e : Fin (N+1) →o P)
  change ∃ x : (tensorFunctor.obj M.nu).Cells (Prism.Basis.dim b),
    (chainComparison M).map x.val = f.cylinder.table (Prism.Basis.atom b)
  cases b with
  | endpoint a w =>
    let x := f.table w.atom
    have hx : M.nu.source w.dim x = x := by
      change truncate w.dim false (f.table w.atom) = f.table w.atom
      rw [← Hom.table_truncate,w.atom_dim]
    refine ⟨⟨((tensorEndpoint a).app M.nu).map x, ?_⟩, ?_⟩
    · change (tensorFunctor.obj M.nu).source w.dim _ = _
      erw [endpoint_source,hx]
    · rw [chainComparison_endpoint_apply]
      exact (congrArg (fun h : Hom (NormalizedChains.complex (Fin (N+1))) M.cylinder =>
        h.table w.atom) (f.cylinder_endpoint a)).symm
  | vertical w =>
    let x := f.table w.atom
    have hx : M.nu.source w.dim x = x := by
      change truncate w.dim false (f.table w.atom) = f.table w.atom
      rw [← Hom.table_truncate,w.atom_dim]
    refine ⟨⟨verticalCell w.dim ⟨x,hx⟩, verticalCell_bounded _ _⟩, ?_⟩
    erw [chainComparison_verticalCell w.dim ⟨x,hx⟩]
    exact (verticalTable_natural f w.atom).symm

lemma chainComparison_finiteSimplex_epi (P : Type u) [LinearOrder P] [Finite P] :
    Epi (chainComparison (NormalizedChains.complex P)) := by
  let := Fintype.ofFinite P
  by_cases he : Fintype.card P = 0
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp he
    infer_instance
  · have hp : Fintype.card P = (Fintype.card P - 1) + 1 := by omega
    let e := Fintype.orderIsoFinOfCardEq P hp
    apply (Prism.Basis.ofOrderIso e).epi_of_atoms_in_range
    intro b
    obtain ⟨x,hx⟩ := chainComparison_atom_lift e b
    exact ⟨x.val,hx⟩

lemma chainComparison_finiteSimplex_three_surjective (P : Type u) [LinearOrder P] [Finite P] :
    Function.Surjective ((chainComparison (NormalizedChains.complex P)).onCells 3) := by
  let := Fintype.ofFinite P
  by_cases he : Fintype.card P = 0
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp he
    intro t
    exact isEmptyElim (PosetTables.tableStart
      ((NormalizedChains.complex P).cylinderProjection.table t.val))
  · have hp : Fintype.card P = (Fintype.card P - 1) + 1 := by omega
    let e := Fintype.orderIsoFinOfCardEq P hp
    apply (Prism.Basis.ofOrderIso e).surjective_onCells_of_lower_injective
    · intro k hk x y hxy
      apply Subtype.ext
      exact chainComparison_twocells_injective x.val y.val
        ((tensorFunctor.obj (NormalizedChains.complex P).nu).source_fixed_upwards (by omega : k ≤ 2) x.property)
        ((tensorFunctor.obj (NormalizedChains.complex P).nu).source_fixed_upwards (by omega : k ≤ 2) y.property)
        (congrArg Subtype.val hxy)
    · intro b hb
      obtain ⟨x,hx⟩ := chainComparison_atom_lift e b
      exact ⟨⟨x.val, (tensorFunctor.obj (NormalizedChains.complex P).nu).source_fixed_upwards hb x.property⟩,hx⟩
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Functor
open CategoryTheory
variable {C D E : OmegaCategory.{u}} (F : C ⟶ D) {n : ℕ}

def liftNCell (hn : Function.Bijective (F.onCells n)) (x : D.Cell) : C.Cells n :=
  (Equiv.ofBijective (F.onCells n) hn).symm ⟨D.source n x, D.source_source_self n x⟩

lemma map_liftNCell (hn : Function.Bijective (F.onCells n)) (x : D.Cell) :
    F.map (F.liftNCell hn x).val = D.source n x :=
  congrArg Subtype.val ((Equiv.ofBijective (F.onCells n) hn).apply_symm_apply
    ⟨D.source n x, D.source_source_self n x⟩)

lemma liftNCell_unique (hn : Function.Bijective (F.onCells n)) (x : D.Cell)
    (y : C.Cell) (hy : C.source n y = y) (he : F.map y = D.source n x) :
    (F.liftNCell hn x).val = y := by
  exact congrArg Subtype.val (hn.1 (a₁ := F.liftNCell hn x) (a₂ := ⟨y,hy⟩)
    (Subtype.ext ((F.map_liftNCell hn x).trans he.symm)))

lemma liftNCell_source (hn : Function.Bijective (F.onCells n)) (k : ℕ) (x : D.Cell) :
    (F.liftNCell hn (D.source k x)).val = C.source k (F.liftNCell hn x).val := by
  apply F.liftNCell_unique hn
  · rw [C.source_source, min_comm, ← C.source_source, (F.liftNCell hn x).property]
  · rw [F.map_source,F.map_liftNCell,D.source_source,D.source_source,min_comm]

lemma liftNCell_target_lt (hn : Function.Bijective (F.onCells n)) (k : ℕ) (hk : k < n)
    (x : D.Cell) :
    (F.liftNCell hn (D.target k x)).val = C.target k (F.liftNCell hn x).val := by
  apply F.liftNCell_unique hn
  · exact C.source_fixed_upwards (by omega : k ≤ n) (C.source_target_self k _)
  · rw [F.map_target,F.map_liftNCell,D.target_source,ite_eq_left hk,D.source_target,ite_eq_right (by omega : ¬n < k)]

lemma map_liftNCell_map (hn : Function.Bijective (F.onCells n)) (G : C ⟶ E)
    (hE : E.IsTruncated n) (x : C.Cell) : G.map (F.liftNCell hn (F.map x)).val = G.map x := by
  rw [F.liftNCell_unique hn (F.map x) (C.source n x)
    (C.source_source_self _ _) (F.map_source _ _), G.map_source,hE]

lemma map_liftNCell_faces (hn : Function.Bijective (F.onCells n))
    (hs : Function.Surjective (F.onCells (n+1))) (G : C ⟶ E) (hE : E.IsTruncated n)
    (x : D.Cell) :
    G.map (F.liftNCell hn (D.target n x)).val = G.map (F.liftNCell hn x).val := by
  obtain ⟨z,hz⟩ := hs ⟨D.source (n+1) x,D.source_source_self _ _⟩
  have he : F.map z.val = D.source (n+1) x := congrArg Subtype.val hz
  have hsource : (F.liftNCell hn x).val = C.source n z.val := by
    apply F.liftNCell_unique hn
    · exact C.source_source_self _ _
    · rw [F.map_source, he, D.source_source, min_eq_left (by omega : n ≤ n+1)]
  have htarget : (F.liftNCell hn (D.target n x)).val = C.target n z.val := by
    apply F.liftNCell_unique hn
    · exact C.source_target_self _ _
    · rw [F.map_target,he,D.target_source,ite_eq_left (by omega : n < n+1),D.source_target_self]
  rw [hsource,htarget,G.map_source,G.map_target,hE]
  exact E.target_eq_self_of_source_eq_self (hE _)

def descendTruncated (hn : Function.Bijective (F.onCells n))
    (hs : Function.Surjective (F.onCells (n+1))) (G : C ⟶ E) (hE : E.IsTruncated n) : D ⟶ E where
  map x := G.map (F.liftNCell hn x).val
  map_source k x := by rw [F.liftNCell_source,G.map_source]
  map_target k x := by
    by_cases hk : k < n
    · rw [F.liftNCell_target_lt hn k hk,G.map_target]
    · have hnk : n ≤ k := by omega
      rw [E.target_eq_self_of_source_eq_self (E.source_fixed_upwards hnk (hE _))]
      by_cases he : n = k
      · subst k
        exact F.map_liftNCell_faces hn hs G hE x
      · congr 1
        apply F.liftNCell_unique hn
        · exact (F.liftNCell hn x).property
        · rw [F.map_liftNCell,D.source_target,ite_eq_left (by omega : n < k)]
  map_comp k x y h h' := by
    by_cases hk : k < n
    · have hm : C.target k (F.liftNCell hn x).val = C.source k (F.liftNCell hn y).val := by
        refine congrArg (fun z : C.Cells n => z.val)
          (hn.1 (a₁ := ⟨_,C.source_fixed_upwards (by omega : k ≤ n) (C.source_target_self k _)⟩)
            (a₂ := ⟨_,C.source_fixed_upwards (by omega : k ≤ n) (C.source_source_self k _)⟩)
            (Subtype.ext ?_))
        change F.map (C.target k _) = F.map (C.source k _)
        rw [F.map_target,F.map_source,F.map_liftNCell,F.map_liftNCell,
          D.target_source,ite_eq_left hk,D.source_source,min_eq_left (Nat.le_of_lt hk)]
        exact h
      have hb : C.source n (C.comp k (F.liftNCell hn x).val (F.liftNCell hn y).val hm) =
          C.comp k (F.liftNCell hn x).val (F.liftNCell hn y).val hm := by
        rw [C.source_comp_gt n k hk _ _ hm (C.source_composable hk hm)]
        congr 1 <;> exact (F.liftNCell hn _).property
      have he : (F.liftNCell hn (D.comp k x y h)).val =
          C.comp k (F.liftNCell hn x).val (F.liftNCell hn y).val hm := by
        apply F.liftNCell_unique hn _ _ hb
        rw [F.map_comp k _ _ hm (F.map_composable hm), D.source_comp_gt n k hk _ _ h (D.source_composable hk h)]
        congr 1 <;> exact F.map_liftNCell hn _
      rw [he,G.map_comp]
    · have hnk : n ≤ k := by omega
      rw [E.comp_of_right_source_fixed k _ _ h'
        (E.source_fixed_upwards hnk (hE _))]
      congr 1
      apply F.liftNCell_unique hn
      · exact (F.liftNCell hn x).property
      · rw [F.map_liftNCell,D.source_comp_le n k hnk]

lemma descendTruncated_fac (hn : Function.Bijective (F.onCells n))
    (hs : Function.Surjective (F.onCells (n+1))) (G : C ⟶ E) (hE : E.IsTruncated n) :
    F ≫ F.descendTruncated hn hs G hE = G := by
  apply Functor.ext
  funext x
  exact F.map_liftNCell_map hn G hE x

lemma precomp_injective_of_cells_surjective (hn : Function.Surjective (F.onCells n))
    (hE : E.IsTruncated n) : Function.Injective (fun G : D ⟶ E => F ≫ G) := by
  intro G H he
  apply Functor.ext
  funext x
  obtain ⟨y,hy⟩ := hn ⟨D.source n x,D.source_source_self _ _⟩
  have he' := congrArg (fun I : C ⟶ E => I.map y.val) he
  change G.map (F.map y.val) = H.map (F.map y.val) at he'
  have hy' : F.map y.val = D.source n x := congrArg Subtype.val hy
  rw [hy',G.map_source,H.map_source,hE,hE] at he'
  exact he'

theorem precomp_bijective_truncated (hn : Function.Bijective (F.onCells n))
    (hs : Function.Surjective (F.onCells (n+1))) (hE : E.IsTruncated n) :
    Function.Bijective (fun G : D ⟶ E => F ≫ G) :=
  ⟨F.precomp_injective_of_cells_surjective hn.2 hE,
    fun G => ⟨F.descendTruncated hn hs G hE,F.descendTruncated_fac hn hs G hE⟩⟩

end Thomason.OmegaCategory.Functor

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits

structure RightIntervalCore where
  tensor : OmegaCategory.{u} ⥤ OmegaCategory.{u}
  endpoint : Bool → ((𝟭 OmegaCategory.{u}) ⟶ tensor)
  projection : tensor ⟶ (𝟭 OmegaCategory.{u})
  endpoint_projection : ∀ b, endpoint b ≫ projection = 𝟙 (𝟭 OmegaCategory.{u})
  cocontinuous : PreservesColimitsOfSize.{u,u} tensor
  rightAdjoint : tensor.IsLeftAdjoint
  simplex : ∀ (P : Type u) [LinearOrder P] [Finite P],
    tensor.obj (NormalizedChains.complex P).nu ⟶
      (NormalizedChains.complex P).cylinder.nu
  simplex_natural : ∀ (P Q : Type u) [LinearOrder P] [Finite P]
      [LinearOrder Q] [Finite Q]
      (a : DirectedComplex.Hom (NormalizedChains.complex P) (NormalizedChains.complex Q)),
    tensor.map a.nu ≫ simplex Q = simplex P ≫ a.cylinder.nu
  simplex_endpoint : ∀ (P : Type u) [LinearOrder P] [Finite P] (b : Bool),
    (endpoint b).app (NormalizedChains.complex P).nu ≫ simplex P =
      ((NormalizedChains.complex P).cylinderEndpoint b).nu
  simplex_projection : ∀ (P : Type u) [LinearOrder P] [Finite P],
    simplex P ≫ (NormalizedChains.complex P).cylinderProjection.nu =
      projection.app (NormalizedChains.complex P).nu
  globe : ∀ n : ℕ, tensor.obj (GlobeComplex.complex.{u} n).nu ≅
    (GlobeComplex.complex.{u} n).cylinder.nu
  globe_natural : ∀ (n m : ℕ)
      (a : DirectedComplex.Hom (GlobeComplex.complex.{u} n) (GlobeComplex.complex.{u} m)),
    tensor.map a.nu ≫ (globe m).hom = (globe n).hom ≫ a.cylinder.nu
  globe_endpoint : ∀ (n : ℕ) (b : Bool),
    (endpoint b).app (GlobeComplex.complex.{u} n).nu ≫ (globe n).hom =
      ((GlobeComplex.complex.{u} n).cylinderEndpoint b).nu
  globe_projection : ∀ n : ℕ,
    (globe n).hom ≫ (GlobeComplex.complex.{u} n).cylinderProjection.nu =
      projection.app (GlobeComplex.complex.{u} n).nu

namespace GrayRecursive.IntervalHom

def intervalCore : RightIntervalCore.{u} where
  tensor := tensorFunctor
  endpoint := tensorEndpoint
  projection := tensorProjection
  endpoint_projection := tensorEndpoint_projection
  cocontinuous := tensorFunctor_preservesColimits
  rightAdjoint := tensorFunctor_isLeftAdjoint
  simplex P _ _ := chainComparison (NormalizedChains.complex P)
  simplex_natural _ _ _ _ _ _ a := chainComparison_natural a
  simplex_endpoint P _ _ b := chainComparison_endpoint (NormalizedChains.complex P) b
  simplex_projection P _ _ := chainComparison_projection (NormalizedChains.complex P)
  globe := globeTensorIso
  globe_natural := globeTensorIso_natural
  globe_endpoint := globeTensorIso_endpoint
  globe_projection := globeTensorIso_projection

lemma chainComparison_precomp_bijective_two (P : Type u) [LinearOrder P] [Finite P]
    (Y : OmegaCategory.{u}) (hY : Y.IsTruncated 2) :
    Function.Bijective (fun G : (NormalizedChains.complex P).cylinder.nu ⟶ Y =>
      chainComparison (NormalizedChains.complex P) ≫ G) :=
  (chainComparison (NormalizedChains.complex P)).precomp_bijective_truncated
    (chainComparison_poset_twocells_bijective P)
    (chainComparison_finiteSimplex_three_surjective P) hY

end GrayRecursive.IntervalHom
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalCore
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma internalHom_truncated (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    {Y : OmegaCategory.{u}} {k : ℕ} (hk : Y.IsTruncated k) :
    (R.obj Y).IsTruncated k := by
  intro x
  obtain ⟨i,hi⟩ := (R.obj Y).finite_dimension x
  let F : (complex i).nu ⟶ R.obj Y := lift x hi
  let P : T.tensor.obj (complex i).nu ⟶ Y := (adj.homEquiv _ _).symm F
  let G : (complex i).cylinder.nu ⟶ Y := (T.globe i).inv ≫ P
  let q := sourceCollapse.{u} i k
  have hG : q.cylinder.nu ≫ G = G :=
    GrayRecursive.sourceCollapse_cylinder_truncated hk G
  have he : P = (T.globe i).hom ≫ G := by
    dsimp [G]
    simp
  have hP : T.tensor.map q.nu ≫ P = P := by
    calc
      T.tensor.map q.nu ≫ P = T.tensor.map q.nu ≫ (T.globe i).hom ≫ G := by rw [← he]
      _ = (T.globe i).hom ≫ q.cylinder.nu ≫ G := by
        rw [← Category.assoc, T.globe_natural, Category.assoc]
      _ = (T.globe i).hom ≫ G := by rw [hG]
      _ = P := he.symm
  have hF : q.nu ≫ F = F := by
    calc
      q.nu ≫ F = q.nu ≫ (adj.homEquiv _ _) P := by rw [Equiv.apply_symm_apply]
      _ = (adj.homEquiv _ _) (T.tensor.map q.nu ≫ P) :=
        (adj.homEquiv_naturality_left q.nu P).symm
      _ = (adj.homEquiv _ _) P := by rw [hP]
      _ = F := Equiv.apply_symm_apply _ _
  have hh := congrArg (fun f : (complex i).nu ⟶ R.obj Y => f.map (topTable i)) hF
  change F.map (q.nu.map (topTable i)) = F.map (topTable i) at hh
  rw [sourceCollapse_top] at hh
  change F.map ((complex i).nu.source k (topTable i)) = F.map (topTable i) at hh
  erw [F.map_source] at hh
  simpa only [F, lift_top] using hh

def truncatedCylinderEquiv (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k) :
    (T.tensor.obj (truncation k X).val ⟶ Y) ≃ (T.tensor.obj X ⟶ Y) :=
  ((adj.homEquiv (truncation k X).val Y).trans
    (truncationHomEquiv k X ⟨R.obj Y, T.internalHom_truncated R adj hk⟩)).trans
      (adj.homEquiv X Y).symm

lemma truncatedCylinderEquiv_apply (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k)
    (P : T.tensor.obj (truncation k X).val ⟶ Y) :
    T.truncatedCylinderEquiv R adj k X Y hk P = T.tensor.map (truncationUnit k X) ≫ P := by
  apply (adj.homEquiv X Y).injective
  change (adj.homEquiv X Y) ((adj.homEquiv X Y).symm
    (truncationUnit k X ≫ (adj.homEquiv (truncation k X).val Y) P)) = _
  erw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left]
  rfl

lemma truncatedCylinderEquiv_endpoint (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k)
    (P : T.tensor.obj (truncation k X).val ⟶ Y) (a : Bool) :
    (T.endpoint a).app X ≫ T.truncatedCylinderEquiv R adj k X Y hk P =
      truncationUnit k X ≫ (T.endpoint a).app (truncation k X).val ≫ P := by
  erw [T.truncatedCylinderEquiv_apply, ← Category.assoc,
    ← (T.endpoint a).naturality, Category.assoc]

end Thomason.RightIntervalCore

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalCore
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalCore.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)

def finiteInternalHom (n : ℕ) : NCategory.{u} n ⥤ NCategory.{u} n where
  obj Y := ⟨R.obj Y.val, T.internalHom_truncated R adj Y.property⟩
  map f := R.map f
  map_id Y := R.map_id Y.val
  map_comp f g := R.map_comp f g

def finiteTranspose (n : ℕ) (X Y : NCategory.{u} n) :
    (T.tensor.obj X.val ⟶ Y.val) ≃ (X ⟶ (T.finiteInternalHom R adj n).obj Y) :=
  adj.homEquiv X.val Y.val

section FiniteDescent
variable {n : ℕ} {A B X Y Z : NCategory.{u} n}
variable {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
variable (sq : IsPushout i a b j)

def finiteGlue (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.obj Y.val ⟶ Z.val :=
  (T.finiteTranspose R adj n Y Z).symm
    (sq.desc ((T.finiteTranspose R adj n B Z) PB) ((T.finiteTranspose R adj n X Z) PX)
      (by
        change OmegaCategory.Functor.comp i ((adj.homEquiv _ _) PB) =
          OmegaCategory.Functor.comp a ((adj.homEquiv _ _) PX)
        exact (adj.homEquiv_naturality_left i PB).symm.trans
          ((congrArg (adj.homEquiv _ _) h).trans (adj.homEquiv_naturality_left a PX))))

lemma finiteGlue_left (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map b ≫ T.finiteGlue R adj sq PB PX h = PB := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left]
  change b ≫ (T.finiteTranspose R adj n Y Z)
    ((T.finiteTranspose R adj n Y Z).symm _) = _
  rw [Equiv.apply_symm_apply, sq.inl_desc]
  rfl

lemma finiteGlue_right (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map j ≫ T.finiteGlue R adj sq PB PX h = PX := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left]
  change j ≫ (T.finiteTranspose R adj n Y Z)
    ((T.finiteTranspose R adj n Y Z).symm _) = _
  rw [Equiv.apply_symm_apply, sq.inr_desc]
  rfl

include R adj sq in
lemma finiteCylinder_hom_ext {P Q : T.tensor.obj Y.val ⟶ Z.val}
    (hb : T.tensor.map b ≫ P = T.tensor.map b ≫ Q)
    (hj : T.tensor.map j ≫ P = T.tensor.map j ≫ Q) : P = Q := by
  apply (T.finiteTranspose R adj n Y Z).injective
  apply sq.hom_ext
  · change OmegaCategory.Functor.comp b ((adj.homEquiv _ _) P) =
      OmegaCategory.Functor.comp b ((adj.homEquiv _ _) Q)
    exact (adj.homEquiv_naturality_left b P).symm.trans
      ((congrArg (adj.homEquiv _ _) hb).trans (adj.homEquiv_naturality_left b Q))
  · change OmegaCategory.Functor.comp j ((adj.homEquiv _ _) P) =
      OmegaCategory.Functor.comp j ((adj.homEquiv _ _) Q)
    exact (adj.homEquiv_naturality_left j P).symm.trans
      ((congrArg (adj.homEquiv _ _) hj).trans (adj.homEquiv_naturality_left j Q))

lemma finiteGlue_endpoint_left
    (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    OmegaCategory.Functor.comp b
        ((T.endpoint ε).app Y.val ≫ T.finiteGlue R adj sq PB PX h) =
      (T.endpoint ε).app B.val ≫ PB := by
  have hb := (T.endpoint ε).naturality b
  exact (congrArg (fun f : B.val ⟶ T.tensor.obj Y.val =>
    f ≫ T.finiteGlue R adj sq PB PX h) hb).trans
    (congrArg (fun f => (T.endpoint ε).app B.val ≫ f)
      (T.finiteGlue_left R adj sq PB PX h))

lemma finiteGlue_endpoint_right
    (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    OmegaCategory.Functor.comp j
        ((T.endpoint ε).app Y.val ≫ T.finiteGlue R adj sq PB PX h) =
      (T.endpoint ε).app X.val ≫ PX := by
  have hj := (T.endpoint ε).naturality j
  exact (congrArg (fun f : X.val ⟶ T.tensor.obj Y.val =>
    f ≫ T.finiteGlue R adj sq PB PX h) hj).trans
    (congrArg (fun f => (T.endpoint ε).app X.val ≫ f)
      (T.finiteGlue_right R adj sq PB PX h))

include R adj sq in

theorem finite_stationary_gluing
    (P : T.tensor.obj B.val ⟶ B.val)
    (F : Bool → (B ⟶ B))
    (he : ∀ ε, (T.endpoint ε).app B.val ≫ P = F ε)
    (hs : T.tensor.map i ≫ P = (T.projection.app A.val) ≫ i) :
    ∃ Q : T.tensor.obj Y.val ⟶ Y.val,
      T.tensor.map b ≫ Q = P ≫ b ∧
      T.tensor.map j ≫ Q = T.projection.app X.val ≫ j ∧
      (∀ ε, OmegaCategory.Functor.comp b ((T.endpoint ε).app Y.val ≫ Q) = F ε ≫ b) ∧
      (∀ ε, OmegaCategory.Functor.comp j ((T.endpoint ε).app Y.val ≫ Q) = j) ∧
      (∀ Q' : T.tensor.obj Y.val ⟶ Y.val,
        T.tensor.map b ≫ Q' = P ≫ b →
        T.tensor.map j ≫ Q' = T.projection.app X.val ≫ j → Q' = Q) := by
  have hc : T.tensor.map i ≫ (P ≫ b) =
      T.tensor.map a ≫ (T.projection.app X.val ≫ j) := by
    calc
      _ = (T.projection.app A.val) ≫ (show A.val ⟶ Y.val from i ≫ b) := by
        rw [← Category.assoc, hs, Category.assoc]
      _ = (T.projection.app A.val) ≫ (show A.val ⟶ Y.val from a ≫ j) :=
        congrArg (fun f : A ⟶ Y => T.projection.app A.val ≫ f) sq.w
      _ = _ := by
        have ha := T.projection.naturality a
        change _ = (T.tensor.map a ≫ T.projection.app X.val) ≫ j
        rw [ha]
        rfl
  let Q := T.finiteGlue R adj sq (P ≫ b) (T.projection.app X.val ≫ j) hc
  refine ⟨Q, T.finiteGlue_left R adj sq _ _ hc,
    T.finiteGlue_right R adj sq _ _ hc, ?_, ?_, ?_⟩
  · intro ε
    rw [T.finiteGlue_endpoint_left, ← Category.assoc, he ε]
    rfl
  · intro ε
    rw [T.finiteGlue_endpoint_right, ← Category.assoc]
    have hε := congrArg (fun α => α.app X.val) (T.endpoint_projection ε)
    change (T.endpoint ε).app X.val ≫ T.projection.app X.val = 𝟙 X.val at hε
    rw [hε]; rfl
  · intro Q' hb hj
    apply T.finiteCylinder_hom_ext R adj sq
    · exact hb.trans (T.finiteGlue_left R adj sq _ _ hc).symm
    · exact hj.trans (T.finiteGlue_right R adj sq _ _ hc).symm

include R adj sq in

lemma finite_stationary_gluing_natural
    {X' Y' : NCategory.{u} n} {j' : X' ⟶ Y'} {b' : B ⟶ Y'}
    (w : X ⟶ X') (v : Y ⟶ Y') (hvB : b ≫ v = b') (hvX : j ≫ v = w ≫ j')
    (P : T.tensor.obj B.val ⟶ B.val)
    (Q : T.tensor.obj Y.val ⟶ Y.val) (Q' : T.tensor.obj Y'.val ⟶ Y'.val)
    (hB : T.tensor.map b ≫ Q = P ≫ b)
    (hX : T.tensor.map j ≫ Q = T.projection.app X.val ≫ j)
    (hB' : T.tensor.map b' ≫ Q' = P ≫ b')
    (hX' : T.tensor.map j' ≫ Q' = T.projection.app X'.val ≫ j') :
    T.tensor.map v ≫ Q' = Q ≫ v := by
  apply T.finiteCylinder_hom_ext R adj sq
  · calc
      _ = T.tensor.map (show B.val ⟶ Y'.val from b ≫ v) ≫ Q' := by
        rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map b' ≫ Q' :=
        congrArg (fun f : B ⟶ Y' => T.tensor.map f ≫ Q') hvB
      _ = P ≫ b' := hB'
      _ = (P ≫ b) ≫ v :=
        congrArg (fun f : B ⟶ Y' => P ≫ f) hvB.symm
      _ = _ := by rw [← hB, Category.assoc]
  · calc
      _ = T.tensor.map (show X.val ⟶ Y'.val from j ≫ v) ≫ Q' := by
        rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map (show X.val ⟶ Y'.val from w ≫ j') ≫ Q' :=
        congrArg (fun f : X ⟶ Y' => T.tensor.map f ≫ Q') hvX
      _ = T.tensor.map w ≫ (T.tensor.map j' ≫ Q') := by
        rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map w ≫ (T.projection.app X'.val ≫ j') := by rw [hX']
      _ = T.projection.app X.val ≫ (show X.val ⟶ Y'.val from w ≫ j') := by
        rw [← Category.assoc, T.projection.naturality w]; rfl
      _ = (T.projection.app X.val ≫ j) ≫ v :=
        congrArg (fun f : X ⟶ Y' => T.projection.app X.val ≫ f) hvX.symm
      _ = _ := by rw [← hX, Category.assoc]

end FiniteDescent
end Thomason.RightIntervalCore

end

end OAI
