import Mathlib
import OAI.CategoryTheory.Thomason.RecursiveCylinders

namespace OAI

/-! Globular Generation. -/

noncomputable section
universe u v w z
open CategoryTheory

namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def corner (n : ℕ) (b : Bool) : Table (K.{u} (n+1)) where
  row
    | 0, _ => diagonalRow n b
    | _+1, _ => 0
  positive p e := by
    cases p with
    | zero =>
      cases b
      · exact ⟨basis_positive _ _ _ (Or.inl (by omega)), (complex (n+1)).positive 0 |>.zero_mem⟩
      · exact ⟨(complex (n+1)).positive 0 |>.zero_mem, basis_positive _ _ _ (Or.inl (by omega))⟩
    | succ p => exact (K (n+1)).positive (p+1) |>.zero_mem
  boundary p e := by cases p <;> simp
  augmentation e := by
    change mass (n+1) 0 (diagonalRow n b).1 + mass (n+1) 0 (diagonalRow n b).2 = 1
    cases b <;> simp [diagonalRow, mass, basis] <;> rfl
  bounded := ⟨0, by
    rintro (_ | p) hp e
    · omega
    · rfl⟩

lemma diagonal_iff_boundaries {n : ℕ} (t : Table (K.{u} (n+1))) :
    IsDiagonal t ↔ truncate 0 false t = corner n false ∧ truncate 0 true t = corner n true := by
  constructor
  · intro ht
    change ∀ b, t.row 0 b = diagonalRow n b at ht
    constructor <;> ext p b <;> cases p <;> simp [truncate_row, corner, ht]
  · intro ht b
    cases b with
    | false => exact congrArg (fun t : Table (K (n+1)) => t.row 0 false) ht.1
    | true => exact congrArg (fun t : Table (K (n+1)) => t.row 0 false) ht.2

lemma truncate_diagonal {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (k : ℕ) (e : Bool) :
    IsDiagonal (truncate (k+1) e t) := by
  intro b
  simpa only [truncate_row, Nat.zero_lt_succ, ite_true] using ht b

lemma comp_diagonal {n : ℕ} (s t : Table (K.{u} (n+1))) (hs : IsDiagonal s) (k : ℕ)
    (h : truncate (k+1) true s = truncate (k+1) false t) :
    IsDiagonal (DirectedComplex.Table.comp (k+1) s t h) := by
  intro b
  simpa only [comp_row, Nat.zero_lt_succ, ite_true] using hs b

lemma down_truncate {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (k : ℕ) (e : Bool) :
    down (truncate (k+1) e t) (truncate_diagonal t ht k e) = truncate k e (down t ht) := by
  ext p b
  simp only [down_row, truncate_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
  split_ifs <;> simp

lemma down_comp {n : ℕ} (s t : Table (K.{u} (n+1))) (hs : IsDiagonal s) (ht : IsDiagonal t) (k : ℕ)
    (h : truncate (k+1) true s = truncate (k+1) false t)
    (h' : truncate k true (down s hs) = truncate k false (down t ht)) :
    down (DirectedComplex.Table.comp (k+1) s t h) (comp_diagonal s t hs k h) =
      DirectedComplex.Table.comp k (down s hs) (down t ht) h' := by
  ext p b
  simp only [down_row, comp_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
  split_ifs <;> simp

abbrev diagonalHom (n : ℕ) : OmegaCategory.{u} :=
  (K (n+1)).nu.homCategory (corner n false) (corner n true)

def downFunctor (n : ℕ) : diagonalHom.{u} n ⟶ (K.{u} n).nu where
  map t := down t.val ((diagonal_iff_boundaries t.val).mpr t.property)
  map_source k t := down_truncate t.val _ k false
  map_target k t := down_truncate t.val _ k true
  map_comp k s t h h' := down_comp s.val t.val _ _ k (congrArg Subtype.val h) h'

lemma downFunctor_bijective (n : ℕ) : Function.Bijective (downFunctor.{u} n).map := by
  constructor
  · intro s t h
    apply Subtype.ext
    exact (up_down s.val ((diagonal_iff_boundaries s.val).mpr s.property)).symm.trans
      ((congrArg up h).trans (up_down t.val ((diagonal_iff_boundaries t.val).mpr t.property)))
  · intro t
    exact ⟨⟨up t, (diagonal_iff_boundaries _).mp (up_diagonal t)⟩, down_up t⟩

def diagonalIso (n : ℕ) : diagonalHom.{u} n ≅ (K.{u} n).nu :=
  OmegaCategory.isoOfBijective (downFunctor n) (downFunctor_bijective n)

lemma diagonalIso_inverse (n : ℕ) (t : Table (K.{u} n)) :
    ((diagonalIso n).inv.map t).val = up t := by
  have h := congrArg (fun F : (K.{u} n).nu ⟶ (K.{u} n).nu => F.map t)
    (diagonalIso n).inv_hom_id
  let x := (diagonalIso n).inv.map t
  have hx : IsDiagonal x.val := (diagonal_iff_boundaries x.val).mpr x.property
  change down x.val hx = t at h
  exact (up_down x.val hx).symm.trans (congrArg up h)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

lemma positive_cycle_zero {n p : ℕ} (x : Chain.{u} n (p+1))
    (hx : x ∈ (complex n).positive (p+1)) (hd : (complex n).d p x = 0) : x = 0 := by
  apply (mass_eq_zero_iff hx).mp
  have h := congrArg (fun y : Chain n p => y.val ⟨false⟩) hd
  erw [complex_d_coordinate] at h
  change -mass n (p+1) x = 0 at h
  simpa using h

lemma positive_add_zero {n p : ℕ} {x y : Chain.{u} n p}
    (hx : x ∈ (complex n).positive p) (hy : y ∈ (complex n).positive p)
    (h : x+y = 0) : x = 0 ∧ y = 0 := by
  have hm := congrArg (mass n p) h
  rw [map_add, map_zero] at hm
  have hx' := mass_nonneg hx
  have hy' := mass_nonneg hy
  exact ⟨(mass_eq_zero_iff hx).mp (by omega), (mass_eq_zero_iff hy).mp (by omega)⟩

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def sideRow {n : ℕ} (t : Table (K.{u} n)) (a : Bool) : (p : ℕ) → Bool → (complex.{u} n).Chain p
  | 0, b => if a then (t.row 0 b).2 else (t.row 0 b).1
  | p+1, b => if a then (t.row (p+1) b).2.1 else (t.row (p+1) b).1

def crossRow {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) : (complex.{u} n).Chain p :=
  (t.row (p+1) b).2.2

def project {n : ℕ} (t : Table (K.{u} n)) : Table (complex.{u} n) :=
  (complex n).cylinderProjection.table t

lemma project_row {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (project t).row p b = sideRow t false p b + sideRow t true p b := by cases p <;> rfl

lemma side_positive {n : ℕ} (t : Table (K.{u} n)) (a : Bool) (p : ℕ) (b : Bool) :
    sideRow t a p b ∈ (complex n).positive p := by
  cases p with
  | zero => cases a; exact (t.positive 0 b).1; exact (t.positive 0 b).2
  | succ p => cases a; exact (t.positive (p+1) b).1; exact (t.positive (p+1) b).2.1

lemma cross_positive {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    crossRow t p b ∈ (complex n).positive p := (t.positive (p+1) b).2.2

lemma cross_boundary {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (complex n).d p (crossRow t (p+1) b) = crossRow t p true - crossRow t p false :=
  congrArg (fun x : (K n).Chain (p+1) => x.2.2) (t.boundary (p+1) b)

lemma left_boundary {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (complex n).d p (sideRow t false (p+1) b) - (-1 : ℤ)^p • crossRow t p b =
      sideRow t false p true - sideRow t false p false := by
  cases p with
  | zero => simpa [sideRow, crossRow, cylinderDifferential] using congrArg Prod.fst (t.boundary 0 b)
  | succ p => exact congrArg Prod.fst (t.boundary (p+1) b)

lemma right_boundary {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (complex n).d p (sideRow t true (p+1) b) + (-1 : ℤ)^p • crossRow t p b =
      sideRow t true p true - sideRow t true p false := by
  cases p with
  | zero => simpa [sideRow, crossRow, cylinderDifferential] using congrArg Prod.snd (t.boundary 0 b)
  | succ p => exact congrArg (fun x : (K n).Chain (p+1) => x.2.1) (t.boundary (p+1) b)

lemma side_augmentation {n : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    mass n 0 (sideRow t false 0 b) + mass n 0 (sideRow t true 0 b) = 1 := t.augmentation b

lemma side_mass_vertex {n : ℕ} (t : Table (K.{u} n)) (a b : Bool) :
    mass n 0 (sideRow t a 0 b) = 0 ∨ mass n 0 (sideRow t a 0 b) = 1 := by
  have h := side_augmentation t b
  have h₀ := mass_nonneg (side_positive t false 0 b)
  have h₁ := mass_nonneg (side_positive t true 0 b)
  cases a <;> omega

lemma cross_mass_vertex {n : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    mass n 0 (crossRow t 0 b) =
      mass n 0 (sideRow t true 0 true) - mass n 0 (sideRow t true 0 false) := by
  have h := congrArg (mass n 0) (right_boundary t 0 b)
  simp only [pow_zero, one_smul] at h
  erw [map_add, map_sub, mass_d] at h
  simpa using h

lemma interval_monotone {n : ℕ} (t : Table (K.{u} n)) :
    mass n 0 (sideRow t true 0 false) ≤ mass n 0 (sideRow t true 0 true) := by
  have h := mass_nonneg (cross_positive t 0 false)
  rw [cross_mass_vertex] at h
  omega

lemma cross_succ_eq_zero_of_constant {n : ℕ} (t : Table (K.{u} n))
    (h : crossRow t 0 true = crossRow t 0 false) (p : ℕ) (b : Bool) :
    crossRow t (p+1) b = 0 := by
  induction p generalizing b with
  | zero => exact positive_cycle_zero _ (cross_positive t 1 b) (by rw [cross_boundary, h, sub_self])
  | succ p ih =>
    exact positive_cycle_zero _ (cross_positive t (p+2) b)
      (by rw [cross_boundary, ih true, ih false, sub_self])

lemma no_cross_of_stationary_interval {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) = mass n 0 (sideRow t true 0 false)) :
    ∀ p b, crossRow t p b = 0 := by
  have h₀ : ∀ b, crossRow t 0 b = 0 := fun b =>
    (mass_eq_zero_iff (cross_positive t 0 b)).mp (by rw [cross_mass_vertex, h, sub_self])
  intro p b
  cases p with
  | zero => exact h₀ b
  | succ p => exact cross_succ_eq_zero_of_constant t (by rw [h₀ true, h₀ false]) p b

lemma no_side_of_empty_vertex {n : ℕ} (t : Table (K.{u} n)) (a : Bool)
    (h : ∀ p b, crossRow t p b = 0) (h₀ : ∀ b, sideRow t a 0 b = 0) :
    ∀ p b, sideRow t a p b = 0 := by
  intro p b
  induction p generalizing b with
  | zero => exact h₀ b
  | succ p ih =>
    apply positive_cycle_zero _ (side_positive t a (p+1) b)
    cases a with
    | false => simpa only [h, smul_zero, ih, sub_zero, sub_self] using left_boundary t p b
    | true => simpa only [h, smul_zero, ih, add_zero, sub_self] using right_boundary t p b

lemma endpoint_of_stationary_interval {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) = mass n 0 (sideRow t true 0 false)) :
    ∃ a, t = ((complex n).cylinderEndpoint a).table (project t) := by
  have hc := no_cross_of_stationary_interval t h
  rcases side_mass_vertex t true false with h₀ | h₁
  · have hs : ∀ p b, sideRow t true p b = 0 := by
      apply no_side_of_empty_vertex t true hc
      intro b
      apply (mass_eq_zero_iff (side_positive t true 0 b)).mp
      cases b
      · exact h₀
      · exact h.trans h₀
    refine ⟨false, ?_⟩
    ext p b
    change t.row p b = (complex n).cylinderEndpointMap false p ((project t).row p b)
    rw [project_row, hs p b, add_zero]
    cases p with
    | zero => exact Prod.ext rfl (hs 0 b)
    | succ p => exact Prod.ext rfl (Prod.ext (hs (p+1) b) (hc p b))
  · have hs : ∀ p b, sideRow t false p b = 0 := by
      apply no_side_of_empty_vertex t false hc
      intro b
      apply (mass_eq_zero_iff (side_positive t false 0 b)).mp
      have hh := side_augmentation t b
      cases b <;> omega
    refine ⟨true, ?_⟩
    ext p b
    change t.row p b = (complex n).cylinderEndpointMap true p ((project t).row p b)
    rw [project_row, hs p b, zero_add]
    cases p with
    | zero => exact Prod.ext (hs 0 b) rfl
    | succ p => exact Prod.ext (hs (p+1) b) (Prod.ext rfl (hc p b))

lemma crossing_sides {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) ≠ mass n 0 (sideRow t true 0 false)) :
    sideRow t true 0 false = 0 ∧ sideRow t false 0 true = 0 := by
  have hs := side_mass_vertex t true false
  have ht := side_mass_vertex t true true
  have hm := interval_monotone t
  have ha := side_augmentation t true
  constructor
  · apply (mass_eq_zero_iff (side_positive t true 0 false)).mp
    omega
  · apply (mass_eq_zero_iff (side_positive t false 0 true)).mp
    omega

lemma crossing_vertices {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) ≠ mass n 0 (sideRow t true 0 false)) :
    (∀ b, sideRow t b 0 b = (project t).row 0 b) := by
  obtain ⟨hs, ht⟩ := crossing_sides t h
  intro b
  rw [project_row]
  cases b
  · rw [hs, add_zero]
  · rw [ht, zero_add]

lemma crossing_diagonal {n : ℕ} (t : Table (K.{u} (n+1)))
    (h : mass (n+1) 0 (sideRow t true 0 true) ≠ mass (n+1) 0 (sideRow t true 0 false))
    {p : ℕ} (hp : 0 < p) (e : Bool)
    (hpj : project t = truncate p e (topTable (n+1))) : IsDiagonal t := by
  have hv := crossing_vertices t h
  obtain ⟨hs, ht⟩ := crossing_sides t h
  intro b
  have hb := hv b
  rw [hpj, truncate_row, ite_eq_left hp] at hb
  change sideRow t b 0 b = topRow (n+1) 0 b at hb
  rw [topRow_lt _ _ _ (by omega)] at hb
  cases b
  · exact Prod.ext hb hs
  · exact Prod.ext ht hb

lemma crossing_vertical {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) ≠ mass n 0 (sideRow t true 0 false))
    (hpj : truncate 0 false (project t) = project t) : t = verticalTable (project t) := by
  have hz : ∀ p b, (project t).row (p+1) b = 0 := by
    intro p b
    rw [← hpj, truncate_row]
    simp
  have hs : ∀ p b, sideRow t false (p+1) b = 0 ∧ sideRow t true (p+1) b = 0 := by
    intro p b
    exact positive_add_zero (side_positive t false (p+1) b) (side_positive t true (p+1) b)
      (by erw [← project_row, hz]; rfl)
  have he : ∀ b, (project t).row 0 b = (project t).row 0 true := by
    intro b
    have h₀ := congrArg (fun x : Table (complex n) => x.row 0 b) hpj
    have h₁ := congrArg (fun x : Table (complex n) => x.row 0 true) hpj
    exact h₀.symm.trans h₁
  have hv := crossing_vertices t h
  obtain ⟨hb, ht⟩ := crossing_sides t h
  have hc₀ : ∀ b, crossRow t 0 b = (project t).row 0 true := by
    intro b
    have hh := right_boundary t 0 b
    rw [(hs 0 b).2, map_zero, zero_add, pow_zero, one_smul, hb, sub_zero, hv true] at hh
    exact hh
  have hc : ∀ p b, crossRow t (p+1) b = 0 :=
    cross_succ_eq_zero_of_constant t (by rw [hc₀, hc₀])
  ext p b
  cases p with
  | zero =>
    change t.row 0 b = verticalRow (project t) 0 b
    cases b
    · exact Prod.ext (hv false) hb
    · exact Prod.ext ht (hv true)
  | succ p =>
    cases p with
    | zero =>
      change t.row 1 b = verticalRow (project t) 1 b
      simp only [verticalRow, show ¬Even (1 : ℕ) by decide, ite_false, hz]
      cases b <;> exact Prod.ext (hs 0 _).1 (Prod.ext (hs 0 _).2 ((hc₀ _).trans (he _).symm))
    | succ p =>
      change t.row (p+2) b = verticalRow (project t) (p+2) b
      simp only [verticalRow, hz]
      split_ifs <;> cases b <;> exact Prod.ext (hs (p+1) _).1 (Prod.ext (hs (p+1) _).2 (hc p _))

lemma table_cases {n : ℕ} (t : Table (K.{u} (n+1))) :
    (∃ a, t = ((complex (n+1)).cylinderEndpoint a).table (project t)) ∨
    (∃ a, t = verticalTable (truncate 0 a (topTable (n+1)))) ∨ IsDiagonal t := by
  by_cases h : mass (n+1) 0 (sideRow t true 0 true) = mass (n+1) 0 (sideRow t true 0 false)
  · exact Or.inl (endpoint_of_stationary_interval t h)
  · obtain ⟨p, a, _, hpj⟩ := table_classification (project t)
    cases p with
    | zero =>
      right; left
      refine ⟨a, ?_⟩
      rw [crossing_vertical t h (by rw [hpj]; simp [truncate_truncate]), hpj]
    | succ p => exact Or.inr (Or.inr (crossing_diagonal t h (by omega) a hpj))

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open DirectedComplex DirectedComplex.Table

def suspendTable {n : ℕ} (x : Table (complex.{u} n)) : Table (complex.{u} (n+1)) where
  row
    | 0, b => basis (n+1) 0 b (Or.inl (by omega))
    | p+1, b => (shiftDown n p).symm (x.row p b)
  positive p b := by
    cases p with
    | zero => exact basis_positive _ _ _ _
    | succ p => exact x.positive p b
  boundary p b := by
    cases p with
    | zero =>
      erw [d_shiftUp_zero, table_mass_zero]
      apply Subtype.ext
      funext ⟨i⟩
      change (if i then (1 : ℤ) else -1) =
        (basis.{u} (n+1) 0 true (Or.inl (by omega))).val ⟨i⟩ -
        (basis.{u} (n+1) 0 false (Or.inl (by omega))).val ⟨i⟩
      cases i <;> simp
    | succ p => erw [shiftUp_d, x.boundary, map_sub]; rfl
  augmentation b := mass_basis _ _ _ _
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k+1, ?_⟩
    rintro (_ | p) hp b
    · omega
    · change (shiftDown n p).symm (x.row p b) = 0
      erw [hk p (by omega) b, map_zero]

@[simp] lemma suspendTable_zero {n : ℕ} (x : Table (complex.{u} n)) (b : Bool) :
    (suspendTable x).row 0 b = basis (n+1) 0 b (Or.inl (by omega)) := rfl

@[simp] lemma suspendTable_succ {n p : ℕ} (x : Table (complex.{u} n)) (b : Bool) :
    (suspendTable x).row (p+1) b = (shiftDown n p).symm (x.row p b) := rfl

lemma suspendTable_truncate {n : ℕ} (x : Table (complex.{u} n)) (k : ℕ) (b : Bool) :
    suspendTable (truncate k b x) = truncate (k+1) b (suspendTable x) := by
  ext p a
  cases p with
  | zero => simp
  | succ p =>
    simp only [suspendTable_succ, truncate_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    erw [apply_ite (shiftDown n p).symm, apply_ite (shiftDown n p).symm, map_zero]
    rfl

lemma suspendTable_top (n : ℕ) : suspendTable (topTable.{u} n) = topTable (n+1) := by
  ext p b
  cases p with
  | zero => exact (topRow_lt (n+1) 0 b (by omega)).symm
  | succ p =>
    change (shiftDown n p).symm (topRow n p b) = topRow (n+1) (p+1) b
    by_cases hp : p < n
    · rw [topRow_lt _ _ _ hp, topRow_lt _ _ _ (by omega)]
      rfl
    · by_cases hn : p = n
      · subst p
        rw [topRow_eq, topRow_eq]
        rfl
      · erw [topRow_gt _ _ _ (by omega), topRow_gt _ _ _ (by omega), map_zero]
        rfl

lemma suspendTable_eq_face {n k : ℕ} (b : Bool) :
    suspendTable (truncate k b (topTable.{u} n)) = truncate (k+1) b (topTable (n+1)) := by
  rw [suspendTable_truncate, suspendTable_top]

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def atEnd {n : ℕ} (a : Bool) (x : Table (complex.{u} n)) : Table (K.{u} n) :=
  ((complex n).cylinderEndpoint a).table x

def vertex (n : ℕ) (a : Bool) : Table (complex.{u} (n+1)) := truncate 0 a (topTable (n+1))

@[simp] lemma vertex_zero (n : ℕ) (a b : Bool) :
    (vertex.{u} n a).row 0 b = basis (n+1) 0 a (Or.inl (by omega)) := by
  simp [vertex, topTable, topRow_lt _ _ _ (show 0 < n+1 by omega)]

@[simp] lemma vertex_succ (n p : ℕ) (a b : Bool) : (vertex.{u} n a).row (p+1) b = 0 := by
  simp [vertex]

@[simp] lemma vertexWeights_one_zero (n : ℕ) :
    vertexWeights.{u} n 1 0 = basis (n+1) 0 false (Or.inl (by omega)) := by
  apply Subtype.ext
  funext ⟨b⟩
  cases b <;> rfl

@[simp] lemma vertexWeights_zero_one (n : ℕ) :
    vertexWeights.{u} n 0 1 = basis (n+1) 0 true (Or.inl (by omega)) := by
  apply Subtype.ext
  funext ⟨b⟩
  cases b <;> rfl

lemma up_truncate {n : ℕ} (t : Table (K.{u} n)) (k : ℕ) (e : Bool) :
    up (truncate k e t) = truncate (k+1) e (up t) := by
  ext p b
  cases p with
  | zero => simp
  | succ p =>
    simp only [up_succ, truncate_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    split_ifs <;> simp

lemma up_composable {n k : ℕ} {s t : Table (K.{u} n)}
    (h : truncate k true s = truncate k false t) :
    truncate (k+1) true (up s) = truncate (k+1) false (up t) := by
  rw [← up_truncate, ← up_truncate, h]

lemma up_comp {n k : ℕ} (s t : Table (K.{u} n))
    (h : truncate k true s = truncate k false t)
    (h' : truncate (k+1) true (up s) = truncate (k+1) false (up t)) :
    up (DirectedComplex.Table.comp k s t h) = DirectedComplex.Table.comp (k+1) (up s) (up t) h' := by
  ext p b
  cases p with
  | zero => simp
  | succ p =>
    simp only [up_succ, comp_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    split_ifs <;> simp

lemma up_endpoint_left_matching {n : ℕ} (x : Table (complex.{u} n)) :
    truncate 0 true (verticalTable (vertex n false)) = truncate 0 false (atEnd true (suspendTable x)) := by
  ext p b
  cases p with
  | zero =>
    simp only [truncate_row, lt_self_iff_false, ite_false, ite_true]
    change (0, (vertex n false).row 0 true) = (0, (suspendTable x).row 0 false)
    simp
  | succ p => simp

lemma up_endpoint_right_matching {n : ℕ} (x : Table (complex.{u} n)) :
    truncate 0 true (atEnd false (suspendTable x)) = truncate 0 false (verticalTable (vertex n true)) := by
  ext p b
  cases p with
  | zero =>
    simp only [truncate_row, lt_self_iff_false, ite_false, ite_true]
    change ((suspendTable x).row 0 true, 0) = ((vertex n true).row 0 false, 0)
    simp
  | succ p => simp

lemma up_endpoint_false {n : ℕ} (x : Table (complex.{u} n)) :
    up (atEnd false x) = DirectedComplex.Table.comp 0 (verticalTable (vertex n false))
      (atEnd true (suspendTable x)) (up_endpoint_left_matching x) := by
  ext p b
  cases p with
  | zero =>
    cases b <;> simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      verticalTable, verticalRow, diagonalRow]
  | succ p =>
    cases p with
    | zero =>
      cases b <;>
        simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
          verticalTable, verticalRow, upRow, table_mass_zero]
      all_goals
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · rfl
        · exact (zero_add _).symm
        · apply Subtype.ext
          funext ⟨index⟩
          cases index <;> rfl
    | succ p =>
      simp only [up_succ, comp_row, Nat.not_lt_zero, ite_false, Nat.succ_ne_zero]
      simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
        verticalTable, verticalRow, upRow]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · rfl
      · exact (zero_add _).symm
      · rfl

lemma up_endpoint_true {n : ℕ} (x : Table (complex.{u} n)) :
    up (atEnd true x) = DirectedComplex.Table.comp 0 (atEnd false (suspendTable x))
      (verticalTable (vertex n true)) (up_endpoint_right_matching x) := by
  ext p b
  cases p with
  | zero =>
    cases b <;> simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      verticalTable, verticalRow, diagonalRow]
  | succ p =>
    cases p with
    | zero =>
      cases b <;>
        simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
          verticalTable, verticalRow, upRow, table_mass_zero]
      all_goals
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (add_zero _).symm
        · rfl
        · apply Subtype.ext
          funext ⟨index⟩
          cases index <;> rfl
    | succ p =>
      simp only [up_succ, comp_row, Nat.not_lt_zero, ite_false, Nat.succ_ne_zero]
      simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
        verticalTable, verticalRow, upRow]
      exact Prod.ext (add_zero _).symm rfl

lemma up_vertical {n : ℕ} (x : Table (complex.{u} n)) :
    up (verticalTable x) = verticalTable (suspendTable x) := by
  ext p b
  cases p with
  | zero => cases b <;> simp [verticalTable, verticalRow, diagonalRow]
  | succ p =>
    cases p with
    | zero =>
      cases b <;> simp [verticalTable, verticalRow, upRow, table_mass_zero]
      all_goals
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · rfl
        · rfl
        · apply Subtype.ext
          funext ⟨index⟩
          cases index <;> rfl
    | succ p =>
      by_cases hp : Even (p+1)
      · have hp' : ¬Even (p+1+1) := by rw [Nat.even_add_one]; exact not_not_intro hp
        cases b <;> simp [verticalTable, verticalRow, upRow, hp, hp'] <;> rfl
      · have hp' : Even (p+1+1) := by rw [Nat.even_add_one]; exact hp
        cases b <;> simp [verticalTable, verticalRow, upRow, hp, hp'] <;> rfl

lemma table_zero_cases (t : Table (K.{u} 0)) :
    (∃ a, t = atEnd a (project t)) ∨ t = verticalTable (topTable 0) := by
  by_cases h : mass 0 0 (sideRow t true 0 true) = mass 0 0 (sideRow t true 0 false)
  · exact Or.inl (endpoint_of_stationary_interval t h)
  · right
    obtain ⟨p,a,hp,he⟩ := table_classification (project t)
    have hp0 : p = 0 := by omega
    subst p
    have ht : project t = topTable 0 := by
      rw [he, ← face_nu]
      exact (complex 0).nu.face_of_fixed (topTable_bounded 0) (le_refl 0) a
    rw [crossing_vertical t h (by rw [ht]; exact topTable_bounded 0), ht]

lemma generated (n : ℕ) (P : Table (K.{u} n) → Prop)
    (hend : ∀ a x, P (atEnd a x)) (hvertical : ∀ x, P (verticalTable x))
    (hcomp : ∀ k s t (h : truncate k true s = truncate k false t),
      P s → P t → P (DirectedComplex.Table.comp k s t h)) : ∀ x, P x := by
  induction n with
  | zero =>
    intro x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he]; exact hend a (project x)
    · rw [he]; exact hvertical (topTable 0)
  | succ n ih =>
    intro x
    rcases table_cases x with ⟨a,he⟩ | ⟨a,he⟩ | hd
    · rw [he]; exact hend a (project x)
    · rw [he]; exact hvertical _
    · rw [← up_down x hd]
      apply ih (fun y => P (up y))
      · intro a y
        cases a
        · rw [up_endpoint_false]
          exact hcomp 0 _ _ _ (hvertical _) (hend true _)
        · rw [up_endpoint_true]
          exact hcomp 0 _ _ _ (hend false _) (hvertical _)
      · intro y
        rw [up_vertical]
        exact hvertical _
      · intro k s t h hs ht
        rw [up_comp s t h (up_composable h)]
        exact hcomp (k+1) _ _ _ hs ht

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table
variable {K : DirectedComplex.{u}}

lemma fixed_of_rows_zero {k : ℕ} (x : Table K)
    (h : ∀ p, k < p → ∀ b, x.row p b = 0) : truncate k false x = x := by
  have ht : x.row k true = x.row k false := by
    have hb := x.boundary k false
    rw [h (k+1) (by omega) false, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  ext p b
  rw [truncate_row]
  split_ifs with hp he
  · rfl
  · subst p
    cases b <;> simp [ht]
  · exact (h p (by omega) b).symm

lemma fixed_iff_rows_zero {k : ℕ} (x : Table K) :
    truncate k false x = x ↔ ∀ p, k < p → ∀ b, x.row p b = 0 :=
  ⟨fun h _ hp b => row_above_fixed x h hp b, fixed_of_rows_zero x⟩

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma up_injective (n : ℕ) : Function.Injective (@up.{u} n) := by
  intro s t h
  ext p b
  have hh := congrArg (fun x : Table (K (n+1)) => downRow n p (x.row (p+1) b)) h
  exact (downRow_upRow n p (s.row p b)).symm.trans (hh.trans (downRow_upRow n p (t.row p b)))

lemma up_fixed_iff {n k : ℕ} (t : Table (K.{u} n)) :
    truncate (k+1) false (up t) = up t ↔ truncate k false t = t := by
  rw [← up_truncate]
  exact (up_injective n).eq_iff

lemma project_fixed {n k : ℕ} (t : Table (K.{u} n))
    (h : truncate k false t = t) : truncate k false (project t) = project t := by
  change truncate k false ((complex n).cylinderProjection.table t) = _
  rw [← Hom.table_truncate, h]
  rfl

lemma atEnd_fixed {n k : ℕ} (a : Bool) (t : Table (complex.{u} n))
    (h : truncate k false t = t) : truncate k false (atEnd a t) = atEnd a t := by
  change truncate k false (((complex n).cylinderEndpoint a).table t) = _
  rw [← Hom.table_truncate, h]
  rfl

lemma suspend_fixed {n k : ℕ} (t : Table (complex.{u} n))
    (h : truncate k false t = t) : truncate (k+1) false (suspendTable t) = suspendTable t := by
  rw [← suspendTable_truncate, h]

lemma vertex_fixed (n : ℕ) (a : Bool) : truncate 0 false (vertex.{u} n a) = vertex n a := by
  simp only [vertex, truncate_truncate, lt_self_iff_false, ite_false]

lemma vertical_fixed {K : DirectedComplex.{u}} {k : ℕ} (t : Table K)
    (h : truncate k false t = t) :
    truncate (k+1) false (verticalTable t) = verticalTable t := by
  apply fixed_of_rows_zero
  rintro (_ | p) hp b
  · omega
  · have hz := row_above_fixed t h (by omega : k < p) b
    have hz' := row_above_fixed t h (by omega : k < p+1) b
    simp [verticalTable, verticalRow, hz, hz']

lemma vertical_fixed_iff {K : DirectedComplex.{u}} {k : ℕ} (t : Table K) :
    truncate (k+1) false (verticalTable t) = verticalTable t ↔ truncate k false t = t := by
  refine ⟨?_, vertical_fixed t⟩
  intro h
  apply fixed_of_rows_zero
  intro p hp b
  have hz := congrArg (fun x : K.cylinder.Chain (p+1) => x.2.2)
    (row_above_fixed (verticalTable t) h (by omega : k+1 < p+1) b)
  simp only [verticalTable, verticalRow] at hz
  split_ifs at hz <;> exact hz

lemma zero_is_endpoint {n : ℕ} (t : Table (K.{u} n))
    (h : truncate 0 false t = t) : ∃ a, t = atEnd a (project t) := by
  apply endpoint_of_stationary_interval
  have hz : crossRow t 0 false = 0 := congrArg (fun x : (K n).Chain 1 => x.2.2)
    (row_above_fixed t h (by omega : 0 < 1) false)
  have hm := cross_mass_vertex t false
  erw [hz, map_zero] at hm
  exact sub_eq_zero.mp hm.symm

lemma generated_bounded (n k : ℕ) (P : Table (K.{u} n) → Prop)
    (hend : ∀ a x, truncate k false x = x → P (atEnd a x))
    (hvertical : ∀ r, r < k → ∀ x, truncate r false x = x → P (verticalTable x))
    (hcomp : ∀ l s t (h : truncate l true s = truncate l false t),
      P s → P t → P (DirectedComplex.Table.comp l s t h)) :
    ∀ x, truncate k false x = x → P x := by
  induction n generalizing k with
  | zero =>
    intro x hx
    cases k with
    | zero =>
      obtain ⟨a,he⟩ := zero_is_endpoint x hx
      rw [he]
      exact hend a (project x) (project_fixed x hx)
    | succ k =>
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · rw [he]; exact hend a (project x) (project_fixed x hx)
      · rw [he]; exact hvertical 0 (by omega) (topTable 0) (topTable_bounded 0)
  | succ n ih =>
    intro x hx
    cases k with
    | zero =>
      obtain ⟨a,he⟩ := zero_is_endpoint x hx
      rw [he]
      exact hend a (project x) (project_fixed x hx)
    | succ k =>
      rcases table_cases x with ⟨a,he⟩ | ⟨a,he⟩ | hd
      · rw [he]; exact hend a (project x) (project_fixed x hx)
      · rw [he]; exact hvertical 0 (by omega) (vertex n a) (vertex_fixed n a)
      · have hdown : truncate k false (down x hd) = down x hd := by
          apply (up_fixed_iff _).mp
          rw [up_down x hd]
          exact hx
        rw [← up_down x hd]
        apply ih k (fun y => P (up y)) ?_ ?_ ?_ (down x hd) hdown
        · intro a y hy
          cases a
          · rw [up_endpoint_false]
            exact hcomp 0 _ _ _ (hvertical 0 (by omega) _ (vertex_fixed _ _))
              (hend true _ (suspend_fixed y hy))
          · rw [up_endpoint_true]
            exact hcomp 0 _ _ _ (hend false _ (suspend_fixed y hy))
              (hvertical 0 (by omega) _ (vertex_fixed _ _))
        · intro r hr y hy
          rw [up_vertical]
          exact hvertical (r+1) (by omega) _ (suspend_fixed y hy)
        · intro l s t h hs ht
          rw [up_comp s t h (up_composable h)]
          exact hcomp (l+1) _ _ _ hs ht

lemma functor_ext {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y)
    (hend : ∀ a x, F.map (atEnd a x) = G.map (atEnd a x))
    (hvert : ∀ x, F.map (verticalTable x) = G.map (verticalTable x)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext x
  apply generated n (fun t => F.map t = G.map t) hend hvert ?_ x
  intro k s t h hs ht
  have hf := F.map_comp k s t h (by erw [← F.map_target, ← F.map_source]; exact congrArg F.map h)
  have hg := G.map_comp k s t h (by erw [← G.map_target, ← G.map_source]; exact congrArg G.map h)
  exact hf.trans ((Y.comp_congr_cells k _ _ hs ht).trans hg.symm)

lemma functor_ext_truncated {n k : ℕ} {Y : OmegaCategory.{v}} (hY : Y.IsTruncated k)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y)
    (hend : ∀ a x, truncate k false x = x → F.map (atEnd a x) = G.map (atEnd a x))
    (hvert : ∀ r, r < k → ∀ x, truncate r false x = x →
      F.map (verticalTable x) = G.map (verticalTable x)) : F = G := by
  have hb (x : Table (K n)) (hx : truncate k false x = x) : F.map x = G.map x := by
    apply generated_bounded n k (fun t => F.map t = G.map t) hend hvert ?_ x hx
    intro l s t h hs ht
    have hf := F.map_comp l s t h (by erw [← F.map_target, ← F.map_source]; exact congrArg F.map h)
    have hg := G.map_comp l s t h (by erw [← G.map_target, ← G.map_source]; exact congrArg G.map h)
    exact hf.trans ((Y.comp_congr_cells l _ _ hs ht).trans hg.symm)
  apply OmegaCategory.Functor.ext
  funext x
  have he := hb (truncate k false x) (by erw [truncate_truncate, ite_self])
  change F.map ((K n).nu.source k x) = G.map ((K n).nu.source k x) at he
  rw [F.map_source, G.map_source, hY, hY] at he
  exact he

end Thomason.GrayRecursive

end

end OAI
