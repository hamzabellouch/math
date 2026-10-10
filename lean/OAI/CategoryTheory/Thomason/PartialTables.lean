import Mathlib
import OAI.CategoryTheory.Thomason.BoundaryQuotients
import OAI.CategoryTheory.Thomason.PosetComparison

namespace OAI

/-! Partial Tables. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table OmegaCategory NormalizedChains
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def image (f : PartialHom K L n) (x : Table K) : (truncation n L.nu).val.Cell :=
  (truncationUnit n L.nu).map (f.table x)

lemma image_source (f : PartialHom K L n) (k : ℕ) (x : Table K) :
    f.image (truncate k false x) = (truncation n L.nu).val.source k (f.image x) := by
  change (truncationUnit n L.nu).map (f.table (truncate k false x)) = _
  rw [f.table_source]
  exact (truncationUnit n L.nu).map_source k _

lemma image_source_n (f : PartialHom K L n) (x : Table K) :
    f.image (truncate n false x) = f.image x := by
  exact congrArg (truncationUnit n L.nu).map (f.table_source_n x)

lemma image_target_lt (f : PartialHom K L n) (k : ℕ) (hk : k<n) (x : Table K) :
    f.image (truncate k true x) = (truncation n L.nu).val.target k (f.image x) := by
  change (truncationUnit n L.nu).map (f.table (truncate k true x)) = _
  rw [f.table_target_lt k hk]
  exact (truncationUnit n L.nu).map_target k _

lemma image_composable (f : PartialHom K L n) {k : ℕ} (hk : k<n) {x y : Table K}
    (h : truncate k true x = truncate k false y) :
    (truncation n L.nu).val.target k (f.image x) = (truncation n L.nu).val.source k (f.image y) := by
  rw [← f.image_target_lt k hk,← f.image_source,h]

lemma image_comp_lt (f : PartialHom K L n) {k : ℕ} (hk : k<n) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    f.image (comp k x y h) = (truncation n L.nu).val.comp k (f.image x) (f.image y)
      (f.image_composable hk h) := by
  change (truncationUnit n L.nu).map (f.table (comp k x y h)) = _
  rw [f.table_comp_lt hk]
  exact (truncationUnit n L.nu).map_comp k _ _ (f.table_composable hk h) (f.image_composable hk h)

lemma image_boundary_of_bounded (f : PartialHom K L n) (x : Table K)
    (hx : truncate n false x = x) : f.image x = f.image (truncate n true x) := by
  exact congrArg f.image (K.nu.target_eq_self_of_source_eq_self hx).symm

lemma image_boundary_comp (f : PartialHom K L n) (k : ℕ) (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (hx : f.image x = f.image (truncate n true x))
    (hy : f.image y = f.image (truncate n true y)) :
    f.image (comp k x y h) = f.image (truncate n true (comp k x y h)) := by
  by_cases hk : k<n
  · erw [truncate_comp_gt n k hk true x y h (K.nu.target_composable hk h),
      f.image_comp_lt hk,f.image_comp_lt hk]
    congr 1
  · have hkn : n ≤ k := by omega
    rw [← f.image_source_n (comp k x y h),source_comp_le n k hkn,
      target_comp_le n k hkn,f.image_source_n]
    by_cases he : n = k
    · subst k
      exact hx.trans ((congrArg f.image h).trans ((f.image_source_n y).trans hy))
    · have hn : n < k := by omega
      have hh := congrArg (truncate n false) h
      rw [truncate_truncate,ite_eq_left hn,truncate_truncate,ite_eq_left hn] at hh
      exact ((f.image_source_n x).symm.trans
        ((congrArg f.image hh).trans (f.image_source_n y))).trans hy

variable {N : ℕ}

lemma image_boundary_of_atoms (f : PartialHom (complex (Fin (N+1))) L n)
    (hatom : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)),
      l.length = n+1 → f.image (simplexAtom a l (ha.imp le_of_lt)).table =
        f.image (truncate n true (simplexAtom a l (ha.imp le_of_lt)).table))
    (x : Table (complex (Fin (N+1)))) :
    f.image x = f.image (truncate n true x) := by
  have hb (z : Table (complex (Fin (N+1))))
      (hz : truncate (n+1) false z = z) :
      f.image z = f.image (truncate n true z) := by
    induction oriental_all_atomic z with
    | atom a l ha =>
      have hl := simplexAtom_dimension_le a l ha hz
      by_cases he : l.length = n+1
      · exact hatom a l ha he
      · apply f.image_boundary_of_bounded
        exact (complex (Fin (N+1))).nu.source_fixed_upwards (i := l.length) (by omega)
          (by exact (simplexAtom a l (ha.imp le_of_lt)).dimension)
    | compose k x y h hx hy ihx ihy =>
      obtain ⟨hx',hy'⟩ := comp_dimension_factors x y h hz
      exact f.image_boundary_comp k x y h (ihx hx') (ihy hy')
  have hh := hb (truncate (n+1) false x) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])
  have hf : f.image (truncate (n+1) false x) = f.image x := by
    rw [← f.image_source_n (truncate (n+1) false x),truncate_truncate,
      ite_eq_left (by omega : n < n+1),f.image_source_n]
  rw [hf,truncate_truncate,ite_eq_left (by omega : n < n+1)] at hh
  exact hh

def extendOriental (f : PartialHom (complex (Fin (N+1))) L n)
    (hatom : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)),
      l.length = n+1 → f.image (simplexAtom a l (ha.imp le_of_lt)).table =
        f.image (truncate n true (simplexAtom a l (ha.imp le_of_lt)).table)) :
    OmegaCategory.Functor (Oriental N) (truncation n L.nu).val where
  map := f.image
  map_source := f.image_source
  map_target k x := by
    change f.image (truncate k true x) = (truncation n L.nu).val.target k (f.image x)
    by_cases hk : k<n
    · exact f.image_target_lt k hk x
    · have hkn : n ≤ k := by omega
      have ht : (truncation n L.nu).val.target k (f.image x) = f.image x :=
        (truncation n L.nu).val.target_eq_self_of_source_eq_self
          ((truncation n L.nu).val.source_fixed_upwards hkn ((truncation n L.nu).property _))
      rw [ht,← f.image_source_n (truncate k true x)]
      by_cases he : n = k
      · subst k
        erw [truncate_truncate,ite_eq_right (Nat.lt_irrefl n)]
        exact (f.image_boundary_of_atoms hatom x).symm
      · erw [truncate_truncate,ite_eq_left (by omega : n<k),f.image_source_n]
  map_comp k x y h h' := by
    change f.image (comp k x y h) = (truncation n L.nu).val.comp k (f.image x) (f.image y) h'
    by_cases hk : k<n
    · exact f.image_comp_lt hk x y h
    · have hkn : n ≤ k := by omega
      erw [← f.image_source_n (comp k x y h),source_comp_le n k hkn,f.image_source_n]
      have hxf : (truncation n L.nu).val.source k (f.image x) = f.image x :=
        (truncation n L.nu).val.source_fixed_upwards hkn ((truncation n L.nu).property _)
      have hyf : (truncation n L.nu).val.source k (f.image y) = f.image y :=
        (truncation n L.nu).val.source_fixed_upwards hkn ((truncation n L.nu).property _)
      have he : f.image x = f.image y := by
        rw [(truncation n L.nu).val.target_eq_self_of_source_eq_self hxf,hyf] at h'
        exact h'
      have hh := (truncation n L.nu).val.unit_left k (f.image y)
        ((truncation n L.nu).val.target_source_self k _)
      have hc := comp_congr_cells (truncation n L.nu).val k
        ((truncation n L.nu).val.target_source_self k _) h'
        (hyf.trans he.symm) rfl
      exact he.trans (hh.symm.trans hc)

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

def homWord (f : PartialHom (complex E) (complex D) n) : List E → Chains D
  | [] => bracket []
  | a :: l => (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).val

def homTotal (f : PartialHom (complex E) (complex D) n) : Chains E →ₗ[ℤ] Chains D :=
  Finsupp.linearCombination ℤ (fun l => homWord f l.val)

lemma homTotal_bracket (f : PartialHom (complex E) (complex D) n) (l : List E) :
    homTotal f (bracket l) = homWord f l := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  · rw [bracket_of_not_pairwise h, map_zero]
    cases l with
    | nil => exact (h (by simp)).elim
    | cons a l =>
      change 0 = (f.map l.length (⟨bracket (a::l), bracket_mem_grade (a::l)⟩ : (complex E).Chain l.length)).val
      have he : (⟨bracket (a::l), bracket_mem_grade (a::l)⟩ : (complex E).Chain l.length) = 0 :=
        Subtype.ext (bracket_of_not_pairwise h)
      erw [he, map_zero]; rfl

lemma homTotal_grade (f : PartialHom (complex E) (complex D) n) {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) : homTotal f c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  rintro ⟨l,hl⟩ hlen
  subst k
  cases l with
  | nil => exact bracket_mem_grade ([] : List D)
  | cons a l => exact (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).property

lemma homTotal_map (f : PartialHom (complex E) (complex D) n) (p : ℕ) (c : (complex E).Chain p) :
    homTotal f c.val = (f.map p c).val := by
  obtain ⟨c,hc⟩ := c
  apply grade_induction (M := fun c hc => homTotal f c =
    (f.map p ⟨c,hc⟩).val) ?_ ?_ ?_ ?_ c hc
  · rintro ⟨l,hl⟩ hlen
    rw [homTotal_bracket]
    cases l with
    | nil => simp at hlen
    | cons a l =>
      have he : l.length = p := by simpa using hlen
      subst p
      rfl
  · rw [map_zero]; exact (congrArg Subtype.val (f.map p).map_zero).symm
  · intro c d hc hd ihc ihd
    rw [map_add, ihc, ihd]
    exact (congrArg Subtype.val ((f.map p).map_add ⟨c,hc⟩ ⟨d,hd⟩)).symm
  · intro r c hc ih
    rw [map_smul,ih]
    exact (congrArg Subtype.val ((f.map p).map_zsmul r ⟨c,hc⟩)).symm

lemma homTotal_positive (f : PartialHom (complex E) (complex D) n) {c : Chains E}
    (hc : Positive c) : Positive (homTotal f c) := by
  apply linearCombination_positive _ ?_ hc
  rintro ⟨l,hl⟩
  cases l with
  | nil => exact bracket_positive []
  | cons a l => exact f.map_positive l.length _ (bracket_positive _)

lemma homTotal_boundary (f : PartialHom (complex E) (complex D) n)
    {k : ℕ} (hk : k ≤ n+1) (c : Chains E) (hc : c ∈ grade k) :
    homTotal f (boundary c) = boundary (homTotal f c) := by
  apply grade_induction (M := fun c _ => homTotal f (boundary c) = boundary (homTotal f c))
    ?_ ?_ ?_ ?_ c hc
  · rintro ⟨l,hl⟩ hlen
    cases l with
    | nil => simp [homTotal_bracket,homWord,boundary_bracket]
    | cons a l =>
      cases l with
      | nil =>
        rw [homTotal_bracket]
        change homTotal f (boundary (bracket [a])) =
          boundary (f.map 0 ⟨bracket [a],bracket_mem_grade [a]⟩).val
        rw [grade_zero_eq_empty (boundary_mem_grade
          (f.map 0 ⟨bracket [a],bracket_mem_grade [a]⟩).property)]
        have hau := f.map_augmentation ⟨bracket [a], bracket_mem_grade [a]⟩
        change emptyCoefficient (boundary (f.map 0 _).val) =
          emptyCoefficient (boundary (bracket [a])) at hau
        rw [hau, boundary_bracket (by simp), wordBoundary_cons,
          wordBoundary_nil, map_zero, sub_zero, homTotal_bracket]
        simp [homWord]
      | cons b l =>
        let x : (complex E).Chain (l.length+1) :=
          ⟨bracket (a::b::l),bracket_mem_grade (a::b::l)⟩
        have hp : l.length < n := by simp only [List.length_cons] at hlen; omega
        have hd := congrArg Subtype.val (f.map_d l.length hp x)
        change homTotal f ((complex E).d l.length x).val =
          boundary (homTotal f x.val)
        rw [homTotal_map,homTotal_map]
        exact hd
  · simp only [map_zero]
  · intro c d hc hd ihc ihd; simp only [map_add,ihc,ihd]
  · intro r c hc ih; simp only [map_smul,ih]

lemma homTotal_vertex_exists (f : PartialHom (complex E) (complex D) n) (a : E) :
    ∃ b : D, homTotal f (bracket [a]) = bracket [b] := by
  apply positive_augmentation_one (homTotal_grade f (bracket_mem_grade [a]))
    (homTotal_positive f (bracket_positive [a]))
  rw [homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩]
  exact (f.map_augmentation ⟨bracket [a],bracket_mem_grade [a]⟩).trans (by
    change emptyCoefficient (boundary (bracket [a])) = 1
    rw [boundary_bracket (by simp)]
    simp [wordBoundary,emptyCoefficient_bracket])

def homVertex (f : PartialHom (complex E) (complex D) n) (a : E) : D :=
  (homTotal_vertex_exists f a).choose

lemma homTotal_vertex (f : PartialHom (complex E) (complex D) n) (a : E) :
    homTotal f (bracket [a]) = bracket [homVertex f a] :=
  (homTotal_vertex_exists f a).choose_spec

lemma homVertex_monotone (f : PartialHom (complex E) (complex D) n) (hn : 0<n) : Monotone (homVertex f) := by
  intro a b hab
  apply table_source_le_target_partial (f.table (edgeTable a b hab))
  · simp only [PartialHom.table,hn,ite_true]
    exact (homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩).symm.trans
      (homTotal_vertex f a)
  · simp only [PartialHom.table,hn,ite_true]
    exact (homTotal_map f 0 ⟨bracket [b],bracket_mem_grade [b]⟩).symm.trans
      (homTotal_vertex f b)

def homVertexOrderHom (f : PartialHom (complex E) (complex D) n) (hn : 0<n) : E →o D :=
  ⟨homVertex f, homVertex_monotone f hn⟩

lemma homTotal_bracket_supportedOn_lower (f : PartialHom (complex E) (complex D) n)
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) (hln : l.length ≤ n+1) : homTotal f (bracket l) ∈ supportedOn S := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | h z ih =>
    cases l with
    | nil =>
      rw [homTotal_bracket]
      exact bracket_mem_supportedOn (by simp)
    | cons a l =>
      cases l with
      | nil =>
        rw [homTotal_vertex]
        exact bracket_mem_supportedOn (by simpa using hs)
      | cons b l =>
        apply positive_supportedOn_of_boundary_partial hS
          (homTotal_grade f (bracket_mem_grade (a::b::l)))
          (homTotal_positive f (bracket_positive _))
        rw [← homTotal_boundary f hln _ (bracket_mem_grade _), boundary_bracket hl, ← faces_bracket]
        change (homTotal f).toAddMonoidHom (faces bracket (a::b::l)) ∈ _
        rw [faces_hom]
        apply faces_mem_submodule_length
        intro m hm hmlen
        exact ih m.length (by simp only [List.length_cons] at hmlen hlen; omega)
          m (hl.sublist hm) (fun a ha => hs a (hm.subset ha)) (by omega) rfl

def cutWord (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) (l : List E) : Chains D :=
  l.reverseRecOn (bracket []) (fun l a c =>
    if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) c)

@[simp] lemma cutWord_nil (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) :
    cutWord f θ [] = bracket [] := by
  unfold cutWord
  exact List.reverseRecOn_nil _ _

lemma cutWord_append (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (a : E) : cutWord f θ (l++[a]) =
      if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) (cutWord f θ l) :=
  by unfold cutWord; rw [List.reverseRecOn_concat]

lemma cutWord_of_all_zero (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (h : ∀ a ∈ l, θ a = 0) : cutWord f θ l = homTotal f (bracket l) := by
  cases l using List.reverseRecOn with
  | nil => rw [cutWord_nil, homTotal_bracket]; rfl
  | append_singleton l a => rw [cutWord_append, ite_eq_left (h a (by simp))]

lemma cutWord_positive (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) : Positive (cutWord f θ l) := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_positive []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_positive f (bracket_positive _)
    · exact append_positive _ ih

lemma cutWord_grade (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) : cutWord f θ l ∈ grade l.length := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_grade []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_grade f (bracket_mem_grade _)
    · simpa only [List.length_append,List.length_singleton] using append_mem_grade _ ih

lemma cutWord_supportedOn_lower (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) (hln : l.length ≤ n+1) : cutWord f θ l ∈ supportedOn S := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_supportedOn (by simp)
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_bracket_supportedOn_lower f S hS _ hl hs hln
    · exact append_mem_supportedOn (hs a (by simp))
        (ih (List.pairwise_append.mp hl).1 (fun b hb => hs b (List.mem_append_left _ hb))
          (by simp only [List.length_append,List.length_singleton] at hln; omega))

lemma cutWord_boundary (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) (hln : l.length ≤ n+1) :
    boundary (cutWord f θ l) = faces (cutWord f θ) l := by
  induction l using List.reverseRecOn with
  | nil => simp [boundary_bracket]
  | append_singleton l a ih =>
    rw [cutWord_append]
    by_cases hθ : θ a = 0
    · rw [ite_eq_left hθ, ← homTotal_boundary f hln _ (bracket_mem_grade _), boundary_bracket hl, ← faces_bracket]
      change (homTotal f).toAddMonoidHom (faces bracket (l++[a])) = _
      rw [faces_hom]
      apply faces_congr
      intro m hm
      apply (cutWord_of_all_zero f θ m ?_).symm
      intro b hb
      have hba : b ≤ a := by
        rcases List.mem_append.mp (hm.subset hb) with hb | hb
        · exact (List.pairwise_append.mp hl).2.2 b hb a (by simp)
        · simpa using (show b = a by simpa using hb).le
      have hle := θ.monotone hba
      rw [hθ] at hle
      exact le_antisymm hle (Fin.zero_le _)
    · rw [ite_eq_right hθ, boundary_append_supported _ (cutWord_grade f θ l)
        (cutWord_supportedOn_lower f θ _ (isLowerSet_Iic _) l
          (List.pairwise_append.mp hl).1 (fun b hb =>
            homVertex_monotone f hn ((List.pairwise_append.mp hl).2.2 b hb a (by simp)))
          (by simp only [List.length_append,List.length_singleton] at hln; omega)),
        ih (List.pairwise_append.mp hl).1
          (by simp only [List.length_append,List.length_singleton] at hln; omega), faces_append_singleton]
      congr 1
      change (append (homVertex f a)).toAddMonoidHom (faces (cutWord f θ) l) = _
      rw [faces_hom]
      apply faces_congr
      intro m _
      rw [cutWord_append,ite_eq_right hθ]
      rfl

lemma cutWord_eq_zero_of_not_pairwise (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hn : ¬l.Pairwise (· < ·)) : cutWord f θ l = 0 := by
  induction l using List.reverseRecOn with
  | nil => exact (hn (by simp)).elim
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · rw [bracket_of_not_pairwise hn,map_zero]
    · rename_i hθ
      by_cases hp : l.Pairwise (· < ·)
      · cases l using List.reverseRecOn with
        | nil => exact (hn (by simp)).elim
        | append_singleton r b =>
          have hba : b ≤ a := (List.pairwise_append.mp hl).2.2 b (by simp) a (by simp)
          have he : b = a := by
            by_contra he
            have hba' : b < a := lt_of_le_of_ne hba he
            apply hn
            apply List.pairwise_append.mpr
            refine ⟨hp, by simp, ?_⟩
            intro c hc d hd
            have hed : d = a := by simpa using hd
            subst d
            rcases List.mem_append.mp hc with hc | hc
            · exact lt_trans ((List.pairwise_append.mp hp).2.2 c hc b (by simp)) hba'
            · have hec : c = b := by simpa using hc
              simpa [hec] using hba'
          subst b
          rw [cutWord_append,ite_eq_right hθ,append_append_self]
      · rw [ih (List.pairwise_append.mp hl).1 hp,map_zero]

def cutTotal (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) :
    Chains E →ₗ[ℤ] Chains D := Finsupp.linearCombination ℤ (fun w => cutWord f θ w.val)

lemma cutTotal_bracket (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) : cutTotal f θ (bracket l) = cutWord f θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single,one_smul]
  · rw [bracket_of_not_pairwise hs,map_zero,cutWord_eq_zero_of_not_pairwise f θ l hl hs]

lemma cutTotal_grade (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    {k : ℕ} {c : Chains E} (hc : c ∈ grade k) : cutTotal f θ c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [← hw] using cutWord_grade f θ w.val

lemma cutTotal_positive (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    {c : Chains E} (hc : Positive c) : Positive (cutTotal f θ c) :=
  linearCombination_positive _ (fun w => cutWord_positive f θ w.val) hc

lemma cutTotal_wordBoundary (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    cutTotal f θ (wordBoundary l) = faces (cutWord f θ) l := by
  rw [← faces_bracket]
  change (cutTotal f θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact cutTotal_bracket f θ m (hl.sublist hm)

lemma cutTotal_boundary (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2)
    {k : ℕ} (hk : k ≤ n+1) (c : Chains E) (hc : c ∈ grade k) :
    cutTotal f θ (boundary c) = boundary (cutTotal f θ c) := by
  apply grade_induction (M := fun c _ => cutTotal f θ (boundary c) = boundary (cutTotal f θ c))
    ?_ ?_ ?_ ?_ c hc
  · intro w hw
    rw [boundary_bracket (w.property.imp le_of_lt),
      cutTotal_bracket f θ w.val (w.property.imp le_of_lt),
      cutWord_boundary f hn θ w.val (w.property.imp le_of_lt) (by omega),
      cutTotal_wordBoundary f θ w.val (w.property.imp le_of_lt)]
  · simp only [map_zero]
  · intro c d hc hd ihc ihd; simp only [map_add,ihc,ihd]
  · intro r c hc ih; simp only [map_smul,ih]

lemma cutTotal_empty (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) :
    cutTotal f θ (bracket []) = bracket [] := by
  rw [cutTotal_bracket f θ [] (by simp),cutWord_nil]

lemma cutTotal_augmentation (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2)
    {c : Chains E} (hc : c ∈ grade 1) :
    emptyCoefficient (boundary (cutTotal f θ c)) = emptyCoefficient (boundary c) := by
  rw [← cutTotal_boundary f hn θ (by omega) _ hc, grade_zero_eq_empty (boundary_mem_grade hc), map_smul,
    cutTotal_empty]
  simp only [map_smul,emptyCoefficient_bracket,smul_eq_mul]

def cutHom (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (θ : E →o Fin 2) :
    PartialHom (complex E) (complex D) n where
  map _p :=
    { toFun := fun c => ⟨cutTotal f θ c.val, cutTotal_grade f θ c.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
  map_d p hp x := Subtype.ext (cutTotal_boundary f hn θ (by omega) x.val x.property)
  map_augmentation x := cutTotal_augmentation f hn θ x.property
  map_positive _ _ hc := cutTotal_positive f θ hc

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table OmegaCategory
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def oneStep (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) : Table L where
  row p b := f.map p (x.row p b)
  positive p b := f.map_positive p _ (x.positive p b)
  boundary p b := by
    by_cases hp : p<n
    · rw [← f.map_d p hp,x.boundary,map_sub]
    · by_cases he : p=n
      · subst p; rw [← hd b,x.boundary,map_sub]
      · have hnp : n+1 ≤ p := by omega
        have hx' := K.nu.source_fixed_upwards hnp hx
        rw [row_above_fixed x hx (by omega : n+1 < p+1) b,map_zero,map_zero]
        have heq : x.row p true = x.row p false := by
          have hh := congrArg (fun t : Table K => t.row p true) hx'
          change (truncate p false x).row p true = x.row p true at hh
          rw [truncate_top_row] at hh
          exact hh.symm
        rw [heq,sub_self]
  augmentation b := by rw [f.map_augmentation,x.augmentation]
  bounded := ⟨n+1,fun p hp b => by rw [row_above_fixed x hx hp b,map_zero]⟩

lemma table_eq_oneStep_source (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) :
    f.table x = truncate n false (f.oneStep x hx hd) := by
  ext p b
  simp only [table,oneStep,truncate_row]

lemma table_target_eq_oneStep_target (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) :
    f.table (truncate n true x) = truncate n true (f.oneStep x hx hd) := by
  ext p b
  simp only [table,oneStep,truncate_row]
  split_ifs <;> simp_all only

lemma image_boundary_of_oneStep (f : PartialHom K L n) (x : Table K)
    (hx : truncate (n+1) false x = x)
    (hd : ∀ b, f.map n (K.d n (x.row (n+1) b)) = L.d n (f.map (n+1) (x.row (n+1) b))) :
    f.image x = f.image (truncate n true x) := by
  change (truncationUnit n L.nu).map (f.table x) =
    (truncationUnit n L.nu).map (f.table (truncate n true x))
  rw [f.table_eq_oneStep_source x hx hd,f.table_target_eq_oneStep_target x hx hd]
  exact ((truncationUnit n L.nu).map_source n _).trans
    (((truncation n L.nu).property _).trans
      (((truncation n L.nu).val.target_eq_self_of_source_eq_self
        ((truncation n L.nu).property _)).symm.trans
          ((truncationUnit n L.nu).map_target n _).symm))

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {C : OmegaCategory.{u}} {n N : ℕ}

lemma liftedChainMap_d_below (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (hp : p<n) (x : (complex (Fin (N+1))).Chain (p+1)) :
    liftedChainMap F p ((complex (Fin (N+1))).d p x) =
      C.lambdaD p (liftedChainMap F (p+1) x) := by
  apply truncationUnit_lambdaMap_injective C n p hp
  rw [liftedChainMap_unit]
  have hd := (simplexCounitInverse N).map_d p x
  change atomCounitInverse p ((complex (Fin (N+1))).d p x) =
    (Oriental N).lambdaD p (atomCounitInverse (p+1) x) at hd
  rw [hd]
  exact (LinearMap.congr_fun (F.lambdaMap_d p) _).trans
    ((congrArg ((truncation n C).val.lambdaD p) (liftedChainMap_unit F (p+1) x).symm).trans
      (LinearMap.congr_fun ((truncationUnit n C).lambdaMap_d p) _).symm)

variable {K : DirectedComplex.{u}}

def liftedPartial (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val) :
    PartialHom (complex (Fin (N+1))) K n where
  map p := (K.lambdaCounit.map p).comp (liftedChainMap F p).toAddMonoidHom
  map_d p hp x := by
    change K.lambdaCounit.map p (liftedChainMap F p ((complex (Fin (N+1))).d p x)) = _
    rw [liftedChainMap_d_below F p hp]
    exact K.lambdaCounit.map_d p _
  map_augmentation x := (K.lambdaCounit.map_augmentation _).trans (liftedChainMap_aug F x)
  map_positive p x hx := K.lambdaCounit.map_positive p _ (liftedChainMap_positive F p x hx)

lemma liftedMap_atom_row
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (hlen : l.length ≤ n) (p : ℕ) (b : Bool) :
    K.lambdaCounitMap p (liftedChainMap F p ((simplexAtom a l (ha.imp le_of_lt)).table.row p b)) =
      (truncationCellLift K.nu n l.length
        (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
          by exact (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)).val.row p b := by
  let A := simplexAtom a l (ha.imp le_of_lt)
  have hd : truncate l.length false A.table = A.table := by
    simpa only [List.length_cons,Nat.add_sub_cancel] using A.dimension
  let L := truncationCellLift K.nu n l.length (F.onCells l.length ⟨A.table,hd⟩)
  have hL : (truncationUnit n K.nu).map L.val = F.map A.table :=
    truncationCellLift_map K.nu n l.length _
  by_cases hp : p < l.length
  · have hl : liftedChainMap F p (A.table.row p b) = K.nu.lambdaGen
        (if b then K.nu.targetCell p L.val else K.nu.sourceCell p L.val) := by
      apply truncationUnit_lambdaMap_injective K.nu n p (by omega)
      rw [liftedChainMap_unit,atomCounitInverse_row]
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
      · erw [OmegaCategory.Functor.lambdaMap_gen,OmegaCategory.Functor.lambdaMap_gen]
        congr 1
        apply Subtype.ext
        change F.map (truncate p false A.table) =
          (truncationUnit n K.nu).map (truncate p false L.val)
        exact (F.map_source p A.table).trans
          ((congrArg ((truncation n K.nu).val.source p) hL.symm).trans
            ((truncationUnit n K.nu).map_source p L.val).symm)
      · erw [OmegaCategory.Functor.lambdaMap_gen,OmegaCategory.Functor.lambdaMap_gen]
        congr 1
        apply Subtype.ext
        change F.map (truncate p true A.table) =
          (truncationUnit n K.nu).map (truncate p true L.val)
        exact (F.map_target p A.table).trans
          ((congrArg ((truncation n K.nu).val.target p) hL.symm).trans
            ((truncationUnit n K.nu).map_target p L.val).symm)
    rw [hl]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · rw [K.lambdaCounitMap_gen]
      exact truncate_top_row p false L.val false
    · rw [K.lambdaCounitMap_gen]
      exact truncate_top_row p true L.val false
  · by_cases he : p = l.length
    · subst p
      have ht : A.table.row l.length b =
          (⟨bracket (a::l),bracket_mem_grade (a::l)⟩ : (complex (Fin (N+1))).Chain l.length) := by
        apply Subtype.ext
        have ht := A.top b
        have he : (a::l).length-1 = l.length := by simp
        rw [he] at ht
        exact ht
      rw [ht,liftedChainMap_bracket F l.length ⟨a::l,ha⟩ rfl,
        liftedBasis_cons F l.length a l ha rfl hd]
      rw [K.lambdaCounitMap_gen]
      change L.val.row l.length false = L.val.row l.length b
      have h := congrArg (fun t : Table K => t.row l.length b) L.property
      change (truncate l.length false L.val).row l.length b = L.val.row l.length b at h
      erw [truncate_top_row] at h
      exact h
    · have hlt : l.length < p := by omega
      rw [row_above_fixed A.table hd hlt b,map_zero,map_zero,
        row_above_fixed L.val L.property hlt b]

lemma liftedPartial_table_atom
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (hlen : l.length ≤ n) :
    (liftedPartial F).table (simplexAtom a l (ha.imp le_of_lt)).table =
      (truncationCellLift K.nu n l.length
        (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
          by exact (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)).val := by
  let L := truncationCellLift K.nu n l.length
    (F.onCells l.length ⟨(simplexAtom a l (ha.imp le_of_lt)).table,
      by exact (simplexAtom a l (ha.imp le_of_lt)).dimension⟩)
  have hL : truncate n false L.val = L.val := K.nu.source_fixed_upwards hlen L.property
  have table_eq : (liftedPartial F).table (simplexAtom a l (ha.imp le_of_lt)).table =
      truncate n false L.val := by
    ext p b
    simp only [PartialHom.table]
    erw [truncate_row]
    split_ifs
    · exact liftedMap_atom_row F a l ha hlen p b
    · exact liftedMap_atom_row F a l ha hlen p false
    · rfl
  exact table_eq.trans hL

lemma liftedPartial_image (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (x : Table (complex (Fin (N+1)))) : (liftedPartial F).image x = F.map x := by
  have hb (y : Table (complex (Fin (N+1)))) (hbound : truncate n false y = y) :
      (liftedPartial F).image y = F.map y := by
    induction oriental_all_atomic y with
    | atom a l ha =>
      have hl := simplexAtom_dimension_le a l ha hbound
      change (truncationUnit n K.nu).map ((liftedPartial F).table _) = _
      rw [liftedPartial_table_atom F a l ha hl]
      exact truncationCellLift_map K.nu n l.length _
    | compose k x y h hx hy ihx ihy =>
      obtain ⟨hx',hy'⟩ := comp_dimension_factors x y h hbound
      by_cases hk : k<n
      · rw [(liftedPartial F).image_comp_lt hk]
        exact (comp_congr_cells (truncation n K.nu).val k _ (F.map_composable h)
          (ihx hx') (ihy hy')).trans (F.map_comp k x y h (F.map_composable h)).symm
      · have hc := (complex (Fin (N+1))).nu.comp_of_left_source_fixed k x y h
          ((complex (Fin (N+1))).nu.source_fixed_upwards (by omega : n≤k) hx')
        change Table.comp k x y h = y at hc
        rw [hc]
        exact ihy hy'
  rw [← (liftedPartial F).image_source_n x,hb _ (by simp only [truncate_truncate,lt_self_iff_false,ite_false])]
  exact (F.map_source n x).trans ((truncation n K.nu).property _)

lemma oriental_functor_ext_truncated {D : OmegaCategory.{v}} (hD : D.IsTruncated n)
    (F G : OmegaCategory.Functor (Oriental N) D)
    (h : ∀ (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·)),
      l.length ≤ n → F.map (simplexAtom a l (ha.imp le_of_lt)).table =
        G.map (simplexAtom a l (ha.imp le_of_lt)).table) : F = G := by
  have hb (x : Table (complex (Fin (N+1)))) (hx : truncate n false x = x) :
      F.map x = G.map x := by
    induction oriental_all_atomic x with
    | atom a l ha => exact h a l ha (simplexAtom_dimension_le a l ha hx)
    | compose k x y hab hax hay ihx ihy =>
      obtain ⟨hx',hy'⟩ := comp_dimension_factors x y hab hx
      exact (F.map_comp k x y hab (F.map_composable hab)).trans
        ((comp_congr_cells D k _ _ (ihx hx') (ihy hy')).trans
          (G.map_comp k x y hab (G.map_composable hab)).symm)
  apply OmegaCategory.Functor.ext
  funext x
  exact (hD _).symm.trans ((F.map_source n x).symm.trans
    ((hb (truncate n false x) (by erw [truncate_truncate,ite_eq_right (Nat.lt_irrefl n)])).trans
      ((G.map_source n x).trans (hD _))))

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma cutWord_boundary_append_one (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) (l : List E) (a : E)
    (hl : (l++[a]).Pairwise (· ≤ ·)) (hln : l.length ≤ n+1) (hθ : θ a ≠ 0) :
    boundary (cutWord f θ (l++[a])) = faces (cutWord f θ) (l++[a]) := by
  rw [cutWord_append,ite_eq_right hθ, boundary_append_supported _ (cutWord_grade f θ l)
    (cutWord_supportedOn_lower f θ _ (isLowerSet_Iic _) l
      (List.pairwise_append.mp hl).1 (fun b hb =>
        homVertex_monotone f hn ((List.pairwise_append.mp hl).2.2 b hb a (by simp))) hln),
    cutWord_boundary f hn θ l (List.pairwise_append.mp hl).1 hln,faces_append_singleton]
  congr 1
  change (append (homVertex f a)).toAddMonoidHom (faces (cutWord f θ) l) = _
  rw [faces_hom]
  apply faces_congr
  intro m _
  rw [cutWord_append,ite_eq_right hθ]
  rfl

lemma cutTotal_eq_homTotal_of_supported (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (c : Chains E) (hc : c ∈ supportedOn {a | θ a = 0}) :
    cutTotal f θ c = homTotal f c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [cutTotal_bracket f θ w.val (w.property.imp le_of_lt),homTotal_bracket]
  exact (cutWord_of_all_zero f θ w.val
    ((mem_supportedOn_iff _ c).mp hc w (Finsupp.mem_support_iff.mp hw))).trans
      (homTotal_bracket f w.val)

lemma cutHom_table_of_supported (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn {a | θ a = 0}) :
    (cutHom f hn θ).table x = f.table x := by
  ext p b
  simp only [PartialHom.table]
  split_ifs
  · apply Subtype.ext
    exact (cutTotal_eq_homTotal_of_supported f θ _ (hx p b)).trans (homTotal_map f p _)
  · apply Subtype.ext
    exact (cutTotal_eq_homTotal_of_supported f θ _ (hx p false)).trans (homTotal_map f p _)
  · rfl

lemma cutHom_image_of_supported (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn {a | θ a = 0}) :
    (cutHom f hn θ).image x = f.image x :=
  congrArg (OmegaCategory.truncationUnit n (complex D).nu).map
    (cutHom_table_of_supported f hn θ x hx)

lemma truncate_supported {S : Set E} (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) (k : ℕ) (e : Bool) :
    ∀ p b, ((Table.truncate k e x).row p b).val ∈ supportedOn S := by
  intro p b
  simp only [Table.truncate_row]
  split_ifs
  · exact hx p b
  · exact hx p e
  · exact (supportedOn S).zero_mem

end Thomason.PartialNormalized

end

end OAI
