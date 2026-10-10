import Mathlib
import OAI.CategoryTheory.Thomason.FiberComparisons
import OAI.CategoryTheory.Thomason.FiniteChains

namespace OAI

/-! Poset Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma grade_induction {k : ℕ} {M : (c : Chains E) → c ∈ grade k → Prop}
    (hgen : ∀ (l : Word E) (hl : l.val.length = k),
      M (bracket l.val) (hl ▸ bracket_mem_grade l.val))
    (hz : M 0 (grade k).zero_mem)
    (ha : ∀ c d hc hd, M c hc → M d hd → M (c+d) ((grade k).add_mem hc hd))
    (hs : ∀ (r : ℤ) c hc, M c hc → M (r • c) ((grade k).smul_mem r hc))
    (c : Chains E) (hc : c ∈ grade k) : M c hc := by
  have hspan : c ∈ Submodule.span ℤ ((fun l : Word E => Finsupp.single l 1) ''
      {l | l.val.length = k}) := by
    rwa [← Finsupp.supported_eq_span_single]
  suffices ∀ h : c ∈ grade k, M c h from this hc
  induction hspan using Submodule.span_induction with
  | mem c h =>
    obtain ⟨l, hl, rfl⟩ := h
    intro hc
    simpa only [bracket_of_pairwise l.property] using hgen l hl
  | zero => exact fun _ => hz
  | add c d hc hd ihc ihd =>
    have hc' : c ∈ grade k := by rwa [grade, Finsupp.supported_eq_span_single]
    have hd' : d ∈ grade k := by rwa [grade, Finsupp.supported_eq_span_single]
    exact fun _ => ha c d hc' hd' (ihc hc' hc') (ihd hd' hd')
  | smul r c hc ih =>
    have hc' : c ∈ grade k := by rwa [grade, Finsupp.supported_eq_span_single]
    exact fun _ => hs r c hc' (ih hc' hc')

def homWord (f : Hom (complex E) (complex D)) : List E → Chains D
  | [] => bracket []
  | a :: l => (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).val

def homTotal (f : Hom (complex E) (complex D)) : Chains E →ₗ[ℤ] Chains D :=
  Finsupp.linearCombination ℤ (fun l => homWord f l.val)

lemma homTotal_bracket (f : Hom (complex E) (complex D)) (l : List E) :
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

lemma homTotal_grade (f : Hom (complex E) (complex D)) {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) : homTotal f c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  rintro ⟨l,hl⟩ hlen
  subst k
  cases l with
  | nil => exact bracket_mem_grade ([] : List D)
  | cons a l => exact (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).property

lemma homTotal_map (f : Hom (complex E) (complex D)) (p : ℕ) (c : (complex E).Chain p) :
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

lemma homTotal_positive (f : Hom (complex E) (complex D)) {c : Chains E}
    (hc : Positive c) : Positive (homTotal f c) := by
  apply linearCombination_positive _ ?_ hc
  rintro ⟨l,hl⟩
  cases l with
  | nil => exact bracket_positive []
  | cons a l => exact f.map_positive l.length _ (bracket_positive _)

lemma homTotal_boundary (f : Hom (complex E) (complex D)) (c : Chains E) :
    homTotal f (boundary c) = boundary (homTotal f c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add w z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single w z = z • bracket w.val := by
      rw [bracket_of_pairwise w.property]; simp
    rw [hz]
    simp only [map_smul]
    congr 1
    obtain ⟨l,hl⟩ := w
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
        have hd := congrArg Subtype.val (f.map_d l.length x)
        change homTotal f ((complex E).d l.length x).val =
          boundary (homTotal f x.val)
        rw [homTotal_map,homTotal_map]
        exact hd

lemma homTotal_vertex_exists (f : Hom (complex E) (complex D)) (a : E) :
    ∃ b : D, homTotal f (bracket [a]) = bracket [b] := by
  apply positive_augmentation_one (homTotal_grade f (bracket_mem_grade [a]))
    (homTotal_positive f (bracket_positive [a]))
  rw [homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩]
  exact (f.map_augmentation ⟨bracket [a],bracket_mem_grade [a]⟩).trans (by
    change emptyCoefficient (boundary (bracket [a])) = 1
    rw [boundary_bracket (by simp)]
    simp [wordBoundary,emptyCoefficient_bracket])

def homVertex (f : Hom (complex E) (complex D)) (a : E) : D :=
  (homTotal_vertex_exists f a).choose

lemma homTotal_vertex (f : Hom (complex E) (complex D)) (a : E) :
    homTotal f (bracket [a]) = bracket [homVertex f a] :=
  (homTotal_vertex_exists f a).choose_spec

lemma homVertex_monotone (f : Hom (complex E) (complex D)) : Monotone (homVertex f) := by
  intro a b hab
  apply table_source_le_target_partial (f.table (edgeTable a b hab))
  · exact (homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩).symm.trans
      (homTotal_vertex f a)
  · exact (homTotal_map f 0 ⟨bracket [b],bracket_mem_grade [b]⟩).symm.trans
      (homTotal_vertex f b)

def homVertexOrderHom (f : Hom (complex E) (complex D)) : E →o D :=
  ⟨homVertex f, homVertex_monotone f⟩

lemma faces_mem_submodule_length {B : Type w} (Q : Submodule ℤ (Chains D))
    (H : List B → Chains D) (l : List B)
    (hH : ∀ m, m.Sublist l → m.length + 1 = l.length → H m ∈ Q) : faces H l ∈ Q := by
  induction l generalizing H with
  | nil => exact Q.zero_mem
  | cons a l ih =>
    rw [faces_cons]
    apply Q.sub_mem
    · exact hH l (List.sublist_cons_self a l) rfl
    · apply ih
      intro m hm hlen
      exact hH (a::m) (List.Sublist.cons_cons a hm) (by simp only [List.length_cons]; omega)

lemma homTotal_bracket_supportedOn_lower (f : Hom (complex E) (complex D))
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) : homTotal f (bracket l) ∈ supportedOn S := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
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
        rw [← homTotal_boundary, boundary_bracket hl, ← faces_bracket]
        change (homTotal f).toAddMonoidHom (faces bracket (a::b::l)) ∈ _
        rw [faces_hom]
        apply faces_mem_submodule_length
        intro m hm hmlen
        exact ih m.length (by simp only [List.length_cons] at hmlen hlen; omega)
          m (hl.sublist hm) (fun a ha => hs a (hm.subset ha)) rfl

lemma chains_eq_sum_bracket (c : Chains E) :
    c = c.sum (fun w z => z • bracket w.val) := by
  classical
  rw [Finsupp.sum]
  conv_lhs => rw [← Finsupp.sum_single c]
  apply Finset.sum_congr rfl
  intro w _
  rw [bracket_of_pairwise w.property]
  simp

lemma append_positive (a : E) {c : Chains E} (hc : Positive c) : Positive (append a c) :=
  linearCombination_positive _ (fun _ => bracket_positive _) hc

lemma append_mem_grade (a : E) {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    append a c ∈ grade (k+1) := by
  apply linearCombination_mem_grade _ k (k+1) _ hc
  intro w hw
  simpa only [List.length_append,List.length_singleton,hw] using
    bracket_mem_grade (w.val++[a])

lemma append_mem_supportedOn {S : Set E} {a : E} (ha : a ∈ S)
    {c : Chains E} (hc : c ∈ supportedOn S) : append a c ∈ supportedOn S := by
  classical
  rw [append, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  apply bracket_mem_supportedOn
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact (mem_supportedOn_iff S c).mp hc w (Finsupp.mem_support_iff.mp hw) b hb
  · have he : b = a := by simpa using hb
    simpa [he] using ha

lemma append_append_self (a : E) (c : Chains E) : append a (append a c) = 0 := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum, map_sum, map_smul, append_bracket]
  apply Finset.sum_eq_zero
  intro w _
  have hn : ¬(w.val ++ [a] ++ [a]).Pairwise (· < ·) := by
    simp [List.append_assoc, List.pairwise_append]
  rw [bracket_of_not_pairwise hn,smul_zero]

lemma boundary_append_supported (a : E) {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) (hs : c ∈ supportedOn (Set.Iic a)) :
    boundary (append a c) = append a (boundary c) + ((-1 : ℤ)^k) • c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hk := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have hws := (mem_supportedOn_iff _ c).mp hs w (Finsupp.mem_support_iff.mp hw)
  have hp : (w.val ++ [a]).Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    exact ⟨w.property.imp le_of_lt, by simp, by simpa using hws⟩
  rw [append_bracket, boundary_bracket hp, wordBoundary_append, hk,
    boundary_bracket (w.property.imp le_of_lt), smul_add, smul_comm]

def cutWord (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) (l : List E) : Chains D :=
  l.reverseRecOn (bracket []) (fun l a c =>
    if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) c)

@[simp] lemma cutWord_nil (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    cutWord f θ [] = bracket [] := by
  unfold cutWord
  exact List.reverseRecOn_nil _ _

lemma cutWord_append (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (a : E) : cutWord f θ (l++[a]) =
      if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) (cutWord f θ l) :=
  by unfold cutWord; rw [List.reverseRecOn_concat]

lemma cutWord_of_all_zero (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (h : ∀ a ∈ l, θ a = 0) : cutWord f θ l = homTotal f (bracket l) := by
  cases l using List.reverseRecOn with
  | nil => rw [cutWord_nil, homTotal_bracket]; rfl
  | append_singleton l a => rw [cutWord_append, ite_eq_left (h a (by simp))]

lemma cutWord_positive (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) : Positive (cutWord f θ l) := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_positive []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_positive f (bracket_positive _)
    · exact append_positive _ ih

lemma cutWord_grade (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) : cutWord f θ l ∈ grade l.length := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_grade []
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_grade f (bracket_mem_grade _)
    · simpa only [List.length_append,List.length_singleton] using append_mem_grade _ ih

lemma cutWord_supportedOn_lower (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (S : Set D) (hS : IsLowerSet S) (l : List E) (hl : l.Pairwise (· ≤ ·))
    (hs : ∀ a ∈ l, homVertex f a ∈ S) : cutWord f θ l ∈ supportedOn S := by
  induction l using List.reverseRecOn with
  | nil => rw [cutWord_nil]; exact bracket_mem_supportedOn (by simp)
  | append_singleton l a ih =>
    rw [cutWord_append]
    split
    · exact homTotal_bracket_supportedOn_lower f S hS _ hl hs
    · exact append_mem_supportedOn (hs a (by simp))
        (ih (List.pairwise_append.mp hl).1 (fun b hb => hs b (List.mem_append_left _ hb)))

lemma cutWord_boundary (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    boundary (cutWord f θ l) = faces (cutWord f θ) l := by
  induction l using List.reverseRecOn with
  | nil => simp [boundary_bracket]
  | append_singleton l a ih =>
    rw [cutWord_append]
    by_cases hθ : θ a = 0
    · rw [ite_eq_left hθ, ← homTotal_boundary, boundary_bracket hl, ← faces_bracket]
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
            homVertex_monotone f ((List.pairwise_append.mp hl).2.2 b hb a (by simp)))),
        ih (List.pairwise_append.mp hl).1, faces_append_singleton]
      congr 1
      change (append (homVertex f a)).toAddMonoidHom (faces (cutWord f θ) l) = _
      rw [faces_hom]
      apply faces_congr
      intro m _
      rw [cutWord_append,ite_eq_right hθ]
      rfl

lemma cutWord_eq_zero_of_not_pairwise (f : Hom (complex E) (complex D))
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

def cutTotal (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    Chains E →ₗ[ℤ] Chains D := Finsupp.linearCombination ℤ (fun w => cutWord f θ w.val)

lemma cutTotal_bracket (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) : cutTotal f θ (bracket l) = cutWord f θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single,one_smul]
  · rw [bracket_of_not_pairwise hs,map_zero,cutWord_eq_zero_of_not_pairwise f θ l hl hs]

lemma cutTotal_grade (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    {k : ℕ} {c : Chains E} (hc : c ∈ grade k) : cutTotal f θ c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [← hw] using cutWord_grade f θ w.val

lemma cutTotal_positive (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    {c : Chains E} (hc : Positive c) : Positive (cutTotal f θ c) :=
  linearCombination_positive _ (fun w => cutWord_positive f θ w.val) hc

lemma cutTotal_wordBoundary (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    cutTotal f θ (wordBoundary l) = faces (cutWord f θ) l := by
  rw [← faces_bracket]
  change (cutTotal f θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact cutTotal_bracket f θ m (hl.sublist hm)

lemma cutTotal_boundary (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (c : Chains E) : cutTotal f θ (boundary c) = boundary (cutTotal f θ c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [boundary_bracket (w.property.imp le_of_lt),
    cutTotal_bracket f θ w.val (w.property.imp le_of_lt),
    cutWord_boundary f θ w.val (w.property.imp le_of_lt),
    cutTotal_wordBoundary f θ w.val (w.property.imp le_of_lt)]

lemma cutTotal_empty (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    cutTotal f θ (bracket []) = bracket [] := by
  rw [cutTotal_bracket f θ [] (by simp),cutWord_nil]

lemma cutTotal_augmentation (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    {c : Chains E} (hc : c ∈ grade 1) :
    emptyCoefficient (boundary (cutTotal f θ c)) = emptyCoefficient (boundary c) := by
  rw [← cutTotal_boundary, grade_zero_eq_empty (boundary_mem_grade hc), map_smul,
    cutTotal_empty]
  simp only [map_smul,emptyCoefficient_bracket,smul_eq_mul]

def cutHom (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    Hom (complex E) (complex D) where
  map _p :=
    { toFun := fun c => ⟨cutTotal f θ c.val, cutTotal_grade f θ c.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.val y.val) }
  map_d _ x := Subtype.ext (cutTotal_boundary f θ x.val)
  map_augmentation x := cutTotal_augmentation f θ x.property
  map_positive _ _ hc := cutTotal_positive f θ hc

variable {B : Type w} [PartialOrder B]

lemma homTotal_comp (f : Hom (complex E) (complex D)) (g : Hom (complex D) (complex B))
    (c : Chains E) : homTotal (Hom.comp f g) c = homTotal g (homTotal f c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  obtain ⟨l,hl⟩ := w
  cases l with
  | nil => simp only [homTotal_bracket,homWord]
  | cons a l =>
    rw [homTotal_map (Hom.comp f g) l.length ⟨bracket (a::l),bracket_mem_grade _⟩,
      homTotal_map f l.length ⟨bracket (a::l),bracket_mem_grade _⟩,
      homTotal_map g l.length (f.map l.length ⟨bracket (a::l),bracket_mem_grade _⟩)]
    rfl

lemma homTotal_complexMap (a : E →o D) (c : Chains E) :
    homTotal (complexMap a) c = map a c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  obtain ⟨l,hl⟩ := w
  cases l with
  | nil => rw [homTotal_bracket,map_bracket a (by simp)]; rfl
  | cons b l =>
    rw [homTotal_map (complexMap a) l.length ⟨bracket (b::l),bracket_mem_grade _⟩]
    rfl

lemma homVertex_complexMap (a : E →o D) (b : E) : homVertex (complexMap a) b = a b := by
  apply bracket_singleton_injective
  change bracket [homVertex (complexMap a) b] = bracket [a b]
  rw [← homTotal_vertex,homTotal_complexMap,map_bracket a (by simp)]
  rfl

lemma homVertex_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (b : B) :
    homVertex (Hom.comp (complexMap a) f) b = homVertex f (a b) := by
  apply bracket_singleton_injective
  change bracket [homVertex (Hom.comp (complexMap a) f) b] = bracket [homVertex f (a b)]
  rw [← homTotal_vertex,homTotal_comp,homTotal_complexMap,map_bracket a (by simp)]
  exact homTotal_vertex f (a b)

lemma cutWord_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (l : List B) (hl : l.Pairwise (· ≤ ·)) :
    cutWord (Hom.comp (complexMap a) f) (θ.comp a) l = cutWord f θ (l.map a) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [List.map_append,List.map_singleton,cutWord_append,cutWord_append]
    change (if θ (a b) = 0 then _ else _) = (if θ (a b) = 0 then _ else _)
    split
    · rw [homTotal_comp,homTotal_complexMap,map_bracket a hl,List.map_append,List.map_singleton]
    · rw [homVertex_precomp,ih (List.pairwise_append.mp hl).1]

lemma cutTotal_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (θ : E →o Fin 2)
    (c : Chains B) :
    cutTotal (Hom.comp (complexMap a) f) (θ.comp a) c = cutTotal f θ (map a c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),
    map_bracket a (w.property.imp le_of_lt),
    cutTotal_bracket _ _ (w.val.map a)
      (List.pairwise_map.mpr (w.property.imp (fun h => a.monotone h.le)))]
  exact cutWord_precomp a f θ w.val (w.property.imp le_of_lt)

lemma cutHom_precomp (a : B →o E) (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    cutHom (Hom.comp (complexMap a) f) (θ.comp a) = Hom.comp (complexMap a) (cutHom f θ) := by
  ext p x
  exact Subtype.ext (cutTotal_precomp a f θ x.val)

lemma cutWord_const_one (f : Hom (complex E) (complex D)) (l : List E) :
    cutWord f (OrderHom.const E (1 : Fin 2)) l = bracket (l.map (homVertex f)) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [cutWord_append,ite_eq_right (by change (1 : Fin 2) ≠ 0; decide),ih,append_bracket,
      List.map_append,List.map_singleton]

lemma cutTotal_const_zero (f : Hom (complex E) (complex D)) (c : Chains E) :
    cutTotal f (OrderHom.const E (0 : Fin 2)) c = homTotal f c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt)]
  exact cutWord_of_all_zero f _ w.val (by simp)

lemma cutTotal_const_one (f : Hom (complex E) (complex D)) (c : Chains E) :
    cutTotal f (OrderHom.const E (1 : Fin 2)) c = map (homVertexOrderHom f) c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),cutWord_const_one,
    map_bracket (homVertexOrderHom f) (w.property.imp le_of_lt)]
  rfl

lemma cutHom_const_zero (f : Hom (complex E) (complex D)) :
    cutHom f (OrderHom.const E (0 : Fin 2)) = f := by
  ext p c
  apply Subtype.ext
  exact (cutTotal_const_zero f c.val).trans (homTotal_map f p c)

lemma cutHom_const_one (f : Hom (complex E) (complex D)) :
    cutHom f (OrderHom.const E (1 : Fin 2)) = complexMap (homVertexOrderHom f) := by
  ext p c
  exact Subtype.ext (cutTotal_const_one f c.val)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains

noncomputable def tableNerveVertexMap (P : Type u) [PartialOrder P] :
    streetNerve (complex P).nu ⟶ nerve P where
  app m := ↾fun F => (homVertexOrderHom (orientalChain m.unop.len F)).monotone.functor
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro F
    apply nerve.ext_of_isThin
    funext i
    change homVertex (orientalChain n.unop.len
      (OmegaCategory.Functor.comp (complexMap a.unop.toOrderHom).nu F)) i =
        homVertex (orientalChain m.unop.len F) (a.unop.toOrderHom i)
    erw [orientalChain_natural,homVertex_precomp]

lemma posetTableNerveMap_vertex (P : Type u) [PartialOrder P] :
    posetTableNerveMap P ≫ tableNerveVertexMap P = 𝟙 (nerve P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change homVertex (orientalChain m.unop.len (complexMap (posetSimplexOrder s)).nu) i = s.obj i
  rw [orientalChain_of_nu,homVertex_complexMap]
  rfl

noncomputable def tableNerveCutSimplex (P : Type u) [PartialOrder P] (m : ℕ)
    (F : OmegaCategory.Functor (Oriental m) (complex P).nu)
    (θ : Fin (m+1) →o Fin 2) : OmegaCategory.Functor (Oriental m) (complex P).nu :=
  (cutHom (orientalChain m F) θ).nu

lemma tableNerveCutSimplex_natural (P : Type u) [PartialOrder P] {m n : ℕ}
    (a : Fin (m+1) →o Fin (n+1))
    (F : OmegaCategory.Functor (Oriental n) (complex P).nu) (θ : Fin (n+1) →o Fin 2) :
    tableNerveCutSimplex P m (OmegaCategory.Functor.comp (complexMap a).nu F) (θ.comp a) =
      OmegaCategory.Functor.comp (complexMap a).nu (tableNerveCutSimplex P n F θ) := by
  unfold tableNerveCutSimplex
  rw [orientalChain_natural,cutHom_precomp]
  rfl

noncomputable def tableNerveCutCylinder (P : Type u) [PartialOrder P] :
    streetNerve (complex P).nu ⊗ Δ[1] ⟶ streetNerve (complex P).nu where
  app m := ↾fun z => tableNerveCutSimplex P m.unop.len z.1
    (SSet.stdSimplex.objEquiv z.2).toOrderHom
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro z
    exact tableNerveCutSimplex_natural P a.unop.toOrderHom z.1
      (SSet.stdSimplex.objEquiv z.2).toOrderHom

noncomputable def tableNerveCutHomotopy (P : Type u) [PartialOrder P] :
    SSet.Homotopy (𝟙 (streetNerve (complex P).nu))
      (tableNerveVertexMap P ≫ posetTableNerveMap P) where
  h := tableNerveCutCylinder P
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    change (cutHom (orientalChain m.unop.len F) (OrderHom.const _ (0 : Fin 2))).nu = F
    rw [cutHom_const_zero]
    exact orientalChain_nu _ F
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    change (cutHom (orientalChain m.unop.len F) (OrderHom.const _ (1 : Fin 2))).nu =
      (complexMap (homVertexOrderHom (orientalChain m.unop.len F))).nu
    rw [cutHom_const_one]
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma tableNerveVertexMap_weakEquivalence (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (tableNerveVertexMap P) :=
  simplicialWeakEquivalence_of_simplicial_retract _ (posetTableNerveMap P)
    (posetTableNerveMap_vertex P) (tableNerveCutHomotopy P)

lemma posetTableNerveMap_weakEquivalence (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (posetTableNerveMap P) := by
  apply simplicialWeakEquivalences.of_postcomp _ (tableNerveVertexMap P)
    (tableNerveVertexMap_weakEquivalence P)
  rw [posetTableNerveMap_vertex]
  exact simplicialWeakEquivalences.id_mem _

lemma posetCategorificationUnit_tableMap (P : Type u) [PartialOrder P] :
    categorificationAdjunction.unit.app (nerve P) ≫
      streetNerveMap (posetCategorificationTableMap P) = posetTableNerveMap P := by
  exact (categorificationAdjunction.homEquiv _ _).apply_symm_apply (posetTableNerveMap P)

theorem posetCategorificationUnit_weakEquivalence (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (categorificationAdjunction.unit.app (nerve P)) := by
  have : IsIso (streetNerveMap (posetCategorificationTableMap P)) := by
    change IsIso (streetNerveFunctor.map (posetCategorificationTableMap P))
    infer_instance
  apply simplicialWeakEquivalences.of_postcomp _ (streetNerveMap (posetCategorificationTableMap P))
    (simplicialWeakEquivalences.of_isIso _)
  erw [posetCategorificationUnit_tableMap]
  exact posetTableNerveMap_weakEquivalence P

end Thomason

end

end OAI
