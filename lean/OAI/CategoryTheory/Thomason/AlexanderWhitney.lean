import Mathlib
import OAI.CategoryTheory.Thomason.ModelClasses

namespace OAI

/-! Alexander Whitney. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma awZeroWord_map (θ : E →o Fin 2) (f : D →o E) {l : List D}
    (h : l.Pairwise (· ≤ ·)) :
    awZeroWord θ (l.map f) = map f (awZeroWord (θ.comp f) l) := by
  have he : (∀ a ∈ l.map f, θ a = 0) ↔ (∀ a ∈ l, (θ.comp f) a = 0) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      OrderHom.comp_coe, Function.comp_apply]
  unfold awZeroWord
  simp only [he]
  split
  · exact (map_bracket f h).symm
  · exact (map_zero _).symm

lemma awEdgeWord_map (θ : E →o Fin 2) (f : D →o E) {l : List D}
    (h : l.Pairwise (· ≤ ·)) :
    awEdgeWord θ (l.map f) = map f (awEdgeWord (θ.comp f) l) := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a =>
    rw [List.map_append, List.map_singleton, awEdgeWord_append, awEdgeWord_append]
    change (if θ (f a) = 0 then 0 else awZeroWord θ (l.map f)) =
      map f (if θ (f a) = 0 then 0 else awZeroWord (θ.comp f) l)
    split
    · exact (map_zero _).symm
    · exact awZeroWord_map θ f (List.pairwise_append.mp h).1

lemma awZero_map (θ : E →o Fin 2) (f : D →o E) (c : Chains D) :
    awZero θ (map f c) = map f (awZero (θ.comp f) c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    rw [map_bracket f (l.property.imp fun h => le_of_lt h), awZero_bracket,
      awZero_bracket, awZeroWord_map θ f (l.property.imp fun h => le_of_lt h)]

lemma awEdge_map (θ : E →o Fin 2) (f : D →o E) (c : Chains D) :
    awEdge θ (map f c) = map f (awEdge (θ.comp f) c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    have hl := l.property.imp fun h => le_of_lt h
    rw [map_bracket f hl,
      awEdge_bracket θ (List.pairwise_map.mpr (hl.imp fun h => f.monotone h)),
      awEdge_bracket (θ.comp f) hl, awEdgeWord_map θ f hl]

lemma awHom_naturality (θ : E →o Fin 2) (f : D →o E) :
    DirectedComplex.Hom.comp (complexMap f) (awHom θ) =
      DirectedComplex.Hom.comp (awHom (θ.comp f)) (complexMap f).cylinder := by
  ext p c
  cases p with
  | zero =>
    apply Prod.ext <;> apply Subtype.ext
    · exact awZero_map θ f c.val
    · change map f c.val - awZero θ (map f c.val) =
        map f (c.val - awZero (θ.comp f) c.val)
      rw [map_sub, awZero_map]
  | succ p =>
    apply Prod.ext
    · exact Subtype.ext (awZero_map θ f c.val)
    · apply Prod.ext
      · apply Subtype.ext
        change map f c.val - awZero θ (map f c.val) =
          map f (c.val - awZero (θ.comp f) c.val)
        rw [map_sub, awZero_map]
      · exact Subtype.ext (awEdge_map θ f c.val)

lemma awHom_projection (θ : E →o Fin 2) :
    DirectedComplex.Hom.comp (awHom θ) (complex E).cylinderProjection =
      DirectedComplex.Hom.id (complex E) := by
  ext p c
  cases p <;> apply Subtype.ext <;>
    change awZero θ c.val + (c.val - awZero θ c.val) = c.val <;> abel

lemma awZero_const_zero (c : Chains E) :
    awZero (OrderHom.const E (0 : Fin 2)) c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    rw [map_add, ih]
    congr 1
    change Finsupp.linearCombination ℤ _ (Finsupp.single l z) = _
    rw [Finsupp.linearCombination_single, awZeroWord_of_all _ (by simp)]
    rw [bracket_of_pairwise l.property]
    simp

lemma awEdge_const_zero (c : Chains E) :
    awEdge (OrderHom.const E (0 : Fin 2)) c = 0 := by
  classical
  rw [awEdge, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [awEdgeWord_of_all _ (by simp), smul_zero]

lemma awZero_const_one_of_grade {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+1)) :
    awZero (OrderHom.const E (1 : Fin 2)) c = 0 := by
  classical
  rw [awZero, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hl := (mem_grade_iff (p+1) c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have hn : w.val ≠ [] := by intro he; simp [he] at hl
  rw [awZeroWord_of_not_all, smul_zero]
  intro h
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w.val hn
  simpa using h a ha

lemma awEdge_const_one_of_grade {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) :
    awEdge (OrderHom.const E (1 : Fin 2)) c = 0 := by
  classical
  rw [awEdge, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hl := (mem_grade_iff (p+2) c).mp hc w (Finsupp.mem_support_iff.mp hw)
  suffices awEdgeWord (OrderHom.const E (1 : Fin 2)) w.val = 0 by rw [this, smul_zero]
  rcases w with ⟨w, hws⟩
  cases w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l a =>
    rw [awEdgeWord_append]
    change (if (1 : Fin 2) = 0 then 0 else awZeroWord (OrderHom.const E 1) l) = 0
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    apply awZeroWord_of_not_all
    intro h
    have hn : l ≠ [] := by intro he; simp [he] at hl
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil l hn
    simpa using h b hb

lemma awHom_endpoint (b : Bool) :
    awHom (OrderHom.const E (if b then (1 : Fin 2) else 0)) =
      (complex E).cylinderEndpoint b := by
  ext p c
  cases p with
  | zero =>
    cases b <;> apply Prod.ext <;> apply Subtype.ext
    · exact awZero_const_zero c.val
    · change c.val - awZero (OrderHom.const E (0 : Fin 2)) c.val = 0
      rw [awZero_const_zero, sub_self]
    · exact awZero_const_one_of_grade c.property
    · change c.val - awZero (OrderHom.const E (1 : Fin 2)) c.val = c.val
      rw [awZero_const_one_of_grade c.property, sub_zero]
  | succ p =>
    cases b
    · apply Prod.ext
      · exact Subtype.ext (awZero_const_zero c.val)
      · apply Prod.ext <;> apply Subtype.ext
        · change c.val - awZero (OrderHom.const E (0 : Fin 2)) c.val = 0
          rw [awZero_const_zero, sub_self]
        · exact awEdge_const_zero c.val
    · apply Prod.ext
      · exact Subtype.ext (awZero_const_one_of_grade c.property)
      · apply Prod.ext <;> apply Subtype.ext
        · change c.val - awZero (OrderHom.const E (1 : Fin 2)) c.val = c.val
          rw [awZero_const_one_of_grade c.property, sub_zero]
        · exact awEdge_const_one_of_grade c.property

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def supportedOn (S : Set E) : Submodule ℤ (Chains E) :=
  Finsupp.supported ℤ ℤ {w : Word E | ∀ a ∈ w.val, a ∈ S}

lemma mem_supportedOn_iff (S : Set E) (c : Chains E) :
    c ∈ supportedOn S ↔ ∀ w, c w ≠ 0 → ∀ a ∈ w.val, a ∈ S := by
  simp only [supportedOn, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff,
    Finset.mem_coe, Set.mem_ofPred_eq]

lemma bracket_mem_supportedOn {S : Set E} {l : List E}
    (h : ∀ a ∈ l, a ∈ S) : bracket l ∈ supportedOn S := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    exact Finsupp.single_mem_supported ℤ 1 h
  · rw [bracket_of_not_pairwise hs]
    exact Submodule.zero_mem _

lemma faces_mem_submodule {D : Type v} (Q : Submodule ℤ (Chains E))
    (H : List D → Chains E) (l : List D)
    (hH : ∀ m, m.Sublist l → H m ∈ Q) : faces H l ∈ Q := by
  induction l generalizing H with
  | nil => exact Q.zero_mem
  | cons a l ih =>
    rw [faces_cons]
    apply Q.sub_mem
    · exact hH l (List.sublist_cons_self a l)
    · apply ih
      intro m hm
      exact hH (a :: m) (List.Sublist.cons_cons a hm)

lemma wordBoundary_mem_supportedOn {S : Set E} {l : List E}
    (h : ∀ a ∈ l, a ∈ S) : wordBoundary l ∈ supportedOn S := by
  rw [← faces_bracket]
  apply faces_mem_submodule
  intro m hm
  exact bracket_mem_supportedOn (fun a ha => h a (hm.subset ha))

lemma boundary_mem_supportedOn {S : Set E} {c : Chains E} (hc : c ∈ supportedOn S) :
    boundary c ∈ supportedOn S := by
  classical
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordBoundary_mem_supportedOn ((mem_supportedOn_iff S c).mp hc w
    (Finsupp.mem_support_iff.mp hw))

lemma bracket_apply [DecidableEq E] (l : List E) (w : Word E) :
    bracket l w = if l = w.val then 1 else 0 := by
  classical
  by_cases he : l = w.val
  · subst l
    rw [bracket_of_pairwise w.property]
    simp
  · by_cases hs : l.Pairwise (· < ·)
    · rw [bracket_of_pairwise hs]
      have hn : (⟨l, hs⟩ : Word E) ≠ w := fun h => he (congrArg Subtype.val h)
      simp [he, hn]
    · simp [bracket_of_not_pairwise hs, he]

lemma prepend_apply_zero (a : E) (c : Chains E) (w : Word E)
    (h : ∀ l : List E, a :: l ≠ w.val) : prepend a c w = 0 := by
  classical
  rw [prepend, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum]
  apply Finset.sum_eq_zero
  intro t _
  simp only [Finsupp.smul_apply, smul_eq_mul, bracket_apply, ite_eq_right (h t.val), mul_zero]

def tailWord (w : Word E) : Word E := ⟨w.val.tail, w.property.tail⟩

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [LinearOrder E]

lemma wordBoundary_leading {a b : E} {l : List E} (h : (a :: b :: l).Pairwise (· < ·))
    (t : Word E) (ht : b :: l ≤ t.val) :
    wordBoundary (a :: b :: l) t = if (b :: l) = t.val then 1 else 0 := by
  have hz : prepend a (wordBoundary (b :: l)) t = 0 := by
    apply prepend_apply_zero
    intro q hq
    have hab : a < b := (List.pairwise_cons.mp h).1 b (by simp)
    have hlt : a :: q < b :: l := List.Lex.rel hab
    exact (not_lt_of_ge ht) (hq ▸ hlt)
  rw [wordBoundary_cons, Finsupp.sub_apply, hz, sub_zero, bracket_apply]

lemma wordBoundary_leading' (w t : Word E) (hn : 2 ≤ w.val.length)
    (ht : tailWord w ≤ t) :
    wordBoundary w.val t = if tailWord w = t then 1 else 0 := by
  rcases w with ⟨w, hw⟩
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b l =>
      rw [wordBoundary_leading hw t ht]
      congr 1
      exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

lemma tailWord_not_supported {S : Set E} (hS : IsLowerSet S) (w : Word E)
    (hn : 2 ≤ w.val.length) (hw : ¬∀ a ∈ w.val, a ∈ S) :
    ¬∀ a ∈ (tailWord w).val, a ∈ S := by
  rcases w with ⟨w, hp⟩
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b l =>
      intro h
      apply hw
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · apply hS (le_of_lt ((List.pairwise_cons.mp hp).1 b (by simp)))
        exact h b (by simp [tailWord])
      · exact h c (by simpa only [tailWord, List.tail_cons, List.mem_cons] using hc)

lemma positive_supportedOn_of_boundary {S : Set E} (hS : IsLowerSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  classical
  rw [mem_supportedOn_iff]
  by_contra hn
  push Not at hn
  obtain ⟨w, hw, a, ha, hna⟩ := hn
  let T := c.support.filter (fun t => ¬∀ b ∈ t.val, b ∈ S)
  have hwT : w ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hw, fun h => hna (h a ha)⟩
  have hT : (T.image tailWord).Nonempty := (show T.Nonempty from ⟨w, hwT⟩).image tailWord
  let t : Word E := (T.image tailWord).max' hT
  have htmem : t ∈ T.image tailWord := Finset.max'_mem _ _
  obtain ⟨w₀, hw₀, hwt⟩ := Finset.mem_image.mp htmem
  have hw₀c : c w₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hw₀).1
  have hw₀len : w₀.val.length = p+2 := (mem_grade_iff (p+2) c).mp hc w₀ hw₀c
  have htS : ¬∀ b ∈ t.val, b ∈ S := by
    rw [← hwt]
    exact tailWord_not_supported hS w₀ (by omega) (Finset.mem_filter.mp hw₀).2
  have hmax : ∀ s ∈ T, tailWord s ≤ t := by
    intro s hs
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hcoef : ∀ s ∈ c.support, 0 ≤ wordBoundary s.val t := by
    intro s hs
    by_cases hsin : ∀ b ∈ s.val, b ∈ S
    · have hbd := wordBoundary_mem_supportedOn hsin
      have he : wordBoundary s.val t = 0 := by
        by_contra he
        exact htS ((mem_supportedOn_iff S _).mp hbd t he)
      rw [he]
    · have hlen := (mem_grade_iff (p+2) c).mp hc s (Finsupp.mem_support_iff.mp hs)
      rw [wordBoundary_leading' s t (by omega) (hmax s (Finset.mem_filter.mpr ⟨hs, hsin⟩))]
      split <;> omega
  have hpos : 0 < (boundary c) t := by
    rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_pos'
    · intro s hs
      exact mul_nonneg (hp s) (hcoef s hs)
    · refine ⟨w₀, (Finset.mem_filter.mp hw₀).1, ?_⟩
      rw [wordBoundary_leading' w₀ t (by omega) (hmax w₀ hw₀), ite_eq_left hwt, mul_one]
      exact lt_of_le_of_ne (hp w₀) (Ne.symm hw₀c)
  exact htS ((mem_supportedOn_iff S _).mp hd t (ne_of_gt hpos))

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def subsetWordEmbedding (S : Set E) : Word S ↪ Word E :=
  wordEmbedding (OrderEmbedding.subtype S)

lemma mem_range_subsetWordEmbedding (S : Set E) (w : Word E)
    (h : ∀ a ∈ w.val, a ∈ S) : w ∈ Set.range (subsetWordEmbedding S) := by
  let l : List S := w.val.attach.map (fun a => ⟨a.val, h a.val a.property⟩)
  have hl : l.map Subtype.val = w.val := by simp [l, List.map_map]
  have hp : l.Pairwise (· < ·) := by
    have hh := hl ▸ w.property
    change l.Pairwise (fun a b : S => a.val < b.val)
    exact List.pairwise_map.mp hh
  refine ⟨⟨l, hp⟩, ?_⟩
  exact Subtype.ext hl

def restrictChain (S : Set E) : Chains E →ₗ[ℤ] Chains S :=
  Finsupp.lcomapDomain (subsetWordEmbedding S) (subsetWordEmbedding S).injective

@[simp] lemma restrictChain_apply (S : Set E) (c : Chains E) (w : Word S) :
    restrictChain S c w = c (subsetWordEmbedding S w) := rfl

lemma map_restrictChain (S : Set E) {c : Chains E} (hc : c ∈ supportedOn S) :
    map (OrderEmbedding.subtype S).toOrderHom (restrictChain S c) = c := by
  rw [map_orderEmbedding]
  apply Finsupp.mapDomain_comapDomain (subsetWordEmbedding S)
    (subsetWordEmbedding S).injective c
  intro w hw
  exact mem_range_subsetWordEmbedding S w ((mem_supportedOn_iff S c).mp hc w
    (Finsupp.mem_support_iff.mp hw))

lemma restrictChain_mem_grade (S : Set E) {p : ℕ} {c : Chains E}
    (hc : c ∈ grade p) : restrictChain S c ∈ grade p := by
  rw [mem_grade_iff]
  intro w hw
  have h := (mem_grade_iff p c).mp hc (subsetWordEmbedding S w) hw
  change (w.val.map Subtype.val).length = p at h
  simpa only [List.length_map] using h

lemma restrictChain_positive (S : Set E) {c : Chains E} (hc : Positive c) :
    Positive (restrictChain S c) := fun w => hc (subsetWordEmbedding S w)

lemma map_mem_supportedOn (S : Set E) (c : Chains S) :
    map (OrderEmbedding.subtype S).toOrderHom c ∈ supportedOn S := by
  classical
  rw [map_orderEmbedding, mem_supportedOn_iff]
  intro w hw
  have hr : w ∈ Set.range (subsetWordEmbedding S) := by
    by_contra hr
    exact hw (Finsupp.mapDomain_of_notMem_range c w hr)
  obtain ⟨s, rfl⟩ := hr
  intro a ha
  obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
  exact hb ▸ b.property

def restrictGrade (S : Set E) (p : ℕ) :
    (complex E).Chain p →+ (complex S).Chain p where
  toFun c := ⟨restrictChain S c.val, restrictChain_mem_grade S c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

lemma complexMap_restrictGrade (S : Set E) (p : ℕ) (c : (complex E).Chain p)
    (hc : c.val ∈ supportedOn S) :
    (complexMap (OrderEmbedding.subtype S).toOrderHom).map p (restrictGrade S p c) = c :=
  Subtype.ext (map_restrictChain S hc)

open DirectedComplex

def restrictTable (S : Set E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) : Table (complex S) where
  row p b := restrictGrade S p (x.row p b)
  positive p b := restrictChain_positive S (x.positive p b)
  boundary p b := by
    apply complexMap_orderEmbedding_injective (OrderEmbedding.subtype S) p
    rw [(complexMap (OrderEmbedding.subtype S).toOrderHom).map_d p
        (restrictGrade S (p+1) (x.row (p+1) b)),
      complexMap_restrictGrade S (p+1) _ (hx (p+1) b), x.boundary, map_sub,
      complexMap_restrictGrade S p _ (hx p true),
      complexMap_restrictGrade S p _ (hx p false)]
  augmentation b := by
    rw [← (complexMap (OrderEmbedding.subtype S).toOrderHom).map_augmentation,
      complexMap_restrictGrade S 0 _ (hx 0 b)]
    exact x.augmentation b
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k, fun p hp b => ?_⟩
    rw [hk p hp b, map_zero]

lemma table_map_restrictTable (S : Set E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) :
    (complexMap (OrderEmbedding.subtype S).toOrderHom).table (restrictTable S x hx) = x := by
  ext p b
  exact complexMap_restrictGrade S p _ (hx p b)

lemma table_map_orderEmbedding_injective {D : Type v} [PartialOrder D] (f : E ↪o D) :
    Function.Injective (complexMap f.toOrderHom).table := by
  intro x y h
  ext p b
  apply complexMap_orderEmbedding_injective f p
  exact congrArg (fun z => z.row p b) h

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [LinearOrder E]
open DirectedComplex

lemma table_supportedOn_lower {S : Set E} (hS : IsLowerSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary hS (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

lemma table_initial_segment_unique_lift {S : Set E} (hS : IsLowerSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∃! y : Table (complex S),
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table y = x := by
  refine ⟨restrictTable S x (table_supportedOn_lower hS x hx),
    table_map_restrictTable S x _, ?_⟩
  intro y hy
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S)
  exact hy.trans (table_map_restrictTable S x _).symm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def reverseWord : Word E ≃ Word Eᵒᵈ where
  toFun w := ⟨w.val.reverse, List.pairwise_reverse.mpr w.property⟩
  invFun w := ⟨w.val.reverse, List.pairwise_reverse.mpr w.property⟩
  left_inv w := Subtype.ext (List.reverse_reverse w.val)
  right_inv w := Subtype.ext (List.reverse_reverse w.val)

def reverseChain : Chains E ≃ₗ[ℤ] Chains Eᵒᵈ := Finsupp.domLCongr reverseWord

@[simp] lemma reverseChain_apply (c : Chains E) (w : Word Eᵒᵈ) :
    reverseChain c w = c (reverseWord.symm w) := rfl

lemma reverseChain_bracket (l : List E) :
    reverseChain (bracket l) = bracket (E := Eᵒᵈ) l.reverse := by
  classical
  by_cases hp : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hp]
    change Finsupp.domLCongr reverseWord (Finsupp.single ⟨l,hp⟩ 1) = _
    rw [Finsupp.domLCongr_single]
    exact (bracket_of_pairwise (List.pairwise_reverse.mpr hp)).symm
  · have hr : ¬l.reverse.Pairwise (fun a b : Eᵒᵈ => a < b) := by
      intro hr
      exact hp (List.pairwise_reverse.mp
        (show l.reverse.Pairwise (fun a b : E => b < a) from hr))
    simp only [bracket_of_not_pairwise hp, bracket_of_not_pairwise hr, map_zero]

lemma reverseChain_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    reverseChain c ∈ grade k := by
  rw [mem_grade_iff]
  intro w hw
  have h := (mem_grade_iff k c).mp hc (reverseWord.symm w) hw
  change w.val.reverse.length = k at h
  simpa only [List.length_reverse] using h

lemma reverseChain_positive {c : Chains E} (hc : Positive c) :
    Positive (reverseChain c) := fun w => hc (reverseWord.symm w)

lemma reverseChain_supportedOn {S : Set E} {c : Chains E}
    (hc : c ∈ supportedOn S) : reverseChain c ∈ supportedOn (E := Eᵒᵈ) S := by
  apply (mem_supportedOn_iff (E := Eᵒᵈ) S (reverseChain c)).mpr
  intro w hw a ha
  apply (mem_supportedOn_iff S c).mp hc (reverseWord.symm w) hw a
  exact List.mem_reverse.mpr ha

lemma supportedOn_of_reverseChain {S : Set E} {c : Chains E}
    (hc : reverseChain c ∈ supportedOn (E := Eᵒᵈ) S) : c ∈ supportedOn S := by
  rw [mem_supportedOn_iff]
  intro w hw a ha
  have hz : reverseChain c (reverseWord w) ≠ 0 := by simpa using hw
  apply (mem_supportedOn_iff (E := Eᵒᵈ) S _).mp hc (reverseWord w) hz a
  exact List.mem_reverse.mpr ha

section
omit [PartialOrder E]
variable {M : Type v} [AddCommGroup M]

lemma faces_reverse (H : List E → M) (l : List E) :
    faces H l.reverse = -((-1 : ℤ)^l.length) • faces (fun m => H m.reverse) l := by
  induction l generalizing H with
  | nil => simp
  | cons a l ih =>
    rw [List.reverse_cons, faces_append_singleton, ih]
    simp only [List.length_reverse, List.length_cons, pow_succ, mul_neg, mul_one,
      neg_neg, faces_cons, List.reverse_cons, smul_sub, neg_smul]
    abel

end

lemma wordBoundary_reverse (l : List E) :
    wordBoundary (E := Eᵒᵈ) l.reverse =
      -((-1 : ℤ)^l.length) • reverseChain (wordBoundary l) := by
  calc
    _ = faces (fun m : List E => bracket (E := Eᵒᵈ) m) l.reverse :=
      (faces_bracket (E := Eᵒᵈ) l.reverse).symm
    _ = -((-1 : ℤ)^l.length) •
        faces (fun m => bracket (E := Eᵒᵈ) m.reverse) l := faces_reverse _ l
    _ = _ := by
      congr 1
      have h := faces_hom reverseChain.toAddMonoidHom bracket l
      change reverseChain (faces bracket l) =
        faces (fun m => reverseChain (bracket m)) l at h
      simp only [reverseChain_bracket, faces_bracket] at h
      exact h.symm

lemma boundary_reverseChain {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    boundary (reverseChain c) = -((-1 : ℤ)^k) • reverseChain (boundary c) := by
  classical
  have he : c = c.sum (fun w z => z • bracket w.val) := by
    rw [Finsupp.sum]
    conv_lhs => rw [← Finsupp.sum_single c]
    apply Finset.sum_congr rfl
    intro w _
    rw [bracket_of_pairwise w.property]
    simp
  rw [he]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hk := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have hb := boundary_bracket (E := Eᵒᵈ) (l := w.val.reverse)
    (List.pairwise_reverse.mpr (w.property.imp le_of_lt))
  rw [reverseChain_bracket, hb, wordBoundary_reverse w.val, hk,
    boundary_bracket (w.property.imp le_of_lt), smul_comm]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [LinearOrder E]

lemma positive_supportedOn_of_boundary_upper {S : Set E} (hS : IsUpperSet S)
    {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2)) (hp : Positive c)
    (hd : boundary c ∈ supportedOn S) : c ∈ supportedOn S := by
  apply supportedOn_of_reverseChain
  apply positive_supportedOn_of_boundary (E := Eᵒᵈ) hS
    (reverseChain_mem_grade hc) (reverseChain_positive hp)
  rw [boundary_reverseChain hc]
  exact (supportedOn (E := Eᵒᵈ) S).smul_mem _ (reverseChain_supportedOn hd)

open DirectedComplex

lemma table_supportedOn_upper {S : Set E} (hS : IsUpperSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  intro p
  induction p with
  | zero => exact hx
  | succ p ih =>
    intro b
    apply positive_supportedOn_of_boundary_upper hS
      (x.row (p+1) b).property (x.positive _ _)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [hb]
    exact (supportedOn S).sub_mem (ih true) (ih false)

lemma table_final_segment_unique_lift {S : Set E} (hS : IsUpperSet S)
    (x : Table (complex E)) (hx : ∀ b, (x.row 0 b).val ∈ supportedOn S) :
    ∃! y : Table (complex S),
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table y = x := by
  refine ⟨restrictTable S x (table_supportedOn_upper hS x hx),
    table_map_restrictTable S x _, ?_⟩
  intro y hy
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S)
  exact hy.trans (table_map_restrictTable S x _).symm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma augmentation_eq_sum {c : Chains E} (hc : c ∈ grade 1) :
    emptyCoefficient (boundary c) = c.sum (fun _ z => z) := by
  classical
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hlen := (mem_grade_iff 1 c).mp hc w (Finsupp.mem_support_iff.mp hw)
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  rw [ha]
  simp [wordBoundary_cons, wordBoundary_nil, emptyCoefficient_bracket]

lemma positive_mass_one {c : Chains E} (hp : Positive c)
    (hc : c.sum (fun _ z => z) = 1) : ∃ w : Word E, c = Finsupp.single w 1 := by
  classical
  have hne : c ≠ 0 := by intro h; simp [h] at hc
  obtain ⟨w, hw⟩ := Finsupp.ne_iff.mp hne
  change c w ≠ 0 at hw
  have hws : w ∈ c.support := Finsupp.mem_support_iff.mpr hw
  have hle : c w ≤ 1 := by
    rw [← hc, Finsupp.sum]
    exact Finset.single_le_sum (fun s _ => hp s) hws
  have hw1 : c w = 1 := by have := hp w; omega
  have he : ∑ s ∈ c.support.erase w, c s = 0 := by
    have h := Finset.sum_erase_add c.support (fun s => c s) hws
    rw [show ∑ s ∈ c.support, c s = 1 from hc, hw1] at h
    omega
  refine ⟨w, ?_⟩
  ext t
  by_cases ht : t = w
  · subst t; simpa using hw1
  · rw [Finsupp.single_eq_of_ne ht]
    by_cases hts : t ∈ c.support
    · have htle := Finset.single_le_sum (s := c.support.erase w)
        (fun s _ => hp s) (Finset.mem_erase.mpr ⟨ht, hts⟩)
      have htn := hp t
      omega
    · exact Finsupp.notMem_support_iff.mp hts

lemma positive_augmentation_one {c : Chains E} (hc : c ∈ grade 1)
    (hp : Positive c) (ha : emptyCoefficient (boundary c) = 1) :
    ∃ a : E, c = bracket [a] := by
  rw [augmentation_eq_sum hc] at ha
  obtain ⟨w, hw⟩ := positive_mass_one hp ha
  have hlen : w.val.length = 1 := by
    apply (mem_grade_iff 1 c).mp hc w
    rw [hw, Finsupp.single_eq_same]
    norm_num
  obtain ⟨a, he⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨a, ?_⟩
  rw [hw, ← he, bracket_of_pairwise w.property]

open DirectedComplex

lemma table_zero_row_vertex (x : Table (complex E)) (b : Bool) :
    ∃ a : E, (x.row 0 b).val = bracket [a] :=
  positive_augmentation_one (x.row 0 b).property (x.positive 0 b) (x.augmentation b)

def vertexTable (a : E) : Table (complex E) where
  row p _ := match p with
    | 0 => ⟨bracket [a], bracket_mem_grade [a]⟩
    | _+1 => 0
  positive p b := by
    cases p with
    | zero =>
      change Positive (bracket [a])
      exact bracket_positive [a]
    | succ p => exact (complex E).positive (p+1) |>.zero_mem
  boundary p b := by
    cases p with
    | zero =>
      apply Subtype.ext
      change boundary 0 = bracket [a] - bracket [a]
      simp
    | succ p => simp only [map_zero, sub_self]
  augmentation b := by
    change emptyCoefficient (boundary (bracket [a])) = 1
    rw [boundary_bracket (by simp)]
    simp [wordBoundary, emptyCoefficient_bracket]
  bounded := ⟨0, by intros p hp b; cases p <;> first | omega | rfl⟩

@[simp] lemma vertexTable_row_zero (a : E) (b : Bool) :
    (vertexTable a).row 0 b =
      (⟨bracket [a], bracket_mem_grade [a]⟩ : (complex E).Chain 0) := by
  rfl

lemma vertexTable_row_pos (a : E) {p : ℕ} (hp : 0 < p) (b : Bool) :
    (vertexTable a).row p b = 0 := by cases p <;> first | omega | rfl

lemma vertexTable_source (a : E) : Table.truncate 0 false (vertexTable a) = vertexTable a := by
  ext p b
  cases p with
  | zero => rfl
  | succ p => simp [vertexTable_row_pos a (by omega : 0 < p+1)]

lemma bracket_singleton_injective : Function.Injective (fun a : E => bracket [a]) := by
  classical
  intro a b h
  have he := congrArg (fun c : Chains E => c ⟨[a], by simp⟩) h
  by_contra hn
  have hl : [b] ≠ [a] := by simpa [eq_comm] using hn
  simp [bracket_apply, hl] at he

def tableObjectsEquiv : (complex E).nu.Objects ≃ E where
  toFun x := Classical.choose (table_zero_row_vertex x.val false)
  invFun a := ⟨vertexTable a, vertexTable_source a⟩
  left_inv x := by
    apply Subtype.ext
    let a := Classical.choose (table_zero_row_vertex x.val false)
    have he : vertexTable a = Table.truncate 0 false x.val := by
      ext p b
      cases p with
      | zero =>
        apply Subtype.ext
        change bracket [a] = (x.val.row 0 false).val
        exact (Classical.choose_spec (table_zero_row_vertex x.val false)).symm
      | succ p =>
        change (vertexTable a).row (p+1) b = 0
        exact vertexTable_row_pos a (by omega) b
    exact he.trans x.property
  right_inv a := by
    apply bracket_singleton_injective
    exact (Classical.choose_spec (table_zero_row_vertex (vertexTable a) false)).symm

end Thomason.NormalizedChains

end

end OAI
