import Mathlib
import OAI.CategoryTheory.Thomason.Definitions

namespace OAI

/-! Normalized Chains. -/

noncomputable section
universe u v w z


namespace Thomason
namespace NormalizedChains

variable {E : Type u} [PartialOrder E]


lemma bracket_of_pairwise {l : List E} (h : l.Pairwise (· < ·)) :
    bracket l = Finsupp.single ⟨l, h⟩ 1 := by
  classical
  simp [bracket, h]

lemma bracket_of_not_pairwise {l : List E} (h : ¬l.Pairwise (· < ·)) :
    bracket l = 0 := by
  classical
  simp [bracket, h]


def append (a : E) : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun l : Word E => bracket (l.val ++ [a]))

@[simp] lemma prepend_bracket (a : E) (l : List E) :
    prepend a (bracket l) = bracket (a :: l) := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ (fun l : Word E => bracket (a :: l.val))
      (Finsupp.single (⟨l, h⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · have h' : ¬(a :: l).Pairwise (· < ·) := fun hw => h hw.tail
    simp [bracket_of_not_pairwise h, bracket_of_not_pairwise h']

@[simp] lemma append_bracket (a : E) (l : List E) :
    append a (bracket l) = bracket (l ++ [a]) := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ (fun l : Word E => bracket (l.val ++ [a]))
      (Finsupp.single (⟨l, h⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · have h' : ¬(l ++ [a]).Pairwise (· < ·) := by
      intro hw
      exact h (List.pairwise_append.mp hw).1
    simp [bracket_of_not_pairwise h, bracket_of_not_pairwise h']

lemma prepend_prepend_self (a : E) (c : Chains E) : prepend a (prepend a c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih, add_zero]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul, prepend_bracket]
    have h : ¬(a :: a :: l.val).Pairwise (· < ·) := by simp
    simp [bracket_of_not_pairwise h]

lemma prepend_append (a b : E) (c : Chains E) :
    prepend a (append b c) = append b (prepend a c) := by
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
    simp only [map_smul, prepend_bracket, append_bracket, List.cons_append]


@[simp] lemma wordBoundary_nil : wordBoundary ([] : List E) = 0 := rfl
@[simp] lemma wordBoundary_cons (a : E) (l : List E) :
    wordBoundary (a :: l) = bracket l - prepend a (wordBoundary l) := rfl


lemma wordBoundary_repeated (a : E) (l : List E) :
    wordBoundary (a :: a :: l) = 0 := by
  simp [wordBoundary, map_sub, prepend_prepend_self]

lemma wordBoundary_eq_zero_of_not_pairwise {l : List E}
    (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : wordBoundary l = 0 := by
  induction l with
  | nil => exact (hn (by simp)).elim
  | cons a l ih =>
    by_cases hl : l.Pairwise (· < ·)
    · cases l with
      | nil => exact (hn (by simp)).elim
      | cons b l =>
        have hab : a ≤ b := (List.pairwise_cons.mp h).1 b (by simp)
        have hab' : ¬a < b := by
          intro hab'
          exact hn (List.Pairwise.cons_cons_of_trans hab' hl)
        have heq : a = b := (lt_or_eq_of_le hab).resolve_left hab'
        subst b
        exact wordBoundary_repeated a l
    · simp [wordBoundary, bracket_of_not_pairwise hl, ih h.tail hl]

lemma boundary_bracket {l : List E} (h : l.Pairwise (· ≤ ·)) :
    boundary (bracket l) = wordBoundary l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E => wordBoundary l.val)
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, wordBoundary_eq_zero_of_not_pairwise h hs]

section AlternatingFaces

omit [PartialOrder E]

variable {M : Type v} [AddCommGroup M]


@[simp] lemma faces_nil (H : List E → M) : faces H [] = 0 := rfl
@[simp] lemma faces_cons (H : List E → M) (a : E) (l : List E) :
    faces H (a :: l) = H l - faces (fun m => H (a :: m)) l := rfl

lemma faces_sub (H K : List E → M) (l : List E) :
    faces (fun m => H m - K m) l = faces H l - faces K l := by
  induction l generalizing H K with
  | nil => simp
  | cons a l ih => simp only [faces_cons, ih]; abel

lemma faces_hom {M' : Type w} [AddCommGroup M'] (q : M →+ M')
    (H : List E → M) (l : List E) :
    q (faces H l) = faces (fun m => q (H m)) l := by
  induction l generalizing H with
  | nil => simp
  | cons a l ih => simp only [faces_cons, map_sub, ih]

lemma faces_congr {H K : List E → M} {l : List E}
    (h : ∀ m, m.Sublist l → H m = K m) : faces H l = faces K l := by
  induction l generalizing H K with
  | nil => rfl
  | cons a l ih =>
    rw [faces_cons, faces_cons, h l (List.sublist_cons_self a l)]
    congr 1
    exact ih (fun m hm => h (a :: m) (List.Sublist.cons_cons a hm))

lemma faces_faces (H : List E → M) (l : List E) :
    faces (faces H) l = 0 := by
  induction l generalizing H with
  | nil => rfl
  | cons a l ih =>
    simp only [faces_cons]
    rw [faces_sub, ih]
    simp

lemma faces_map {D : Type w} (f : D → E) (H : List E → M) (l : List D) :
    faces H (l.map f) = faces (fun m => H (m.map f)) l := by
  induction l generalizing H with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, faces_cons, ih]

lemma faces_append_singleton (H : List E → M) (l : List E) (a : E) :
    faces H (l ++ [a]) = faces (fun m => H (m ++ [a])) l +
      ((-1 : ℤ) ^ l.length) • H l := by
  induction l generalizing H with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, List.length_cons, faces_cons, ih, pow_succ,
      mul_neg, mul_one, neg_smul]
    abel

end AlternatingFaces

lemma faces_bracket (l : List E) : faces bracket l = wordBoundary l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [faces_cons, wordBoundary_cons]
    have h := faces_hom (prepend a).toAddMonoidHom bracket l
    simp only [LinearMap.toAddMonoidHom_coe, prepend_bracket] at h
    rw [← h, ih]

lemma wordBoundary_append (l : List E) (a : E) :
    wordBoundary (l ++ [a]) = append a (wordBoundary l) +
      ((-1 : ℤ) ^ l.length) • bracket l := by
  rw [← faces_bracket, faces_append_singleton]
  have h := faces_hom (append a).toAddMonoidHom bracket l
  simp only [LinearMap.toAddMonoidHom_coe, append_bracket] at h
  rw [← h, faces_bracket]

lemma boundary_wordBoundary {l : List E} (h : l.Pairwise (· ≤ ·)) :
    boundary (wordBoundary l) = 0 := by
  rw [← faces_bracket]
  change boundary.toAddMonoidHom (faces bracket l) = 0
  rw [faces_hom]
  have hc : faces (fun m => boundary (bracket m)) l = faces wordBoundary l := by
    apply faces_congr
    intro m hm
    exact boundary_bracket (h.sublist hm)
  change faces (fun m => boundary (bracket m)) l = 0
  rw [hc]
  change faces (fun m => wordBoundary m) l = 0
  simp_rw [← faces_bracket]
  exact faces_faces bracket l

lemma boundary_boundary (c : Chains E) : boundary (boundary c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih, add_zero]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    rw [boundary_bracket (l.property.imp fun h => le_of_lt h),
      boundary_wordBoundary (l.property.imp fun h => le_of_lt h), smul_zero]

section Functoriality

variable {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]


lemma pairwise_of_map {l : List E} (h : l.Pairwise (· ≤ ·)) (f : E → D)
    (hf : (l.map f).Pairwise (· < ·)) : l.Pairwise (· < ·) := by
  apply (h.and (List.pairwise_map.mp hf)).imp
  intro a b hab
  exact lt_of_le_of_ne hab.1 (fun he => (ne_of_lt hab.2) (congrArg f he))

lemma map_bracket (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    map f (bracket l) = bracket (l.map f) := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E => bracket (l.val.map f))
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · have hf : ¬(l.map f).Pairwise (· < ·) := fun hm => hs (pairwise_of_map h f hm)
    simp [bracket_of_not_pairwise hs, bracket_of_not_pairwise hf]

lemma map_wordBoundary (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    map f (wordBoundary l) = wordBoundary (l.map f) := by
  simp only [← faces_bracket]
  change (map f).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom, faces_map]
  apply faces_congr
  intro m hm
  exact map_bracket f (h.sublist hm)

lemma map_boundary (f : E →o D) (c : Chains E) :
    map f (boundary c) = boundary (map f c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    rw [hz]
    simp only [map_smul]
    rw [boundary_bracket hl, map_wordBoundary f hl, map_bracket f hl,
      boundary_bracket (List.pairwise_map.mpr (hl.imp fun hh => f.monotone hh))]

@[simp] lemma map_id (c : Chains E) : map (OrderHom.id) c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz, map_smul, map_bracket _ (l.property.imp fun h => le_of_lt h)]
    simp

lemma map_comp (f : E →o D) (g : D →o B) (c : Chains E) :
    map (g.comp f) c = map g (map f c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    rw [hz]
    simp only [map_smul]
    rw [map_bracket _ hl, map_bracket _ hl,
      map_bracket _ (List.pairwise_map.mpr (hl.imp fun hh => f.monotone hh))]
    simp [List.map_map]

end Functoriality

def prismWord {D : Type v} (f g : D → E) : List D → Chains E
  | [] => 0
  | a :: l => bracket ((a :: l).map f ++ [g ((a :: l).getLast (by simp))])

@[simp] lemma prismWord_nil {D : Type v} (f g : D → E) : prismWord f g [] = 0 := rfl

lemma prismWord_append {D : Type v} (f g : D → E) (l : List D) (a : D) :
    prismWord f g (l ++ [a]) = bracket (l.map f ++ [f a, g a]) := by
  cases l with
  | nil => rfl
  | cons b l => simp [prismWord, List.map_append]

lemma prismWord_faces_append {D : Type v} (f g : D → E) (l : List D) (a : D) :
    faces (prismWord f g) (l ++ [a]) =
      append (g a) (append (f a) (wordBoundary (l.map f))) +
        ((-1 : ℤ) ^ l.length) • prismWord f g l := by
  rw [faces_append_singleton]
  congr 1
  have h₁ := faces_hom (append (g a)).toAddMonoidHom
    (fun m => bracket (m.map f ++ [f a])) l
  have h₂ := faces_hom (append (f a)).toAddMonoidHom
    (fun m => bracket (m.map f)) l
  simp only [LinearMap.toAddMonoidHom_coe, append_bracket] at h₁ h₂
  simp_rw [prismWord_append]
  simp only [List.append_assoc, List.singleton_append] at h₁
  rw [← h₁, ← h₂, ← faces_map, faces_bracket]

lemma prism_boundary_residual {D : Type v} (f g : D → E) (l : List D) (a : D)
    (h : (l.map f ++ [f a, g a]).Pairwise (· ≤ ·)) :
    boundary (prismWord f g (l ++ [a])) =
      faces (prismWord f g) (l ++ [a]) +
        ((-1 : ℤ) ^ l.length) •
          (append (g a) (bracket (l.map f)) - prismWord f g l -
            bracket ((l ++ [a]).map f)) := by
  rw [prismWord_append, boundary_bracket h]
  rw [show l.map f ++ [f a, g a] = (l.map f ++ [f a]) ++ [g a] by simp]
  rw [wordBoundary_append, wordBoundary_append, prismWord_faces_append]
  simp only [List.length_append, List.length_map, List.length_singleton, pow_succ,
    mul_neg, mul_one, map_add, map_smul, neg_smul, smul_sub, List.map_append,
    List.map_singleton]
  abel

lemma bracket_repeat_end (l : List E) (a : E) : bracket (l ++ [a, a]) = 0 := by
  apply bracket_of_not_pairwise
  simp [List.pairwise_append]

section LinearPrism

variable {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]

def prism (f g : E → D) : Chains E →ₗ[ℤ] Chains D :=
  Finsupp.linearCombination ℤ (fun l : Word E => prismWord f g l.val)

lemma prismWord_eq_zero_of_not_pairwise (f g : E → D) {l : List E}
    (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) :
    prismWord f g l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a =>
    rw [prismWord_append]
    apply bracket_of_not_pairwise
    intro hh
    have hm : ((l ++ [a]).map f).Pairwise (· < ·) := by
      apply (List.pairwise_append.mp (show ((l ++ [a]).map f ++ [g a]).Pairwise
        (· < ·) by simpa using hh)).1
    exact hn (pairwise_of_map h f hm)

lemma prism_bracket (f g : E → D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    prism f g (bracket l) = prismWord f g l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E => prismWord f g l.val)
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, prismWord_eq_zero_of_not_pairwise f g h hs]

lemma prism_wordBoundary (f g : E → D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    prism f g (wordBoundary l) = faces (prismWord f g) l := by
  rw [← faces_bracket]
  change (prism f g).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact prism_bracket f g (h.sublist hm)

omit [PartialOrder E] [PartialOrder D] in

lemma prismWord_map (f g : D → B) (a : E → D) (l : List E) :
    prismWord f g (l.map a) = prismWord (f ∘ a) (g ∘ a) l := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b =>
    simp only [List.map_append, List.map_singleton, prismWord_append, List.map_map,
      Function.comp_apply]

lemma prism_map (f g : D → B) (a : E →o D) (c : Chains E) :
    prism f g (map a c) = prism (f ∘ a) (g ∘ a) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    rw [hz]
    simp only [map_smul]
    rw [map_bracket _ hl,
      prism_bracket _ _ (List.pairwise_map.mpr (hl.imp fun hh => a.monotone hh)),
      prism_bracket _ _ hl, prismWord_map]

end LinearPrism

def degreeSign : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun l : Word E =>
    ((-1 : ℤ) ^ (l.val.length - 1)) • bracket l.val)

lemma degreeSign_bracket (l : List E) :
    degreeSign (bracket l) = ((-1 : ℤ) ^ (l.length - 1)) • bracket l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E =>
      ((-1 : ℤ) ^ (l.val.length - 1)) • bracket l.val)
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp [bracket_of_pairwise hs]
  · simp [bracket_of_not_pairwise hs]


lemma bracket_positive (l : List E) : Positive (bracket l) := by
  classical
  intro w
  by_cases h : l.Pairwise (· < ·)
  · simp [bracket_of_pairwise h, Finsupp.single_apply]
    split <;> omega
  · simp [bracket_of_not_pairwise h]

lemma linearCombination_positive {D : Type v} [PartialOrder D]
    (H : Word E → Chains D) (hH : ∀ w, Positive (H w))
    {c : Chains E} (hc : Positive c) :
    Positive (Finsupp.linearCombination ℤ H c) := by
  intro w
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hc i) (hH i w)

lemma map_positive {D : Type v} [PartialOrder D] (f : E →o D)
    {c : Chains E} (hc : Positive c) : Positive (map f c) :=
  linearCombination_positive _ (fun w => bracket_positive (w.val.map f)) hc

lemma prismWord_positive {D : Type v} (f g : D → E) (l : List D) :
    Positive (prismWord f g l) := by
  cases l with
  | nil => exact fun _ => le_refl _
  | cons a l => exact bracket_positive _

lemma prism_positive {D : Type v} [PartialOrder D] (f g : E → D)
    {c : Chains E} (hc : Positive c) : Positive (prism f g c) :=
  linearCombination_positive _ (fun w => prismWord_positive f g w.val) hc


lemma bracket_mem_grade (l : List E) : bracket l ∈ grade l.length := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    exact Finsupp.single_mem_supported ℤ 1 rfl
  · rw [bracket_of_not_pairwise h]
    exact Submodule.zero_mem _

lemma mem_grade_iff (k : ℕ) (c : Chains E) :
    c ∈ grade k ↔ ∀ w, c w ≠ 0 → w.val.length = k := by
  simp only [grade, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff,
    Finset.mem_coe, Set.mem_ofPred_eq]

lemma linearCombination_mem_grade {D : Type v} [PartialOrder D]
    (H : Word E → Chains D) (k j : ℕ)
    (hH : ∀ w, w.val.length = k → H w ∈ grade j)
    {c : Chains E} (hc : c ∈ grade k) :
    Finsupp.linearCombination ℤ H c ∈ grade j := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  exact Submodule.smul_mem _ _ (hH w ((mem_grade_iff k c).mp hc w
    (Finsupp.mem_support_iff.mp hw)))

lemma map_mem_grade {D : Type v} [PartialOrder D] (f : E →o D) {k : ℕ}
    {c : Chains E} (hc : c ∈ grade k) : map f c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [List.length_map, hw] using bracket_mem_grade (w.val.map f)

lemma prepend_mem_grade (a : E) {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    prepend a c ∈ grade (k+1) := by
  apply linearCombination_mem_grade _ k (k+1) _ hc
  intro w hw
  simpa only [List.length_cons, hw] using bracket_mem_grade (a :: w.val)

lemma wordBoundary_mem_grade (l : List E) : wordBoundary l ∈ grade (l.length-1) := by
  induction l with
  | nil => exact Submodule.zero_mem _
  | cons a l ih =>
    cases l with
    | nil => simpa [wordBoundary] using bracket_mem_grade ([] : List E)
    | cons b l =>
      rw [wordBoundary_cons]
      apply Submodule.sub_mem
      · simpa using bracket_mem_grade (b :: l)
      · simpa using prepend_mem_grade a ih

lemma boundary_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade (k+1)) :
    boundary c ∈ grade k := by
  apply linearCombination_mem_grade _ (k+1) k _ hc
  intro w hw
  simpa only [hw, Nat.add_sub_cancel] using wordBoundary_mem_grade w.val

lemma prismWord_mem_grade {D : Type v} (f g : D → E) (l : List D) :
    prismWord f g l ∈ grade (l.length+1) := by
  cases l with
  | nil => exact Submodule.zero_mem _
  | cons a l =>
    unfold prismWord
    simpa using bracket_mem_grade ((a :: l).map f ++ [g ((a :: l).getLast (by simp))])

lemma prism_mem_grade {D : Type v} [PartialOrder D] (f g : E → D) {k : ℕ}
    {c : Chains E} (hc : c ∈ grade k) : prism f g c ∈ grade (k+1) := by
  apply linearCombination_mem_grade _ k (k+1) _ hc
  intro w hw
  simpa only [hw] using prismWord_mem_grade f g w.val

end NormalizedChains

structure RelativePrismData (E : Type u) [PartialOrder E] (A : Set E) where
  lowerSet : IsLowerSet A
  f : E →o E
  g : E →o E
  below : ∀ e, f e ≤ g e
  agree : ∀ e ∈ A, f e = g e
  constant : ∀ e ∉ A, ∀ e' ∉ A, g e = g e'

namespace RelativePrismData

open NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

lemma prism_ordered (l : List E) (a : E) (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    (l.map d.f ++ [d.f a, d.g a]).Pairwise (· ≤ ·) := by
  rw [show l.map d.f ++ [d.f a, d.g a] = ((l ++ [a]).map d.f) ++ [d.g a] by simp]
  apply List.pairwise_append.mpr
  refine ⟨?_, by simp, ?_⟩
  · exact List.pairwise_map.mpr (h.imp fun hab => d.f.monotone hab)
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    apply le_trans (d.f.monotone ?_) (d.below a)
    have ht := h.rel_getLast hb
    simpa using ht

lemma prism_cancellation (l : List E) (a : E)
    (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    append (d.g a) (bracket (l.map d.f)) - prismWord d.f d.g l =
      bracket ((l ++ [a]).map d.g) := by
  cases l using List.reverseRecOn with
  | nil => simp [prismWord, append_bracket]
  | append_singleton l b =>
    rw [append_bracket, prismWord_append]
    have hlb : (l ++ [b]).Pairwise (· ≤ ·) := (List.pairwise_append.mp h).1
    have hba : b ≤ a := (List.pairwise_append.mp h).2.2 b (by simp) a (by simp)
    by_cases hb : b ∈ A
    · have hprefix : ∀ x ∈ l ++ [b], d.f x = d.g x := by
        intro x hx
        apply d.agree x
        apply d.lowerSet (show x ≤ b by simpa using hlb.rel_getLast hx) hb
      have hf : (l ++ [b]).map d.f = (l ++ [b]).map d.g := by
        exact List.map_congr_left hprefix
      have hzero : bracket (l.map d.f ++ [d.f b, d.g b]) = 0 := by
        rw [d.agree b hb]
        exact bracket_repeat_end _ _
      rw [hzero, sub_zero, hf]
      simp
    · have ha : a ∉ A := fun ha => hb (d.lowerSet hba ha)
      have hg : d.g b = d.g a := d.constant b hb a ha
      have hzero : bracket (((l ++ [b]) ++ [a]).map d.g) = 0 := by
        simp only [List.map_append, List.map_singleton, List.append_assoc, hg]
        exact bracket_repeat_end _ _
      rw [hzero]
      simp only [List.map_append, List.map_singleton, List.append_assoc,
        List.singleton_append, hg, sub_self]

lemma prism_boundary (l : List E) (a : E)
    (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    boundary (prismWord d.f d.g (l ++ [a])) =
      faces (prismWord d.f d.g) (l ++ [a]) +
        ((-1 : ℤ) ^ l.length) •
          (bracket ((l ++ [a]).map d.g) - bracket ((l ++ [a]).map d.f)) := by
  rw [prism_boundary_residual _ _ _ _ (d.prism_ordered l a h),
    d.prism_cancellation l a h]

lemma prism_stationary (l : List E) (h : ∀ x ∈ l, x ∈ A) :
    prismWord d.f d.g l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a =>
    rw [prismWord_append, d.agree a (h a (by simp))]
    exact bracket_repeat_end _ _

lemma boundary_prism (c : Chains E) :
    boundary (prism d.f d.g c) = prism d.f d.g (boundary c) +
      map d.g (degreeSign c) - map d.f (degreeSign c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    have hb : boundary (prism d.f d.g (bracket l.val)) =
        prism d.f d.g (boundary (bracket l.val)) +
          map d.g (degreeSign (bracket l.val)) -
          map d.f (degreeSign (bracket l.val)) := by
      rw [prism_bracket _ _ hl, boundary_bracket hl, prism_wordBoundary _ _ hl,
        degreeSign_bracket]
      simp only [map_smul]
      rw [map_bracket _ hl, map_bracket _ hl]
      rcases l with ⟨l, hs⟩
      dsimp at *
      cases l using List.reverseRecOn with
      | nil => simp [prismWord, faces, boundary, Finsupp.linearCombination]
      | append_singleton l a =>
        rw [d.prism_boundary l a hl]
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, smul_sub]
        abel
    rw [hz]
    simp only [map_smul, hb, smul_add, smul_sub]
    abel

end RelativePrismData
end Thomason

end

end OAI
