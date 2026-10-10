import OAI.Combinatorics.Coboundary.Cones

namespace OAI

noncomputable section

/-!
Binary and finite joins, augmented exactness, and bounded cone constructions.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def complex (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V) where
  faces := {s | s.toLeft ∈ X.faces ∧ s.toRight ∈ Y.faces}
  empty_mem := by simpa [Finset.toLeft, Finset.toRight] using And.intro X.empty_mem Y.empty_mem
  downward := by
    intro s t hs ht
    exact ⟨X.downward hs.1 (by intro x hx; simpa using ht (by simpa using hx : Sum.inl x ∈ t)),
      Y.downward hs.2 (by intro x hx; simpa using ht (by simpa using hx : Sum.inr x ∈ t))⟩

def prepend (B : Finset V) : Raw W →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.lmapDomain k k (·.disjSum B)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma prepend_single (B : Finset V) (A : Finset W) (a : k) :
    prepend B (Finsupp.single A a) = Finsupp.single (A.disjSum B) a :=
  Finsupp.mapDomain_single

lemma prepend_boundary (B : Finset V) (c : Raw W) :
    rawBoundary (prepend B c) = prepend B (rawBoundary c) +
      ∑ v ∈ B, prepend (B.erase v) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, Finset.sum_add_distrib]; abel
  | single A a =>
    rw [prepend_single, boundary_disjSum_single, rawBoundary_single, map_sum]
    simp only [prepend_single]

def leftAction (T : Raw W →ₗ[k] Raw W) : Raw (W ⊕ V) →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.linearCombination k (fun s => prepend s.toRight (T (Finsupp.single s.toLeft 1)))

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma leftAction_single (T : Raw W →ₗ[k] Raw W)
    (s : Finset (W ⊕ V)) (a : k) :
    leftAction T (Finsupp.single s a) = prepend s.toRight (T (Finsupp.single s.toLeft a)) := by
  simp [leftAction, ← map_smul]

omit [DecidableEq V] [DecidableEq W] in
lemma leftAction_prepend (T : Raw W →ₗ[k] Raw W) (B : Finset V) (c : Raw W) :
    leftAction T (prepend B c) = prepend B (T c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single A a => simp

lemma leftAction_homotopy (T : Raw W →ₗ[k] Raw W) (A : Finset W) (B : Finset V) :
    rawBoundary (leftAction T (Finsupp.single (A.disjSum B) 1)) +
      leftAction T (rawBoundary (Finsupp.single (A.disjSum B) 1)) =
        prepend B (rawBoundary (T (Finsupp.single A 1)) + T (rawBoundary (Finsupp.single A 1))) := by
  rw [show Finsupp.single (A.disjSum B) (1 : k) = prepend B (Finsupp.single A 1) by simp]
  rw [leftAction_prepend, prepend_boundary, prepend_boundary, map_add, map_sum]
  simp only [leftAction_prepend]
  rw [map_add]
  have hz := twice (∑ v ∈ B, prepend (B.erase v) (T (Finsupp.single A 1)))
  have he : ∀ a b c : Raw (W ⊕ V), (a+b)+(c+b) = (a+c)+(b+b) := by intros; abel
  rw [he, hz, add_zero]

lemma left_contraction {X : CoboundaryExpanders.InfiniteChains.Complex W} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset (W ⊕ V)) (hs : s.toLeft ∈ X.faces) (hn : s.toLeft.card ≤ n) :
    rawBoundary (leftAction H.hom (Finsupp.single s 1)) +
      leftAction H.hom (rawBoundary (Finsupp.single s 1)) = Finsupp.single s 1 := by
  rw [← Finset.toLeft_disjSum_toRight (u := s)]
  rw [leftAction_homotopy]
  rw [H.contraction s.toLeft hs hn, prepend_single]

lemma leftAction_graded {X : CoboundaryExpanders.InfiniteChains.Complex W} (Y : CoboundaryExpanders.InfiniteChains.Complex V) {n R : ℕ}
    (H : BoundedCone X n R) (r : ℕ) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (graded {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ n} r)) :
    leftAction H.hom c ∈ supported (graded (complex X Y).faces (r+1)) := by
  apply map_supported _ _ _ _ c hc
  intro s hs a
  rw [leftAction_single]
  have hH := H.map_graded s.toLeft.card hs.1.2 (Finsupp.single s.toLeft a)
    (single_mem_supported (P := graded X.faces s.toLeft.card) ⟨hs.1.1.1, rfl⟩ a)
  apply map_supported (prepend s.toRight) (graded X.faces (s.toLeft.card+1))
    (graded (complex X Y).faces (r+1)) _ _ hH
  intro A hA b
  rw [prepend_single]
  apply single_mem_supported
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using hA.1
  · simpa using hs.1.1.2
  · rw [Finset.card_disjSum, hA.2]
    have he := Finset.card_toLeft_add_card_toRight (u := s)
    dsimp [graded] at hs
    omega

lemma fill_small_left {X : CoboundaryExpanders.InfiniteChains.Complex W} (Y : CoboundaryExpanders.InfiniteChains.Complex V) {n R : ℕ}
    (H : BoundedCone X n R) (r : ℕ) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (graded {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ n} r))
    (hz : rawBoundary c = 0) :
    ∃ b ∈ supported (graded (complex X Y).faces (r+1)), rawBoundary b = c := by
  refine ⟨leftAction H.hom c, leftAction_graded Y H r c hc, ?_⟩
  have he := linear_eq_on_supported
    (rawBoundary.comp (leftAction H.hom) + (leftAction H.hom).comp rawBoundary)
    LinearMap.id (graded {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ n} r)
    (fun s hs => left_contraction H s hs.1.1.1 hs.1.2) c hc
  change rawBoundary (leftAction H.hom c) + leftAction H.hom (rawBoundary c) = c at he
  simpa only [hz, map_zero, add_zero] using he

end

open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def truncated (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (M : ℕ) : Set (Finset (W ⊕ V)) :=
  {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ M}

omit [DecidableEq V] [DecidableEq W] in
lemma truncated_downward (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (M : ℕ) :
    ∀ {s t}, s ∈ truncated X Y M → t ⊆ s → t ∈ truncated X Y M := by
  intro s t hs ht
  exact ⟨(complex X Y).downward hs.1 ht,
    (Finset.card_le_card (Finset.toLeft_subset_toLeft ht)).trans hs.2⟩

lemma relative_enlarge_old (P O Q : Set (Finset V)) (r : ℕ)
    (hQ : ∀ {s t}, s ∈ Q → t ⊆ s → t ∈ Q)
    (hOP : O ⊆ P) (hPQ : P ∩ Q ⊆ O) (h : RelativeExactIn O Q r) :
    RelativeExactIn P Q r := by
  intro c hc hz
  have hb := boundary_supported Q hQ c (graded_forget Q r hc)
  have hδ : rawBoundary c ∈ supported O := by
    rw [mem_supported] at hz hb ⊢
    exact fun s hs => hPQ ⟨hz s hs, hb s hs⟩
  obtain ⟨b, hbc, hres⟩ := h c hc hδ
  exact ⟨b, hbc, supported_mono (P := graded O r) (Q := graded P r) (fun s hs => ⟨hOP hs.1, hs.2⟩) hres⟩

lemma relativeExactIn_self (P : Set (Finset V)) (r : ℕ) : RelativeExactIn P P r := by
  intro c hc _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  simpa using hc

lemma truncated_step (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (M r m : ℕ)
    (hr : r ≤ M+m+1) (hY : ∀ j ≤ m, ExactIn Y.faces j) :
    RelativeExactIn (truncated X Y M) (truncated X Y (M+1)) r := by
  classical
  let I := {F : Finset W // F ∈ X.faces ∧ F.card = M+1}
  let A : I → Set (Finset (W ⊕ V)) := fun F => joinFaces F.val Y
  have hAP (F : I) : RelativeExactIn (truncated X Y M) (A F) r := by
    apply relative_enlarge_old (truncated X Y M) (oldFaces F.val Y) (A F) r
      (joinFaces_downward F.val Y)
    · intro s hs
      refine ⟨⟨X.downward F.property.1 hs.1.1, hs.1.2⟩, ?_⟩
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs.1.1, hs.2⟩)
      rw [F.property.2] at hlt
      omega
    · intro s hs
      refine ⟨hs.2, ?_⟩
      intro he
      have hn := hs.1.2
      rw [he, F.property.2] at hn
      omega
    · apply relativeExactIn_join
      intro hf
      exact hY (r-F.val.card) (by rw [F.property.2]; omega)
  have hAA (F G : I) (hFG : F ≠ G) : A F ∩ A G ⊆ truncated X Y M := by
    intro s hs
    refine ⟨⟨X.downward F.property.1 hs.1.1, hs.1.2⟩, ?_⟩
    have hle := Finset.card_le_card hs.1.1
    rw [F.property.2] at hle
    by_contra hnot
    have he : s.toLeft.card = M+1 := by omega
    have hF : s.toLeft = F.val := Finset.eq_of_subset_of_card_le hs.1.1 (by omega)
    have hG : s.toLeft = G.val := Finset.eq_of_subset_of_card_le hs.2.1 (by rw [G.property.2, he])
    exact hFG (Subtype.ext (hF.symm.trans hG))
  have hU := relativeExactIn_iUnion (truncated X Y M) A r
    (fun F => joinFaces_downward F.val Y) hAA hAP
  have he : truncated X Y (M+1) = truncated X Y M ∪ ⋃ F : I, A F := by
    ext s
    constructor
    · intro hs
      by_cases hn : s.toLeft.card ≤ M
      · exact Or.inl ⟨hs.1, hn⟩
      · apply Or.inr
        exact Set.mem_iUnion.mpr ⟨⟨s.toLeft, hs.1.1, by have := hs.2; omega⟩,
          ⟨Finset.Subset.refl _, hs.1.2⟩⟩
    · intro hs
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (by omega)⟩
      · obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
        exact ⟨⟨X.downward F.property.1 hF.1, hF.2⟩,
          (Finset.card_le_card hF.1).trans_eq F.property.2⟩
  rw [he]
  apply relativeExactIn_union _ _ _ r (truncated_downward X Y M) _
    (fun _ hs => hs.1) (relativeExactIn_self _ r) hU
  intro s t hs ht
  obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
  exact Set.mem_iUnion.mpr ⟨F, joinFaces_downward F.val Y hF ht⟩

theorem exactIn_join {X : CoboundaryExpanders.InfiniteChains.Complex W} (Y : CoboundaryExpanders.InfiniteChains.Complex V) {n R : ℕ}
    (H : BoundedCone X n R) (m : ℕ) (hY : ∀ j ≤ m, ExactIn Y.faces j)
    (r : ℕ) (hr : r ≤ n+m+1) : ExactIn (complex X Y).faces r := by
  have hf (M : ℕ) : ∀ c ∈ supported (graded (truncated X Y (n+M)) r),
      rawBoundary c = 0 → ∃ b ∈ supported (graded (complex X Y).faces (r+1)),
        rawBoundary b = c := by
    induction M with
    | zero =>
      intro c hc hz
      exact fill_small_left Y H r c (by simpa only [Nat.add_zero, truncated] using hc) hz
    | succ M ih =>
      intro c hc hz
      obtain ⟨e, he, hres⟩ := truncated_step X Y (n+M) r m (by omega) hY c
        (by simpa only [Nat.add_assoc, Nat.succ_eq_add_one] using hc) (by rw [hz]; exact Submodule.zero_mem _)
      have hzres : rawBoundary (c-rawBoundary e) = 0 := by
        rw [map_sub, hz]
        have hh := LinearMap.congr_fun (rawBoundary_squared (V := W ⊕ V)) e
        change rawBoundary (rawBoundary e) = 0 at hh
        rw [hh, sub_self]
      obtain ⟨b, hb, hbc⟩ := ih (c-rawBoundary e) hres hzres
      refine ⟨e+b, Submodule.add_mem _ ?_ hb, ?_⟩
      · exact supported_mono (P := graded (truncated X Y (n+M+1)) (r+1))
          (Q := graded (complex X Y).faces (r+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) he
      · rw [map_add, hbc]
        abel
  intro c hc hz
  apply hf r c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1, ?_⟩, (hc s hs).2⟩
  have he := Finset.card_toLeft_add_card_toRight (u := s)
  have hcard := (hc s hs).2
  omega

end CoboundaryExpanders.InfiniteChains.Join

namespace CoboundaryExpanders.InfiniteChains.Cone.BoundedCone
open Attachment
variable {V : Type} [DecidableEq V] {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ}

def cut (H : BoundedCone X n R) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s => if s.card ≤ n then H.hom (Finsupp.single s 1) else 0)

@[simp] lemma cut_single (H : BoundedCone X n R) (s : Finset V) (a : k) :
    H.cut (Finsupp.single s a) = if s.card ≤ n then H.hom (Finsupp.single s a) else 0 := by
  by_cases h : s.card ≤ n <;> simp [cut, h, ← map_smul]

lemma cut_boundary (H : BoundedCone X n R) (s : Finset V) (hs : s.card ≤ n+1) :
    H.cut (rawBoundary (Finsupp.single s 1)) = H.hom (rawBoundary (Finsupp.single s 1)) := by
  simp only [rawBoundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [cut_single, ite_eq_left]
  rw [Finset.card_erase_of_mem hv]
  omega

def normalize (H : BoundedCone X n R) : BoundedCone X n R where
  hom := H.cut
  support := by
    intro s hs hn
    rw [cut_single, ite_eq_left hn]
    exact H.support s hs hn
  contraction := by
    intro s hs hn
    rw [cut_single, ite_eq_left hn, cut_boundary H s (by omega)]
    exact H.contraction s hs hn
  bound := by
    intro s hs hn
    rw [cut_single, ite_eq_left hn]
    exact H.bound s hs hn

end CoboundaryExpanders.InfiniteChains.Cone.BoundedCone

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def crossLinear : Raw W →ₗ[k] (Raw V →ₗ[k] Raw (W ⊕ V)) :=
  Finsupp.linearCombination k (fun A => append A)

def cross (c : Raw W) (d : Raw V) : Raw (W ⊕ V) := crossLinear c d

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_single_left (A : Finset W) (a : k) (d : Raw V) :
    cross (Finsupp.single A a) d = a • append A d := by simp [cross, crossLinear]

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_single_right (c : Raw W) (B : Finset V) (b : k) :
    cross c (Finsupp.single B b) = b • prepend B c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [cross]
  | add c d hc hd => simp only [cross, map_add, LinearMap.add_apply] at *; rw [hc, hd, smul_add]
  | single A a => simp [cross_single_left, mul_comm]

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_zero_left (d : Raw V) : cross (0 : Raw W) d = 0 := by simp [cross]
omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma cross_zero_right (c : Raw W) : cross c (0 : Raw V) = 0 := by simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_add_left (c e : Raw W) (d : Raw V) : cross (c+e) d = cross c d + cross e d := by
  simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_add_right (c : Raw W) (d e : Raw V) : cross c (d+e) = cross c d + cross c e := by
  simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_sum_left {ι : Type*} (I : Finset ι) (c : ι → Raw W) (d : Raw V) :
    cross (∑ i ∈ I, c i) d = ∑ i ∈ I, cross (c i) d := by simp [cross]
omit [DecidableEq V] [DecidableEq W] in
lemma cross_sum_right {ι : Type*} (I : Finset ι) (c : Raw W) (d : ι → Raw V) :
    cross c (∑ i ∈ I, d i) = ∑ i ∈ I, cross c (d i) := by simp [cross]

lemma cross_boundary (c : Raw W) (d : Raw V) :
    rawBoundary (cross c d) = cross (rawBoundary c) d + cross c (rawBoundary d) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he =>
    simp only [cross_add_left, map_add, hc, he]
    abel
  | single A a =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d e hd he =>
      simp only [cross_add_right, map_add, hd, he]
      abel
    | single B b =>
      simp only [map_smul, rawBoundary_single, cross_single_right, cross_sum_right]
      simp [prepend_single, map_sum, Finset.smul_sum, mul_comm,
        erase_disjSum_inl, erase_disjSum_inr]

lemma cross_graded (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (a b : ℕ) (c : Raw W) (d : Raw V)
    (hc : c ∈ supported (graded X.faces a)) (hd : d ∈ supported (graded Y.faces b)) :
    cross c d ∈ supported (graded (complex X Y).faces (a+b)) := by
  let T : Raw W →ₗ[k] Raw (W ⊕ V) := (LinearMap.applyₗ (R := k) d).comp crossLinear
  change T c ∈ _
  apply map_supported T _ _ _ c hc
  intro A hA z
  change cross (Finsupp.single A z) d ∈ _
  rw [cross_single_left]
  apply Submodule.smul_mem
  apply map_supported (append A) (graded Y.faces b) _ _ d hd
  intro B hB t
  rw [append_single]
  exact single_mem_supported (P := graded (complex X Y).faces (a+b)) ⟨⟨by simpa using hA.1, by simpa using hB.1⟩,
    by rw [Finset.card_disjSum, hA.2, hB.2]⟩ t

lemma cross_size (c : Raw W) (d : Raw V) : size (cross c d) ≤ size c * size d := by
  let T : Raw W →ₗ[k] Raw (W ⊕ V) := (LinearMap.applyₗ (R := k) d).comp crossLinear
  have hT (A : Finset W) (_ : A ∈ Set.univ) : size (T (Finsupp.single A 1)) ≤ size d := by
    change size (cross (Finsupp.single A 1) d) ≤ _
    rw [cross_single_left, one_smul]
    exact (size_map_le (append A) Set.univ 1 (fun B _ => by simpa using size_single_le (A.disjSum B) (1 : k))
      d (by rw [mem_supported]; simp)).trans_eq (by omega)
  exact (size_map_le T Set.univ (size d) hT c (by rw [mem_supported]; simp)).trans_eq (Nat.mul_comm _ _)

def operator (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V) :
    Raw (W ⊕ V) →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.linearCombination k (fun s =>
    cross (T (Finsupp.single s.toLeft 1)) (U (Finsupp.single s.toRight 1)))

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma operator_single (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V)
    (A : Finset W) (B : Finset V) :
    operator T U (Finsupp.single (A.disjSum B) 1) =
      cross (T (Finsupp.single A 1)) (U (Finsupp.single B 1)) := by simp [operator]

lemma operator_boundary (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V)
    (A : Finset W) (B : Finset V) :
    operator T U (rawBoundary (Finsupp.single (A.disjSum B) 1)) =
      cross (T (rawBoundary (Finsupp.single A 1))) (U (Finsupp.single B 1)) +
      cross (T (Finsupp.single A 1)) (U (rawBoundary (Finsupp.single B 1))) := by
  rw [boundary_disjSum_single, map_add, map_sum, map_sum]
  simp only [operator_single, rawBoundary_single, map_sum, cross_sum_left, cross_sum_right]

def residual (T : Raw V →ₗ[k] Raw V) : Raw V →ₗ[k] Raw V :=
  LinearMap.id + rawBoundary.comp T + T.comp rawBoundary

lemma residual_eq (T : Raw V →ₗ[k] Raw V) (c : Raw V) :
    residual T c = c + rawBoundary (T c) + T (rawBoundary c) := rfl

lemma residual_boundary (T : Raw V →ₗ[k] Raw V) (c : Raw V) :
    rawBoundary (residual T c) = residual T (rawBoundary c) := by
  have hh (x : Raw V) : rawBoundary (rawBoundary x) = 0 :=
    LinearMap.congr_fun (rawBoundary_squared (V := V)) x
  simp [residual_eq, map_add, hh]

def joinHom (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V) :
    Raw (W ⊕ V) →ₗ[k] Raw (W ⊕ V) :=
  operator T LinearMap.id + operator (residual T) U

lemma joinHom_contraction (T : Raw W →ₗ[k] Raw W) (U : Raw V →ₗ[k] Raw V)
    (A : Finset W) (B : Finset V) :
    rawBoundary (joinHom T U (Finsupp.single (A.disjSum B) 1)) +
      joinHom T U (rawBoundary (Finsupp.single (A.disjSum B) 1)) =
        Finsupp.single (A.disjSum B) 1 +
          cross (residual T (Finsupp.single A 1)) (residual U (Finsupp.single B 1)) := by
  simp only [joinHom, LinearMap.add_apply, operator_single, map_add, cross_boundary,
    LinearMap.id_apply, operator_boundary, residual_boundary]
  rw [residual_eq U, cross_add_right, cross_add_right]
  have he := residual_eq T (Finsupp.single A 1)
  have he' := congrArg (fun x => cross x (Finsupp.single B 1)) he
  rw [cross_add_left, cross_add_left] at he'
  have h0 : cross (Finsupp.single A 1) (Finsupp.single B 1) = Finsupp.single (A.disjSum B) 1 := by simp
  rw [h0] at he'
  have h2 (x : Raw (W ⊕ V)) : x+x = 0 := twice x
  rw [he']
  abel_nf
  simp only [two_smul ℤ, twice, zero_add, add_zero]

end

open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma cut_boundary_high {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : n+1 < s.card) : H.cut (rawBoundary (Finsupp.single s 1)) = 0 := by
  rw [rawBoundary_single, map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [BoundedCone.cut_single, ite_eq_right]
  rw [Finset.card_erase_of_mem hv]
  omega

lemma residual_cut_low {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : s ∈ X.faces) (hn : s.card ≤ n) :
    residual H.cut (Finsupp.single s 1) = 0 := by
  rw [residual_eq, add_assoc]
  have he := H.normalize.contraction s hs hn
  change rawBoundary (H.cut (Finsupp.single s 1)) + H.cut (rawBoundary (Finsupp.single s 1)) = _ at he
  rw [he, twice]

lemma residual_cut_graded {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : s ∈ X.faces) :
    residual H.cut (Finsupp.single s 1) ∈ supported (graded X.faces s.card) := by
  by_cases hn : s.card ≤ n
  · rw [residual_cut_low H s hs hn]
    exact Submodule.zero_mem _
  rw [residual_eq, BoundedCone.cut_single, ite_eq_right hn, map_zero, add_zero]
  apply Submodule.add_mem _ (single_mem_supported (P := graded X.faces s.card) ⟨hs, rfl⟩ _)
  by_cases he : s.card = n+1
  · rw [H.cut_boundary s (by omega)]
    rw [he]
    apply H.map_graded n le_rfl
    apply boundary_graded X.faces (fun {_ _} ht h => X.downward ht h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, he⟩ _
  · rw [cut_boundary_high H s (by omega)]
    exact Submodule.zero_mem _

lemma residual_cut_size {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset V) (hs : s ∈ X.faces) :
    size (residual H.cut (Finsupp.single s 1)) ≤ 1+R*(n+1) := by
  by_cases hn : s.card ≤ n
  · rw [residual_cut_low H s hs hn, size_zero]
    omega
  rw [residual_eq, BoundedCone.cut_single, ite_eq_right hn, map_zero, add_zero]
  by_cases he : s.card = n+1
  · have hb : rawBoundary (Finsupp.single s 1) ∈ supported (graded X.faces n) := by
      apply boundary_graded X.faces (fun {_ _} ht h => X.downward ht h) n
      exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, he⟩ _
    rw [H.cut_boundary s (by omega)]
    exact (size_add_le _ _).trans (Nat.add_le_add (size_single_le s (1 : k))
      ((H.size_apply n le_rfl _ hb).trans (Nat.mul_le_mul_left R (by simpa [he] using boundary_single_size s (1 : k)))))
  · rw [cut_boundary_high H s (by omega), add_zero]
    exact (size_single_le s (1 : k)).trans (by omega)

def boundedCone {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {n m R S : ℕ}
    (H : BoundedCone X n R) (K : BoundedCone Y m S) :
    BoundedCone (complex X Y) (n+m+1) (max R ((1+R*(n+1))*S)) where
  hom := joinHom H.cut K.cut
  support := by
    intro s hs hn
    rw [← Finset.toLeft_disjSum_toRight (u := s)]
    simp only [joinHom, LinearMap.add_apply, operator_single, LinearMap.id_apply]
    by_cases hA : s.toLeft.card ≤ n
    · rw [residual_cut_low H s.toLeft hs.1 hA, cross_zero_left, add_zero]
      have hg := cross_graded X Y (s.toLeft.card+1) s.toRight.card
        (H.cut (Finsupp.single s.toLeft 1)) (Finsupp.single s.toRight 1)
        (H.normalize.support s.toLeft hs.1 hA) (single_mem_supported (P := graded Y.faces s.toRight.card) ⟨hs.2, rfl⟩ _)
      convert hg using 1
      simp [Finset.card_disjSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hB : s.toRight.card ≤ m := by
        have hcard := Finset.card_toLeft_add_card_toRight (u := s)
        omega
      rw [BoundedCone.cut_single, ite_eq_right hA, cross_zero_left, zero_add]
      have hg := cross_graded X Y s.toLeft.card (s.toRight.card+1)
        (residual H.cut (Finsupp.single s.toLeft 1)) (K.cut (Finsupp.single s.toRight 1))
        (residual_cut_graded H s.toLeft hs.1) (K.normalize.support s.toRight hs.2 hB)
      convert hg using 1
      simp [Finset.card_disjSum, Nat.add_assoc]
  contraction := by
    intro s hs hn
    rw [← Finset.toLeft_disjSum_toRight (u := s), joinHom_contraction]
    by_cases hA : s.toLeft.card ≤ n
    · rw [residual_cut_low H s.toLeft hs.1 hA, cross_zero_left, add_zero]
    · have hB : s.toRight.card ≤ m := by
        have hcard := Finset.card_toLeft_add_card_toRight (u := s)
        omega
      rw [residual_cut_low K s.toRight hs.2 hB, cross_zero_right, add_zero]
  bound := by
    intro s hs hn
    rw [← Finset.toLeft_disjSum_toRight (u := s)]
    simp only [joinHom, LinearMap.add_apply, operator_single, LinearMap.id_apply]
    by_cases hA : s.toLeft.card ≤ n
    · rw [residual_cut_low H s.toLeft hs.1 hA, cross_zero_left, add_zero]
      exact ((cross_size _ _).trans (Nat.mul_le_mul
        (H.normalize.bound s.toLeft hs.1 hA) (size_single_le s.toRight (1 : k)))).trans
        (by simp)
    · have hB : s.toRight.card ≤ m := by
        have hcard := Finset.card_toLeft_add_card_toRight (u := s)
        omega
      rw [BoundedCone.cut_single, ite_eq_right hA, cross_zero_left, zero_add]
      exact ((cross_size _ _).trans (Nat.mul_le_mul (residual_cut_size H s.toLeft hs.1)
        (K.normalize.bound s.toRight hs.2 hB))).trans (Nat.le_max_right _ _)

end CoboundaryExpanders.InfiniteChains.Join

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
open scoped BigOperators
variable {V : Type} [DecidableEq V]
def fiber {L : ℕ} (s : Finset (Fin L × V)) (i : Fin L) : Finset V :=
  (s.filter fun x => x.1 = i).image Prod.snd
@[simp] lemma mem_fiber {L : ℕ} (s : Finset (Fin L × V)) (i : Fin L) (v : V) :
    v ∈ fiber s i ↔ (i,v) ∈ s := by
  simp only [fiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨j,w⟩,⟨hm,hj⟩,hw⟩
    dsimp only at hj hw
    simpa only [hj,hw] using hm
  · intro h
    exact ⟨(i,v),⟨h,rfl⟩,rfl⟩
def finiteComplex {L : ℕ} (X : Fin L → CoboundaryExpanders.InfiniteChains.Complex V) : InfiniteChains.Complex (Fin L × V) where
  faces := {s | ∀ i, fiber s i ∈ (X i).faces}
  empty_mem := by intro i; simpa only [fiber,Finset.filter_empty,Finset.image_empty] using (X i).empty_mem
  downward := by
    intro s t hs hts i
    apply (X i).downward (hs i)
    intro v hv
    rw [mem_fiber] at hv ⊢
    exact hts hv

def splitEquiv (L : ℕ) : (Fin (L+1) × V) ≃ (V ⊕ (Fin L × V)) where
  toFun x := Fin.cases (Sum.inl x.2) (fun i => Sum.inr (i,x.2)) x.1
  invFun := Sum.elim (fun v => (0,v)) (fun x => (x.1.succ,x.2))
  left_inv := by rintro ⟨i,v⟩; induction i using Fin.cases <;> rfl
  right_inv := by intro x; cases x <;> rfl
omit [DecidableEq V] in
@[simp] lemma splitEquiv_zero (L : ℕ) (v : V) : splitEquiv L (0,v) = Sum.inl v := rfl
omit [DecidableEq V] in
@[simp] lemma splitEquiv_succ (L : ℕ) (i : Fin L) (v : V) :
    splitEquiv L (i.succ,v) = Sum.inr (i,v) := rfl
lemma split_left {L : ℕ} (s : Finset (Fin (L+1) × V)) :
    (s.image (splitEquiv L)).toLeft = fiber s 0 := by
  ext v
  rw [Finset.mem_toLeft,mem_fiber]
  constructor
  · rintro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    have he' : x = (0,v) := (splitEquiv L).injective (he.trans (splitEquiv_zero L v).symm)
    exact he' ▸ hx
  · intro hh
    exact Finset.mem_image.mpr ⟨(0,v),hh,rfl⟩
lemma split_right_fiber {L : ℕ} (s : Finset (Fin (L+1) × V)) (i : Fin L) :
    fiber (s.image (splitEquiv L)).toRight i = fiber s i.succ := by
  ext v
  rw [mem_fiber,Finset.mem_toRight,mem_fiber]
  constructor
  · rintro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    have he' : x = (i.succ,v) := (splitEquiv L).injective (he.trans (splitEquiv_succ L i v).symm)
    exact he' ▸ hx
  · intro hh
    exact Finset.mem_image.mpr ⟨(i.succ,v),hh,rfl⟩
lemma finiteComplex_split {L : ℕ} (X : Fin (L+1) → CoboundaryExpanders.InfiniteChains.Complex V) (s : Finset (Fin (L+1) × V)) :
    s ∈ (finiteComplex X).faces ↔
      s.image (splitEquiv L) ∈ (complex (X 0) (finiteComplex (fun i => X i.succ))).faces := by
  change (∀ i, fiber s i ∈ (X i).faces) ↔
    (s.image (splitEquiv L)).toLeft ∈ (X 0).faces ∧
      ∀ i, fiber (s.image (splitEquiv L)).toRight i ∈ (X i.succ).faces
  simp only [split_left,split_right_fiber]
  constructor
  · exact fun h => ⟨h 0,fun i => h i.succ⟩
  · rintro ⟨h0,h⟩ i
    induction i using Fin.cases
    · exact h0
    · exact h _
lemma finiteComplex_one (X : Fin 1 → CoboundaryExpanders.InfiniteChains.Complex V) (s : Finset (Fin 1 × V)) :
    s ∈ (finiteComplex X).faces ↔ s.image Prod.snd ∈ (X 0).faces := by
  have h : fiber s 0 = s.image Prod.snd := by
    unfold fiber
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact Subsingleton.elim _ _
  change (∀ i, fiber s i ∈ (X i).faces) ↔ _
  simp only [Fin.forall_fin_one,h]
def oneEquiv : (Fin 1 × V) ≃ V where
  toFun := Prod.snd
  invFun v := (0,v)
  left_inv := by rintro ⟨i,v⟩; have hi : i = 0 := Subsingleton.elim _ _; simp only [hi]
  right_inv _ := rfl

theorem exactIn_finiteComplex (L : ℕ) (X : Fin (L+1) → CoboundaryExpanders.InfiniteChains.Complex V)
    (a : Fin (L+1) → ℕ) (ha : ∀ i, 0 < a i)
    (hcones : ∀ i, ∃ R : ℕ, Nonempty (BoundedCone (X i) (a i-1) R))
    (r : ℕ) (hr : r < ∑ i, a i) : ExactIn (finiteComplex X).faces r := by
  induction L generalizing r with
  | zero =>
    obtain ⟨R,⟨H⟩⟩ := hcones 0
    apply exactIn_equivalence oneEquiv _ (X 0).faces (finiteComplex_one X) r
    apply H.exactIn r
    have he : (∑ i, a i) = a 0 := Fin.sum_univ_one a
    rw [he] at hr
    omega
  | succ L ih =>
    obtain ⟨R,⟨H⟩⟩ := hcones 0
    let b : ℕ := ∑ i : Fin (L+1), a i.succ
    have hb : 0 < b := by
      exact Finset.sum_pos (fun i _ => ha i.succ) Finset.univ_nonempty
    have hY : ∀ j ≤ b-1, ExactIn (finiteComplex (fun i : Fin (L+1) => X i.succ)).faces j := by
      intro j hj
      exact ih (fun i => X i.succ) (fun i => a i.succ) (fun i => ha i.succ)
        (fun i => hcones i.succ) j (by change j < b; omega)
    apply exactIn_equivalence (splitEquiv (L+1)) _ _ (finiteComplex_split X) r
    apply exactIn_join (finiteComplex (fun i => X i.succ)) H (b-1) hY r
    rw [Fin.sum_univ_succ] at hr
    have h0 := ha 0
    change r < a 0 + b at hr
    omega
end

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]
lemma exactIn_empty_left [Nonempty W] (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W)
    (hX : ∀ s ∈ X.faces, s = ∅) (r : ℕ) (hY : ExactIn Y.faces r) :
    ExactIn (complex X Y).faces r := by
  classical
  let f : V ⊕ W → W := Sum.elim (fun _ => Classical.choice (inferInstance : Nonempty W)) id
  have hret (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) :
      ∀ v ∈ s, Sum.inr (f v) = v := by
    intro v hv
    cases v with
    | inl v =>
      have hh : v ∈ s.toLeft := by simpa using hv
      rw [hX s.toLeft hs.1] at hh
      exact False.elim (Finset.notMem_empty _ hh)
    | inr w => rfl
  have him (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) : s.image f = s.toRight := by
    ext w
    constructor
    · rintro hh
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
      rw [Finset.mem_toRight,hret s hs v hv]
      exact hv
    · intro hh
      exact Finset.mem_image.mpr ⟨Sum.inr w,by simpa using hh,rfl⟩
  apply exactIn_retract f Sum.inr (complex X Y).faces Y.faces
    (fun s hs => (him s hs).symm ▸ hs.2) _ _ _ hret r hY
  · intro s hs
    change _ ∈ X.faces ∧ _ ∈ Y.faces
    have hl : (s.image (Sum.inr : W → V ⊕ W)).toLeft = ∅ := by ext v; simp [Finset.mem_toLeft]
    have hr : (s.image (Sum.inr : W → V ⊕ W)).toRight = s := by ext w; simp [Finset.mem_toRight]
    rw [hl,hr]
    exact ⟨X.empty_mem,hs⟩
  · intro s hs x hx y hy hh
    have he := congrArg (Sum.inr : W → V ⊕ W) hh
    rwa [hret s hs x hx,hret s hs y hy] at he
  · intro s hs
    exact Sum.inr_injective.injOn
lemma exactIn_empty_right [Nonempty V] (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W)
    (hY : ∀ s ∈ Y.faces, s = ∅) (r : ℕ) (hX : ExactIn X.faces r) :
    ExactIn (complex X Y).faces r := by
  classical
  let f : V ⊕ W → V := Sum.elim id (fun _ => Classical.choice (inferInstance : Nonempty V))
  have hret (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) :
      ∀ v ∈ s, Sum.inl (f v) = v := by
    intro v hv
    cases v with
    | inr v =>
      have hh : v ∈ s.toRight := by simpa using hv
      rw [hY s.toRight hs.2] at hh
      exact False.elim (Finset.notMem_empty _ hh)
    | inl w => rfl
  have him (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) : s.image f = s.toLeft := by
    ext w
    constructor
    · rintro hh
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
      rw [Finset.mem_toLeft,hret s hs v hv]
      exact hv
    · intro hh
      exact Finset.mem_image.mpr ⟨Sum.inl w,by simpa using hh,rfl⟩
  apply exactIn_retract f Sum.inl (complex X Y).faces X.faces
    (fun s hs => (him s hs).symm ▸ hs.1) _ _ _ hret r hX
  · intro s hs
    change _ ∈ X.faces ∧ _ ∈ Y.faces
    have hl : (s.image (Sum.inl : V → V ⊕ W)).toLeft = s := by ext v; simp [Finset.mem_toLeft]
    have hr : (s.image (Sum.inl : V → V ⊕ W)).toRight = ∅ := by ext w; simp [Finset.mem_toRight]
    rw [hl,hr]
    exact ⟨hs,Y.empty_mem⟩
  · intro s hs x hx y hy hh
    have he := congrArg (Sum.inl : V → V ⊕ W) hh
    rwa [hret s hs x hx,hret s hs y hy] at he
  · intro s hs
    exact Sum.inl_injective.injOn
end

open Attachment Cone
open scoped BigOperators
variable {V : Type} [DecidableEq V]
lemma finiteComplex_only_empty {L : ℕ} (X : Fin L → CoboundaryExpanders.InfiniteChains.Complex V)
    (hX : ∀ i s, s ∈ (X i).faces → s = ∅)
    (s : Finset (Fin L × V)) (hs : s ∈ (finiteComplex X).faces) : s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i,v⟩ hv
  have hh : v ∈ fiber s i := (mem_fiber s i v).mpr hv
  rw [hX i (fiber s i) (hs i)] at hh
  exact Finset.notMem_empty _ hh

theorem exactIn_finiteComplex_all [Nonempty V] (L : ℕ) (X : Fin (L+1) → CoboundaryExpanders.InfiniteChains.Complex V)
    (a : Fin (L+1) → ℕ)
    (hcones : ∀ i, 0 < a i → ∃ R : ℕ, Nonempty (BoundedCone (X i) (a i-1) R))
    (hzero : ∀ i, a i = 0 → ∀ s ∈ (X i).faces, s = ∅)
    (r : ℕ) (hr : r < ∑ i, a i) : ExactIn (finiteComplex X).faces r := by
  induction L generalizing r with
  | zero =>
    have he : (∑ i, a i) = a 0 := Fin.sum_univ_one a
    rw [he] at hr
    obtain ⟨R,⟨H⟩⟩ := hcones 0 (by omega)
    apply exactIn_equivalence oneEquiv _ (X 0).faces (finiteComplex_one X) r
    exact H.exactIn r (by omega)
  | succ L ih =>
    let b : ℕ := ∑ i : Fin (L+1), a i.succ
    rw [Fin.sum_univ_succ] at hr
    change r < a 0 + b at hr
    apply exactIn_equivalence (splitEquiv (L+1)) _ _ (finiteComplex_split X) r
    by_cases h0 : a 0 = 0
    · apply exactIn_empty_left (X 0) (finiteComplex (fun i => X i.succ)) (hzero 0 h0) r
      exact ih (fun i => X i.succ) (fun i => a i.succ) (fun i => hcones i.succ)
        (fun i => hzero i.succ) r (by change r < b; omega)
    · obtain ⟨R,⟨H⟩⟩ := hcones 0 (by omega)
      by_cases hb : b = 0
      · have hz (i : Fin (L+1)) : a i.succ = 0 := by
          have he := Finset.sum_eq_zero_iff.mp hb
          exact he i (Finset.mem_univ _)
        apply exactIn_empty_right (X 0) (finiteComplex (fun i => X i.succ))
          (finiteComplex_only_empty _ (fun i => hzero i.succ (hz i))) r
        exact H.exactIn r (by omega)
      · have hY : ∀ j ≤ b-1, ExactIn (finiteComplex (fun i : Fin (L+1) => X i.succ)).faces j := by
          intro j hj
          exact ih (fun i => X i.succ) (fun i => a i.succ) (fun i => hcones i.succ)
            (fun i => hzero i.succ) j (by change j < b; omega)
        apply exactIn_join _ H (b-1) hY r
        omega
end CoboundaryExpanders.InfiniteChains.Join

end

end OAI
