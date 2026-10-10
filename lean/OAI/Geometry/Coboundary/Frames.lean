import OAI.Combinatorics.Coboundary.Cones

namespace OAI

/-!
Unimodular frames, bad-simplex transport, height reduction, and partial-basis exactness.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {R M S T : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def IsFrame (R : Type*) [CommRing R] {M S : Type*} [AddCommGroup M] [Module R M]
    (f : S → M) : Prop :=
  ∃ r : M →ₗ[R] (S → R), ∀ i, r (f i) = Pi.single i 1

lemma frame_empty (f : S → M) [IsEmpty S] : IsFrame R f := by
  refine ⟨0, ?_⟩
  intro i
  exact isEmptyElim i

lemma frame_reindex {f : S → M} (hf : IsFrame R f) (e : T ↪ S) :
    IsFrame R (f ∘ e) := by
  classical
  obtain ⟨r, hr⟩ := hf
  refine ⟨LinearMap.pi (fun j => (LinearMap.proj (e j)).comp r), ?_⟩
  intro i
  ext j
  simp [hr, Pi.single_apply, e.injective.eq_iff]

lemma frame_equiv {f : S → M} (e : T ≃ S) :
    IsFrame R (f ∘ e) ↔ IsFrame R f := by
  constructor
  · intro h
    simpa only [Function.comp_def, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using frame_reindex h e.symm.toEmbedding
  · exact fun h => frame_reindex h e.toEmbedding

variable [Fintype S]

def combine (f : S → M) : (S → R) →ₗ[R] M :=
  ∑ i, (LinearMap.proj i).smulRight (f i)

lemma combine_apply (f : S → M) (x : S → R) :
    combine f x = ∑ i, x i • f i := by simp [combine]

@[simp] lemma combine_single (f : S → M) (i : S) :
    combine f (Pi.single i 1 : S → R) = f i := by
  classical
  simp [combine_apply, Pi.single_apply]

@[simp] lemma retract_combine (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (x : S → R) : r (combine f x) = x := by
  classical
  ext j
  simp [combine_apply, map_sum, hr, Finset.sum_apply, Pi.single_apply]

def quotientProjection (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) : M →ₗ[R] r.ker :=
  LinearMap.codRestrict r.ker (LinearMap.id - (combine f).comp r) (by
    intro x
    change r (x - combine f (r x)) = 0
    rw [map_sub, retract_combine f r hr, sub_self])

@[simp] lemma quotientProjection_val (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (x : M) :
    (quotientProjection f r hr x : M) = x - combine f (r x) := rfl

@[simp] lemma quotientProjection_family (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (i : S) :
    quotientProjection f r hr (f i) = 0 := by
  apply Subtype.ext
  simp [hr]

@[simp] lemma quotientProjection_ker (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (x : r.ker) :
    quotientProjection f r hr x = x := by
  apply Subtype.ext
  simp [show r (x : M) = 0 from x.property]

def splitEquiv (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) : M ≃ₗ[R] (S → R) × r.ker where
  toFun x := (r x, quotientProjection f r hr x)
  invFun x := combine f x.1 + x.2
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · simp [retract_combine f r hr]
    · apply Subtype.ext
      simp [retract_combine f r hr]
  map_add' x y := by simp
  map_smul' a x := by simp

variable [Fintype T]

theorem frame_sum_iff (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (g : T → M) :
    IsFrame R (Sum.elim f g) ↔ IsFrame R (fun j => quotientProjection f r hr (g j)) := by
  classical
  constructor
  · rintro ⟨l, hl⟩
    let q : M →ₗ[R] (T → R) := LinearMap.pi (fun j => (LinearMap.proj (Sum.inr j)).comp l)
    have hqf (i : S) : q (f i) = 0 := by
      ext j
      have hh := congrFun (hl (Sum.inl i)) (Sum.inr j)
      simpa [q, Pi.single_apply] using hh
    have hqg (i : T) : q (g i) = Pi.single i 1 := by
      ext j
      have hh := congrFun (hl (Sum.inr i)) (Sum.inr j)
      simpa [q, Pi.single_apply] using hh
    refine ⟨q.domRestrict r.ker, ?_⟩
    intro i
    change q (g i - combine f (r (g i))) = _
    simp [combine_apply, map_sum, hqf, hqg]
  · rintro ⟨l, hl⟩
    let q := quotientProjection f r hr
    let a : M →ₗ[R] (T → R) := l.comp q
    have haf (i : S) : a (f i) = 0 := by simp [a, q]
    have hag (i : T) : a (g i) = Pi.single i 1 := hl i
    let b : M →ₗ[R] (S → R) := r - (r.comp (combine g)).comp a
    have hbf (i : S) : b (f i) = Pi.single i 1 := by simp [b, haf, hr]
    have hbg (i : T) : b (g i) = 0 := by simp [b, hag]
    refine ⟨LinearMap.pi (Sum.elim (fun i => (LinearMap.proj i).comp b)
      (fun j => (LinearMap.proj j).comp a)), ?_⟩
    intro i
    ext j
    cases i <;> cases j <;> simp [haf, hag, hbf, hbg, Pi.single_apply]

lemma frame_rank_split [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M]
    (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) :
    Fintype.card S + Module.finrank R r.ker = Module.finrank R M := by
  have hh := (splitEquiv f r hr).finrank_eq
  rw [Module.finrank_prod, Module.finrank_pi] at hh
  exact hh.symm

end CoboundaryExpanders.Unimodular

end

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.BadSimplex
open Attachment
variable {W V : Type} [DecidableEq W] [DecidableEq V]

def stage (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V) where
  faces := {s | s ∈ X.faces ∧ s.toLeft.card ≤ r}
  empty_mem := ⟨X.empty_mem, by simp [Finset.toLeft]⟩
  downward := by
    intro s t hs ht
    exact ⟨X.downward hs.1 ht,
      (Finset.card_le_card (Finset.toLeft_subset_toLeft ht)).trans hs.2⟩

def goodLink (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {t | F.disjSum t ∈ X.faces}
  empty_mem := hF
  downward := by
    intro s t hs ht
    exact X.downward hs (Finset.disjSum_mono (by rfl) ht)

omit [DecidableEq W] [DecidableEq V] in
lemma block_faces (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) :
    joinFaces F (goodLink X F hF) ⊆ X.faces := by
  intro s hs
  have hh : s.toLeft.disjSum s.toRight ⊆ F.disjSum s.toRight :=
    Finset.disjSum_mono hs.1 (by rfl)
  rw [Finset.toLeft_disjSum_toRight] at hh
  exact X.downward hs.2 hh

omit [DecidableEq W] [DecidableEq V] in
lemma block_stage (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) (hcard : F.card ≤ r) :
    joinFaces F (goodLink X F hF) ⊆ (stage X r).faces := by
  intro s hs
  exact ⟨block_faces X F hF hs, (Finset.card_le_card hs.1).trans hcard⟩

omit [DecidableEq W] [DecidableEq V] in
lemma old_stage (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) (hcard : F.card = r+1) :
    oldFaces F (goodLink X F hF) ⊆ (stage X r).faces := by
  intro s hs
  refine ⟨block_faces X F hF hs.1, ?_⟩
  have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs.1.1, hs.2⟩)
  omega

lemma block_relative (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r n : ℕ) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) (hcard : F.card = r+1)
    (hL : F.card ≤ n → ExactIn (goodLink X F hF).faces (n-F.card)) :
    RelativeExactIn (stage X r).faces (joinFaces F (goodLink X F hF)) n := by
  intro c hc hd
  have hdblock := boundary_supported _ (joinFaces_downward F (goodLink X F hF)) c
    (graded_forget _ n hc)
  have hdold : rawBoundary c ∈ supported (oldFaces F (goodLink X F hF)) := by
    rw [mem_supported] at hd hdblock ⊢
    intro s hs
    refine ⟨hdblock s hs, ?_⟩
    intro he
    have hh := (hd s hs).2
    change s.toLeft.card ≤ r at hh
    rw [he, hcard] at hh
    omega
  obtain ⟨b, hb, he⟩ := relativeExactIn_join F (goodLink X F hF) n hL c hc hdold
  refine ⟨b, hb, supported_mono (P := graded (oldFaces F (goodLink X F hF)) n)
    (Q := graded (stage X r).faces n) (fun s hs => ⟨old_stage X r F hF hcard hs.1, hs.2⟩) he⟩

abbrev BadFaces (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) :=
  {F : Finset W // F.disjSum (∅ : Finset V) ∈ X.faces ∧ F.card = r+1}

omit [DecidableEq W] [DecidableEq V] in
lemma stage_succ (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) :
    (stage X (r+1)).faces = (stage X r).faces ∪
      ⋃ F : BadFaces X r, joinFaces F.val (goodLink X F.val F.property.1) := by
  ext s
  constructor
  · rintro ⟨hs, hr⟩
    by_cases h : s.toLeft.card ≤ r
    · exact Or.inl ⟨hs, h⟩
    · refine Or.inr (Set.mem_iUnion.mpr ⟨⟨s.toLeft, ?_, by omega⟩, ?_⟩)
      · apply X.downward hs
        conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
        exact Finset.disjSum_mono (by rfl) (Finset.empty_subset _)
      · refine ⟨Finset.Subset.refl _, ?_⟩
        change s.toLeft.disjSum s.toRight ∈ X.faces
        rw [Finset.toLeft_disjSum_toRight]
        exact hs
  · rintro (hs | hs)
    · exact ⟨hs.1, hs.2.trans (Nat.le_succ r)⟩
    · obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
      exact block_stage X (r+1) F.val F.property.1 F.property.2.le hF

omit [DecidableEq W] [DecidableEq V] in
lemma blocks_inter (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) (F G : BadFaces X r)
    (hFG : F ≠ G) :
    joinFaces F.val (goodLink X F.val F.property.1) ∩
      joinFaces G.val (goodLink X G.val G.property.1) ⊆ (stage X r).faces := by
  intro s hs
  refine ⟨block_faces X F.val F.property.1 hs.1, ?_⟩
  by_contra hh
  have hc : s.toLeft.card = r+1 := by
    have := Finset.card_le_card hs.1.1
    rw [F.property.2] at this
    omega
  have hf : s.toLeft = F.val := Finset.eq_of_subset_of_card_le hs.1.1 (by omega)
  have hg : s.toLeft = G.val := Finset.eq_of_subset_of_card_le hs.2.1 (by omega)
  exact hFG (Subtype.ext (hf.symm.trans hg))

lemma relative_self (P : Set (Finset V)) (n : ℕ) : RelativeExactIn P P n := by
  intro c hc _
  exact ⟨0, Submodule.zero_mem _, by simpa using hc⟩

lemma relative_stage_succ (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r n : ℕ)
    (hL : ∀ F : BadFaces X r, F.val.card ≤ n →
      ExactIn (goodLink X F.val F.property.1).faces (n-F.val.card)) :
    RelativeExactIn (stage X r).faces (stage X (r+1)).faces n := by
  rw [stage_succ]
  apply relativeExactIn_union _ _ _ n (stage X r).downward
  · intro s t hs ht
    obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
    exact Set.mem_iUnion.mpr ⟨F, joinFaces_downward _ _ hF ht⟩
  · intro s hs
    exact hs.1
  · exact relative_self _ n
  · apply relativeExactIn_iUnion
    · intro F
      exact joinFaces_downward _ _
    · exact blocks_inter X r
    · intro F
      exact block_relative X r n F.val F.property.1 F.property.2 (hL F)

lemma exactIn_of_relative {Z : Type} [DecidableEq Z]
    (P Q : Set (Finset Z)) (hPQ : P ⊆ Q) (n : ℕ)
    (hP : ExactIn P n) (hR : RelativeExactIn P Q n) : ExactIn Q n := by
  intro c hc hz
  obtain ⟨b, hb, hcb⟩ := hR c hc (by rw [hz]; exact Submodule.zero_mem _)
  have hzc : rawBoundary (c - rawBoundary b) = 0 := by
    rw [map_sub, hz]
    have hh := LinearMap.congr_fun (rawBoundary_squared (V := Z)) b
    change rawBoundary (rawBoundary b) = 0 at hh
    rw [hh, sub_self]
  obtain ⟨a, ha, hea⟩ := hP _ hcb hzc
  refine ⟨a+b, ?_, ?_⟩
  · exact Submodule.add_mem _
      (supported_mono (P := graded P (n+1)) (Q := graded Q (n+1))
        (fun s hs => ⟨hPQ hs.1, hs.2⟩) ha) hb
  · rw [map_add, hea, sub_add_cancel]

lemma relative_trans {Z : Type} [DecidableEq Z]
    (P Q T : Set (Finset Z)) (hPQ : P ⊆ Q) (hQT : Q ⊆ T) (n : ℕ)
    (hP : RelativeExactIn P Q n) (hQ : RelativeExactIn Q T n) : RelativeExactIn P T n := by
  intro c hc hd
  obtain ⟨b, hb, hcb⟩ := hQ c hc (supported_mono hPQ hd)
  have hdd : rawBoundary (c - rawBoundary b) = rawBoundary c := by
    rw [map_sub]
    have hh := LinearMap.congr_fun (rawBoundary_squared (V := Z)) b
    change rawBoundary (rawBoundary b) = 0 at hh
    rw [hh, sub_zero]
  obtain ⟨a, ha, he⟩ := hP _ hcb (by rw [hdd]; exact hd)
  refine ⟨a+b, Submodule.add_mem _
    (supported_mono (P := graded Q (n+1)) (Q := graded T (n+1))
      (fun s hs => ⟨hQT hs.1, hs.2⟩) ha) hb, ?_⟩
  have heq : c - rawBoundary (a+b) = (c-rawBoundary b)-rawBoundary a := by
    rw [map_add]; abel
  rw [heq]
  exact he

theorem relative (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (n : ℕ)
    (hlinks : ∀ F : Finset W, ∀ hF : F.disjSum (∅ : Finset V) ∈ X.faces,
      F.Nonempty → F.card ≤ n → ExactIn (goodLink X F hF).faces (n-F.card)) :
    RelativeExactIn (stage X 0).faces X.faces n := by
  have stages (r : ℕ) : RelativeExactIn (stage X 0).faces (stage X r).faces n := by
    induction r with
    | zero => exact relative_self _ n
    | succ r ih =>
      apply relative_trans (stage X 0).faces (stage X r).faces (stage X (r+1)).faces
        (fun s hs => ⟨hs.1, hs.2.trans (Nat.zero_le r)⟩)
        (fun s hs => ⟨hs.1, hs.2.trans (Nat.le_succ r)⟩) n ih
      apply relative_stage_succ
      intro F hn
      exact hlinks F.val F.property.1
        (Finset.card_pos.mp (by rw [F.property.2]; omega)) hn
  intro c hc hd
  have hcn : c ∈ supported (graded (stage X n).faces n) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    obtain ⟨hx, hn⟩ := hc s hs
    refine ⟨⟨hx, ?_⟩, hn⟩
    have hh := Finset.card_toLeft_add_card_toRight (u := s)
    omega
  obtain ⟨b, hb, he⟩ := stages n c hcn hd
  exact ⟨b, supported_mono (P := graded (stage X n).faces (n+1))
    (Q := graded X.faces (n+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) hb, he⟩

theorem exactIn (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (n : ℕ)
    (hbase : ExactIn (stage X 0).faces n)
    (hlinks : ∀ F : Finset W, ∀ hF : F.disjSum (∅ : Finset V) ∈ X.faces,
      F.Nonempty → F.card ≤ n → ExactIn (goodLink X F hF).faces (n-F.card)) :
    ExactIn X.faces n := by
  have stages (r : ℕ) : ExactIn (stage X r).faces n := by
    induction r with
    | zero => exact hbase
    | succ r ih =>
      apply exactIn_of_relative (stage X r).faces (stage X (r+1)).faces
        (fun s hs => ⟨hs.1, hs.2.trans (Nat.le_succ r)⟩) n ih
      apply relative_stage_succ
      intro F hn
      exact hlinks F.val F.property.1
        (Finset.card_pos.mp (by rw [F.property.2]; omega)) hn
  intro c hc hz
  have hcn : c ∈ supported (graded (stage X n).faces n) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    obtain ⟨hx, hn⟩ := hc s hs
    refine ⟨⟨hx, ?_⟩, hn⟩
    have hh := Finset.card_toLeft_add_card_toRight (u := s)
    omega
  obtain ⟨b, hb, he⟩ := stages n c hcn hz
  exact ⟨b, supported_mono (P := graded (stage X n).faces (n+1))
    (Q := graded X.faces (n+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) hb, he⟩

end CoboundaryExpanders.InfiniteChains.BadSimplex

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.ChainTransport
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]
def relabel (f : V → W) : Raw V →ₗ[k] Raw W :=
  Finsupp.lmapDomain k k (Finset.image f)

omit [DecidableEq V] in
@[simp] lemma relabel_single (f : V → W) (s : Finset V) (a : k) :
    relabel f (Finsupp.single s a) = Finsupp.single (s.image f) a := by
  simp [relabel]

omit [DecidableEq V] in
lemma relabel_supported (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W))
    (h : ∀ s ∈ P, s.image f ∈ Q) (c : Raw V) (hc : c ∈ supported P) :
    relabel f c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [relabel_single]
  exact single_mem_supported (h s hs) a

omit [DecidableEq V] in
lemma relabel_graded (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W)) (r : ℕ)
    (h : ∀ s ∈ P, s.image f ∈ Q)
    (hinj : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (c : Raw V) (hc : c ∈ supported (graded P r)) :
    relabel f c ∈ supported (graded Q r) := by
  apply relabel_supported f (graded P r) (graded Q r) _ c hc
  intro s hs
  exact ⟨h s hs.1, (Finset.card_image_of_injOn (hinj s hs.1)).trans hs.2⟩

omit [DecidableEq V] in
lemma relabel_injective (f : V → W) (hf : Function.Injective f) :
    Function.Injective (relabel f) :=
  Finsupp.mapDomain_injective (Finset.image_injective hf)

lemma relabel_boundary (f : V → W) (hf : Function.Injective f) :
    rawBoundary.comp (relabel f) = (relabel f).comp rawBoundary := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, relabel_single,
    rawBoundary_single, map_sum, Finset.sum_image, hf.injOn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.image_erase hf]

omit [DecidableEq V] in
lemma relabel_comp {U : Type} [DecidableEq U] (f : V → W) (g : W → U) :
    (relabel g).comp (relabel f) = relabel (g ∘ f) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp [Finset.image_image]

lemma relabel_id : relabel (id : V → V) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp

theorem exactIn_equiv (e : V ≃ W) (P : Set (Finset V)) (Q : Set (Finset W))
    (he : ∀ s, s ∈ P ↔ s.image e ∈ Q) (n : ℕ) (hQ : ExactIn Q n) : ExactIn P n := by
  intro c hc hz
  have hy := relabel_graded e P Q n (fun s hs => (he s).mp hs)
    (fun _ _ => e.injective.injOn) c hc
  have hyd : rawBoundary (relabel e c) = 0 := by
    have hh := LinearMap.congr_fun (relabel_boundary e e.injective) c
    change rawBoundary (relabel e c) = relabel e (rawBoundary c) at hh
    rw [hh, hz, map_zero]
  obtain ⟨b, hb, hbc⟩ := hQ _ hy hyd
  have hg (s : Finset W) (hs : s ∈ Q) : s.image e.symm ∈ P := by
    apply (he _).mpr
    simpa [Finset.image_image, Function.comp_def] using hs
  refine ⟨relabel e.symm b,
    relabel_graded e.symm Q P (n+1) hg (fun _ _ => e.symm.injective.injOn) b hb, ?_⟩
  have hh := LinearMap.congr_fun (relabel_boundary e.symm e.symm.injective) b
  change rawBoundary (relabel e.symm b) = relabel e.symm (rawBoundary b) at hh
  rw [hh, hbc]
  have hret := LinearMap.congr_fun (relabel_comp e e.symm) c
  change relabel e.symm (relabel e c) = relabel (e.symm ∘ e) c at hret
  rw [hret]
  have heq : e.symm ∘ e = id := by funext x; simp
  rw [heq, relabel_id]
  rfl

lemma relabel_equiv_cancel (e : V ≃ W) (c : Raw V) :
    relabel e.symm (relabel e c) = c := by
  have hh := LinearMap.congr_fun (relabel_comp e e.symm) c
  change relabel e.symm (relabel e c) = relabel (e.symm ∘ e) c at hh
  rw [hh]
  have he : e.symm ∘ e = id := by funext x; simp
  rw [he, relabel_id]
  rfl

lemma relabel_boundary_apply (f : V → W) (hf : Function.Injective f) (c : Raw V) :
    rawBoundary (relabel f c) = relabel f (rawBoundary c) :=
  LinearMap.congr_fun (relabel_boundary f hf) c

theorem relativeIn_equiv (e : V ≃ W) (P Q : Set (Finset V)) (P' Q' : Set (Finset W))
    (hP : ∀ s, s ∈ P ↔ s.image e ∈ P')
    (hQ : ∀ s, s ∈ Q ↔ s.image e ∈ Q') (n : ℕ)
    (hR : RelativeExactIn P' Q' n) : RelativeExactIn P Q n := by
  intro c hc hd
  have hce := relabel_graded e Q Q' n (fun s hs => (hQ s).mp hs)
    (fun _ _ => e.injective.injOn) c hc
  have hde : rawBoundary (relabel e c) ∈ supported P' := by
    rw [relabel_boundary_apply e e.injective]
    exact relabel_supported e P P' (fun s hs => (hP s).mp hs) _ hd
  obtain ⟨b, hb, he⟩ := hR _ hce hde
  have inverse (A : Set (Finset V)) (A' : Set (Finset W))
      (hA : ∀ s, s ∈ A ↔ s.image e ∈ A') (s : Finset W) (hs : s ∈ A') :
      s.image e.symm ∈ A := by
    apply (hA _).mpr
    simpa [Finset.image_image, Function.comp_def] using hs
  refine ⟨relabel e.symm b,
    relabel_graded e.symm Q' Q (n+1) (inverse Q Q' hQ)
      (fun _ _ => e.symm.injective.injOn) b hb, ?_⟩
  have ht := relabel_graded e.symm P' P n (inverse P P' hP)
    (fun _ _ => e.symm.injective.injOn) _ he
  rw [map_sub, relabel_equiv_cancel] at ht
  rw [relabel_boundary_apply e.symm e.symm.injective]
  exact ht

lemma rawCone_supported (a : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : rawCone a c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs r
  rw [rawCone_single]
  split_ifs with ha
  · exact Submodule.zero_mem _
  · exact single_mem_supported (h s hs ha) r

lemma rawCone_graded (a : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P n)) :
    rawCone a c ∈ supported (graded Q (n+1)) := by
  apply rawCone_supported a (graded P n) (graded Q (n+1)) _ c hc
  intro s hs ha
  exact ⟨h s hs.1 ha, by rw [Finset.card_insert_of_notMem ha, hs.2]⟩

lemma exactIn_of_extend (P Q : Set (Finset V)) (a : V)
    (ha : ∀ s ∈ P, a ∉ s → insert a s ∈ Q) (n : ℕ) :
    ∀ c ∈ supported (graded P n), rawBoundary c = 0 →
      ∃ b ∈ supported (graded Q (n+1)), rawBoundary b = c := by
  intro c hc hz
  refine ⟨rawCone a c, rawCone_graded a P Q n ha c hc, ?_⟩
  have hh := LinearMap.congr_fun (raw_contraction a) c
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hz, map_zero, add_zero] using hh

end CoboundaryExpanders.InfiniteChains.ChainTransport

end

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment
variable {R M V W : Type} [CommRing R] [AddCommGroup M] [Module R M]
variable [DecidableEq V] [DecidableEq W]

def complex (R : Type) [CommRing R] {M V : Type} [AddCommGroup M] [Module R M]
    (f : V → M) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {s | IsFrame R (fun v : s => f v)}
  empty_mem := frame_empty _
  downward := by
    intro s t hs hts
    let e : t ↪ s := ⟨(fun v => ⟨v.val, hts v.property⟩),
      fun x y h => Subtype.ext (congrArg (fun z : s => z.val) h)⟩
    exact frame_reindex hs e

omit [DecidableEq V] in
lemma frame_image (f : W → M) (e : V ↪ W) (s : Finset V) :
    s.image e ∈ (complex R f).faces ↔ s ∈ (complex R (f ∘ e)).faces := by
  rw [← Finset.map_eq_image]
  exact (frame_equiv (R := R) (f := fun w : s.map e => f w) (Finset.equivMap e s)).symm

def disjSumEquiv (s : Finset V) (t : Finset W) : (s ⊕ t) ≃ s.disjSum t :=
  Equiv.ofBijective (Sum.elim (fun v => ⟨Sum.inl v.val, by simp⟩)
    (fun w => ⟨Sum.inr w.val, by simp⟩)) (by
      constructor
      · intro x y h
        cases x with
        | inl x => cases y with
          | inl y => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val h)))
          | inr y =>
            have hh : Sum.inl x.val = Sum.inr y.val := congrArg (fun z : s.disjSum t => z.val) h
            cases hh
        | inr x => cases y with
          | inl y =>
            have hh : Sum.inr x.val = Sum.inl y.val := congrArg (fun z : s.disjSum t => z.val) h
            cases hh
          | inr y => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (congrArg Subtype.val h)))
      · rintro ⟨x,hx⟩
        cases x with
        | inl x => exact ⟨Sum.inl ⟨x, by simpa using hx⟩, rfl⟩
        | inr x => exact ⟨Sum.inr ⟨x, by simpa using hx⟩, rfl⟩)

omit [DecidableEq V] [DecidableEq W] in
lemma frame_disjSum (f : V ⊕ W → M) (s : Finset V) (t : Finset W) :
    s.disjSum t ∈ (complex R f).faces ↔
      IsFrame R (Sum.elim (fun v : s => f (Sum.inl v)) (fun w : t => f (Sum.inr w))) := by
  change IsFrame R (fun x : s.disjSum t => f x) ↔ _
  rw [← frame_equiv (R := R) (f := fun x : s.disjSum t => f x) (disjSumEquiv s t)]
  have he : (fun x : s.disjSum t => f x) ∘ disjSumEquiv s t =
      Sum.elim (fun v : s => f (Sum.inl v)) (fun w : t => f (Sum.inr w)) := by
    funext x
    cases x <;> rfl
  rw [he]

omit [DecidableEq V] [DecidableEq W] in
lemma frame_inl (f : V ⊕ W → M) (s : Finset V) :
    s.disjSum (∅ : Finset W) ∈ (complex R f).faces ↔
      IsFrame R (fun v : s => f (Sum.inl v)) := by
  rw [Finset.disjSum_empty]
  exact (frame_equiv (R := R) (f := fun x : s.map (@Function.Embedding.inl V W) => f x.val)
    (Finset.equivMap (@Function.Embedding.inl V W) s)).symm

lemma frame_adjoin {S : Type} [Fintype S] (f : S → M) (hf : IsFrame R f)
    (a : M) (φ : M →ₗ[R] R) (ha : φ a = 1) (hfφ : ∀ i, φ (f i) = 0) :
    IsFrame R (Sum.elim (fun _ : Unit => a) f) := by
  obtain ⟨r, hr⟩ := hf
  let l : M →ₗ[R] (Unit → R) := LinearMap.pi (fun _ => φ)
  have hl (i : Unit) : l a = Pi.single i 1 := by ext j; cases i; cases j; simpa [l] using ha
  apply (frame_sum_iff (fun _ : Unit => a) l (by intro i; ext j; cases i; cases j; simpa [l] using ha) f).mpr
  refine ⟨r.domRestrict l.ker, ?_⟩
  intro i
  change r (f i - combine (fun _ : Unit => a) (l (f i))) = Pi.single i 1
  have hz : l (f i) = 0 := by ext j; exact hfφ i
  rw [hz, map_zero, sub_zero, hr]

def insertEquiv (a : V) (s : Finset V) (ha : a ∉ s) : (Unit ⊕ s) ≃ ↥(insert a s) :=
  Equiv.ofBijective (Sum.elim (fun _ => ⟨a, Finset.mem_insert_self _ _⟩)
    (fun v => ⟨v.val, Finset.mem_insert_of_mem v.property⟩)) (by
      constructor
      · intro x y h
        cases x with
        | inl x => cases y with
          | inl y => congr
          | inr y =>
            have hh : a = y.val := congrArg (fun z : ↥(insert a s) => z.val) h
            exact (ha (hh ▸ y.property)).elim
        | inr x => cases y with
          | inl y =>
            have hh : x.val = a := congrArg (fun z : ↥(insert a s) => z.val) h
            exact (ha (hh ▸ x.property)).elim
          | inr y => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : ↥(insert a s) => z.val) h))
      · rintro ⟨x,hx⟩
        obtain rfl | hx := Finset.mem_insert.mp hx
        · exact ⟨Sum.inl (), rfl⟩
        · exact ⟨Sum.inr ⟨x,hx⟩,rfl⟩)

lemma insert_mem (f : V → M) (s : Finset V) (hs : s ∈ (complex R f).faces)
    (a : V) (ha : a ∉ s) (φ : M →ₗ[R] R) (hφa : φ (f a) = 1)
    (hφs : ∀ v ∈ s, φ (f v) = 0) : insert a s ∈ (complex R f).faces := by
  change IsFrame R (fun v : ↥(insert a s) => f v)
  apply (frame_equiv (R := R) (f := fun v : ↥(insert a s) => f v) (insertEquiv a s ha)).mp
  have he : (fun v : ↥(insert a s) => f v) ∘ insertEquiv a s ha =
      Sum.elim (fun _ : Unit => f a) (fun v : s => f v) := by
    funext x
    cases x <;> rfl
  rw [he]
  exact frame_adjoin (fun v : s => f v) hs (f a) φ hφa (fun v => hφs v.val v.property)

lemma fill_zero_coordinate (f : V → M) (φ : M →ₗ[R] R) (a : V)
    (ha : φ (f a) = 1) (n : ℕ) :
    ∀ c ∈ supported (graded {s | s ∈ (complex R f).faces ∧ ∀ v ∈ s, φ (f v) = 0} n),
      rawBoundary c = 0 → ∃ b ∈ supported (graded (complex R f).faces (n+1)), rawBoundary b = c := by
  apply InfiniteChains.ChainTransport.exactIn_of_extend _ _ a
  intro s hs has
  exact insert_mem f s hs.1 a has φ ha hs.2

end CoboundaryExpanders.Unimodular

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.HeightReduction
open Attachment BadSimplex ChainTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type} [DecidableEq V]

def bounded (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H : ℕ) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {s | s ∈ X.faces ∧ ∀ v ∈ s, h v ≤ H}
  empty_mem := ⟨X.empty_mem, by simp⟩
  downward := by
    intro s t hs ht
    exact ⟨X.downward hs.1 ht, fun v hv => hs.2 v (ht hv)⟩

abbrev Bad (h : V → ℕ) (H : ℕ) := {v // H ≤ h v}
abbrev Good (h : V → ℕ) (H : ℕ) := {v // ¬ H ≤ h v}

def split (h : V → ℕ) (H : ℕ) : Bad h H ⊕ Good h H ≃ V :=
  Equiv.sumCompl (fun v => H ≤ h v)

def splitComplex (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H : ℕ) : CoboundaryExpanders.InfiniteChains.Complex (Bad h H ⊕ Good h H) where
  faces := {s | s.image (split h H) ∈ (bounded X h H).faces}
  empty_mem := by simpa using (bounded X h H).empty_mem
  downward := by
    intro s t hs ht
    exact (bounded X h H).downward hs (Finset.image_mono _ ht)

lemma stage0_iff (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H : ℕ)
    (s : Finset (Bad h H ⊕ Good h H)) :
    s ∈ (stage (splitComplex X h H) 0).faces ↔
      s.image (split h H) ∈ X.faces ∧ ∀ v ∈ s.image (split h H), h v < H := by
  constructor
  · rintro ⟨⟨hs, hb⟩, hz⟩
    refine ⟨hs, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    cases x with
    | inl x =>
      have hm : x ∈ s.toLeft := by simpa using hx
      have he : s.toLeft = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [he] at hm
    | inr x => exact Nat.lt_of_not_ge x.property
  · rintro ⟨hs, hb⟩
    refine ⟨⟨hs, fun v hv => (hb v hv).le⟩, ?_⟩
    have he : s.toLeft = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm : Sum.inl x ∈ s := by simpa using hx
      have hh := hb x.val (Finset.mem_image.mpr ⟨Sum.inl x, hm, rfl⟩)
      exact (Nat.not_lt_of_ge x.property) hh
    simp [he]

lemma relative_lower (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H n : ℕ)
    (hlinks : ∀ F : Finset (Bad h H),
      ∀ hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex X h H).faces,
      F.Nonempty → F.card ≤ n →
      ExactIn (goodLink (splitComplex X h H) F hF).faces (n-F.card)) :
    RelativeExactIn {s | s ∈ X.faces ∧ ∀ v ∈ s, h v < H} (bounded X h H).faces n := by
  apply relativeIn_equiv (split h H).symm _ _ (stage (splitComplex X h H) 0).faces
    (splitComplex X h H).faces
  · intro s
    rw [stage0_iff]
    simp [Finset.image_image, Function.comp_def]
  · intro s
    change s ∈ (bounded X h H).faces ↔
      (s.image (split h H).symm).image (split h H) ∈ (bounded X h H).faces
    simp [Finset.image_image, Function.comp_def]
  · exact BadSimplex.relative _ n hlinks

theorem exactIn (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (n : ℕ)
    (hzero : ∀ c ∈ supported (graded (bounded X h 0).faces n),
      rawBoundary c = 0 → ∃ b ∈ supported (graded X.faces (n+1)), rawBoundary b = c)
    (hlinks : ∀ H : ℕ, 0 < H → ∀ F : Finset (Bad h H),
      ∀ hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex X h H).faces,
      F.Nonempty → F.card ≤ n →
      ExactIn (goodLink (splitComplex X h H) F hF).faces (n-F.card)) :
    ExactIn X.faces n := by
  have fill (H : ℕ) : ∀ c ∈ supported (graded (bounded X h H).faces n),
      rawBoundary c = 0 → ∃ b ∈ supported (graded X.faces (n+1)), rawBoundary b = c := by
    induction H using Nat.strong_induction_on with
    | h H ih =>
      intro c hc hz
      by_cases hH : H = 0
      · subst H; exact hzero c hc hz
      · have hp : 0 < H := Nat.pos_of_ne_zero hH
        obtain ⟨b, hb, he⟩ := relative_lower X h H n (hlinks H hp) c hc
          (by rw [hz]; exact Submodule.zero_mem _)
        have hl : c - rawBoundary b ∈ supported (graded (bounded X h (H-1)).faces n) := by
          apply supported_mono (P := graded {s | s ∈ X.faces ∧ ∀ v ∈ s, h v < H} n) _ he
          intro s hs
          exact ⟨⟨hs.1.1, fun v hv => by have := hs.1.2 v hv; omega⟩, hs.2⟩
        have hcycle : rawBoundary (c - rawBoundary b) = 0 := by
          rw [map_sub, hz]
          have hh := LinearMap.congr_fun (rawBoundary_squared (V := V)) b
          change rawBoundary (rawBoundary b) = 0 at hh
          rw [hh, sub_self]
        obtain ⟨a, ha, hea⟩ := ih (H-1) (by omega) _ hl hcycle
        refine ⟨a+b, Submodule.add_mem _ ha ?_, ?_⟩
        · exact supported_mono (P := graded (bounded X h H).faces (n+1))
            (Q := graded X.faces (n+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) hb
        · rw [map_add, hea, sub_add_cancel]
  intro c hc hz
  apply fill (c.support.sup (fun s => s.sup h)) c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  exact ⟨⟨(hc s hs).1, fun v hv => (Finset.le_sup (f := h) hv).trans
      (Finset.le_sup (f := fun t : Finset V => t.sup h) (Finsupp.mem_support_iff.mpr hs))⟩,
    (hc s hs).2⟩

end CoboundaryExpanders.InfiniteChains.HeightReduction

end

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment InfiniteChains.BadSimplex
open InfiniteChains.HeightReduction

structure EuclideanHeight (R : Type) [CommRing R] where
  height : R → ℕ
  zero_iff : ∀ a, height a = 0 ↔ a = 0
  reduce : ∀ a b, b ≠ 0 → ∃ q, height (a-q*b) < height b

variable {R M V : Type} [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq V]

abbrev standardCoordinate {S : Type} (i : S) : S → R :=
  @Pi.single S (fun _ => R) (fun _ => inferInstance) (Classical.decEq S) i 1

lemma split_frame (f : V → M) (h : V → ℕ) (H : ℕ) (F : Finset (Bad h H))
    (hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex (complex R f) h H).faces) :
    IsFrame R (fun v : F => f v.val.val) := by
  have hi := (frame_image (R := R) f (split h H).toEmbedding
    (F.disjSum (∅ : Finset (Good h H)))).mp hF.1
  exact (frame_inl (R := R) (f ∘ split h H) F).mp hi

lemma goodLink_eq (f : V → M) (h : V → ℕ) (H : ℕ) (F : Finset (Bad h H))
    (hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex (complex R f) h H).faces)
    (r : M →ₗ[R] (F → R)) (hr : ∀ i, r (f i.val.val) = standardCoordinate (R := R) i) :
    (goodLink (splitComplex (complex R f) h H) F hF).faces =
      (complex R (fun v : Good h H => quotientProjection (fun i : F => f i.val.val) r hr (f v.val))).faces := by
  ext t
  change ((F.disjSum t).image (split h H) ∈ (complex R f).faces ∧
    ∀ v ∈ (F.disjSum t).image (split h H), h v ≤ H) ↔ _
  have bound : ∀ v ∈ (F.disjSum t).image (split h H), h v ≤ H := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    cases x with
    | inl x =>
      apply hF.2
      exact Finset.mem_image.mpr ⟨Sum.inl x, by simpa using hx, rfl⟩
    | inr x => exact (Nat.lt_of_not_ge x.property).le
  rw [and_iff_left bound]
  apply (frame_image (R := R) f (split h H).toEmbedding (F.disjSum t)).trans
  apply (frame_disjSum (R := R) (f ∘ split h H) F t).trans
  exact frame_sum_iff (fun i : F => f i.val.val) r hr (fun v : t => f v.val.val)

lemma reduced_projection_surjective (δ : EuclideanHeight R) (f : V → M)
    (hf : Function.Surjective f) (φ : M →ₗ[R] R) (H : ℕ) (hH : 0 < H)
    (F : Finset (Bad (fun v => δ.height (φ (f v))) H))
    (hF : F.disjSum (∅ : Finset (Good (fun v => δ.height (φ (f v))) H)) ∈
      (splitComplex (complex R f) (fun v => δ.height (φ (f v))) H).faces)
    (hFn : F.Nonempty) (r : M →ₗ[R] (F → R))
    (hr : ∀ i, r (f i.val.val) = standardCoordinate (R := R) i) :
    Function.Surjective (fun v : Good (fun v => δ.height (φ (f v))) H =>
      quotientProjection (fun i : F => f i.val.val) r hr (f v.val)) := by
  obtain ⟨v,hv⟩ := hFn
  let i : F := ⟨v,hv⟩
  have hp : H ≤ δ.height (φ (f v.val)) := v.property
  have hneq : φ (f v.val) ≠ 0 := by
    intro hz
    have hh := (δ.zero_iff _).mpr hz
    omega
  intro y
  obtain ⟨q,hq⟩ := δ.reduce (φ (y : M)) (φ (f v.val)) hneq
  have hmax : δ.height (φ (f v.val)) ≤ H := by
    apply hF.2
    exact Finset.mem_image.mpr ⟨Sum.inl v, by simpa using hv, rfl⟩
  obtain ⟨x,hx⟩ := hf ((y : M) - q • f v.val)
  have hgood : ¬ H ≤ δ.height (φ (f x)) := by
    rw [hx, map_sub, map_smul, smul_eq_mul]
    omega
  refine ⟨⟨x,hgood⟩, ?_⟩
  change quotientProjection (fun j : F => f j.val.val) r hr (f x) = y
  rw [hx, map_sub, map_smul]
  have hz := quotientProjection_family (fun j : F => f j.val.val) r hr i
  change quotientProjection (fun j : F => f j.val.val) r hr (f v.val) = 0 at hz
  rw [quotientProjection_ker, hz, smul_zero, sub_zero]

theorem exactIn_complex (δ : EuclideanHeight R) [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M] (f : V → M) (hf : Function.Surjective f)
    (n : ℕ) (hn : n < Module.finrank R M) : ExactIn (complex R f).faces n := by
  have ranks (d : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M]
      [Module.Free R M] [Module.Finite R M], Module.finrank R M = d →
      ∀ (V : Type) [DecidableEq V] (f : V → M), Function.Surjective f →
      ∀ n : ℕ, n < d → ExactIn (complex R f).faces n := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro M _ _ _ _ hdim V _ f hf n hn
      have hpos : 0 < Module.finrank R M := by omega
      have hidx : Nonempty (Module.Free.ChooseBasisIndex R M) := by
        apply Fintype.card_pos_iff.mp
        rw [← Module.finrank_eq_card_chooseBasisIndex]
        exact hpos
      let i := Classical.choice hidx
      let b := Module.Free.chooseBasis R M
      let φ : M →ₗ[R] R := b.coord i
      obtain ⟨a,ha⟩ := hf (b i)
      have hφa : φ (f a) = 1 := by rw [ha]; simp [φ, Module.Basis.coord_apply]
      apply HeightReduction.exactIn (complex R f) (fun v => δ.height (φ (f v))) n
      · intro c hc hz
        apply fill_zero_coordinate f φ a hφa n c _ hz
        apply supported_mono (P := graded (bounded (complex R f) (fun v => δ.height (φ (f v))) 0).faces n) _ hc
        intro s hs
        refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
        intro v hv
        exact (δ.zero_iff _).mp (Nat.eq_zero_of_le_zero (hs.1.2 v hv))
      · intro H hH F hF hFn hnF
        obtain ⟨r,hr⟩ := split_frame (R := R) f (fun v => δ.height (φ (f v))) H F hF
        have hd := frame_rank_split (fun v : F => f v.val.val) r hr
        rw [Fintype.card_coe, hdim] at hd
        have hc : 0 < F.card := Finset.card_pos.mpr hFn
        have hrlt : Module.finrank R r.ker < d := by omega
        rw [goodLink_eq f (fun v => δ.height (φ (f v))) H F hF r hr]
        apply ih (Module.finrank R r.ker) hrlt r.ker rfl
          (Good (fun v => δ.height (φ (f v))) H)
          (fun v => quotientProjection (fun i : F => f i.val.val) r hr (f v.val))
        · exact reduced_projection_surjective δ f hf φ H hH F hF hFn r hr
        · omega
  exact ranks (Module.finrank R M) M rfl V f hf n hn

def fieldHeight (K : Type) [Field K] : EuclideanHeight K where
  height a := if a = 0 then 0 else 1
  zero_iff a := by by_cases h : a = 0 <;> simp [h]
  reduce a b hb := by
    refine ⟨a / b, ?_⟩
    simp [div_mul_cancel₀ a hb, hb]

def polynomialHeight (K : Type) [Field K] : EuclideanHeight (Polynomial K) where
  height a := if a = 0 then 0 else a.natDegree+1
  zero_iff a := by by_cases h : a = 0 <;> simp [h]
  reduce a b hb := by
    refine ⟨a / b, ?_⟩
    rw [mul_comm (a/b) b, ← EuclideanDomain.mod_eq_sub_mul_div]
    by_cases hz : a % b = 0
    · simp [hz, hb]
    · have hh := Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_mod_lt a hb)
      simp only [hz, hb, ite_false]
      omega

theorem polynomial_exact (K V : Type) [Field K] [DecidableEq V] (r : ℕ)
    (f : V → (Fin r → Polynomial K)) (hf : Function.Surjective f)
    (n : ℕ) (hn : n < r) : ExactIn (complex (Polynomial K) f).faces n := by
  apply exactIn_complex (polynomialHeight K) f hf n
  simpa using hn

theorem field_exact (K V : Type) [Field K] [DecidableEq V] (r : ℕ)
    (f : V → (Fin r → K)) (hf : Function.Surjective f)
    (n : ℕ) (hn : n < r) : ExactIn (complex K f).faces n := by
  apply exactIn_complex (fieldHeight K) f hf n
  simpa using hn

end CoboundaryExpanders.Unimodular

end

end OAI
