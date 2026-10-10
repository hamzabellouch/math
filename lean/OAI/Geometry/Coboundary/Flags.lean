import OAI.Combinatorics.Coboundary.Cosets

namespace OAI

/-!
Complete flags, spherical opposition, unitriangular groups, and the flag-coset model.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.SphericalOpposition
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure CompleteFlag (K V : Type) [Field K] [AddCommGroup V] [Module K V] (N : ℕ) where
  space : Fin (N+1) → Submodule K V
  mono : Monotone space
  dimension : finrank K V = N
  rank : ∀ i, finrank K (space i) = i.val

variable {N : ℕ}

namespace CompleteFlag
variable [FiniteDimensional K V]

lemma space_zero (F : CompleteFlag K V N) : F.space 0 = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  exact F.rank 0

lemma space_last (F : CompleteFlag K V N) : F.space (Fin.last N) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [F.rank, F.dimension]
  rfl

def Opposed (F : CompleteFlag K V N) (W : Submodule K V) : Prop :=
  IsCompl W (F.space ⟨N-finrank K W, by omega⟩)

def Good (F : CompleteFlag K V N) (W : Submodule K V) : Prop :=
  0 < finrank K W ∧ finrank K W < N ∧ F.Opposed W

def complex (F : CompleteFlag K V N) : InfiniteChains.Complex (Submodule K V) where
  faces := {s | (∀ W ∈ s, F.Good W) ∧ (s : Set (Submodule K V)).Pairwise (fun W W' => W ≤ W' ∨ W' ≤ W)}
  empty_mem := by simp
  downward := by
    intro s t hs hts
    exact ⟨fun W hW => hs.1 W (hts hW), hs.2.mono hts⟩

omit [FiniteDimensional K V] in
lemma mem_faces (F : CompleteFlag K V N) (s : Finset (Submodule K V)) :
    s ∈ F.complex.faces ↔
      (∀ W ∈ s, F.Good W) ∧ (s : Set (Submodule K V)).Pairwise (fun W W' => W ≤ W' ∨ W' ≤ W) := Iff.rfl

lemma rank_le (F : CompleteFlag K V N) (W : Submodule K V) : finrank K W ≤ N := by
  simpa [F.dimension] using Submodule.finrank_le W

lemma opposed_iff_disjoint (F : CompleteFlag K V N) (W : Submodule K V) :
    F.Opposed W ↔ Disjoint W (F.space ⟨N-finrank K W, by omega⟩) := by
  apply Submodule.isCompl_iff_disjoint
  rw [F.dimension, F.rank]
  dsimp
  have := F.rank_le W
  omega

lemma opposed_disjoint_below (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (i : Fin (N+1)) (hi : i.val ≤ N-finrank K W) :
    Disjoint W (F.space i) := by
  exact (F.opposed_iff_disjoint W).mp hW |>.mono_right (F.mono hi)

def forbidden (F : CompleteFlag K V N) (W : Submodule K V) : Submodule K V :=
  W ⊔ F.space ⟨N-finrank K W-1, by omega⟩

lemma forbidden_rank (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N) :
    finrank K (F.forbidden W) = N-1 := by
  have hd := F.opposed_disjoint_below W hW ⟨N-finrank K W-1, by omega⟩ (by simp)
  have he := Submodule.finrank_sup_add_finrank_inf_eq W
    (F.space ⟨N-finrank K W-1, by omega⟩)
  rw [hd.eq_bot, finrank_bot, F.rank, add_zero] at he
  dsimp only [Fin.val_mk] at he
  change finrank K (W ⊔ F.space ⟨N-finrank K W-1, by omega⟩ : Submodule K V) = N-1
  omega

lemma forbidden_ne_top (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N) : F.forbidden W ≠ ⊤ := by
  intro e
  have he := F.forbidden_rank W hW hlt
  rw [e, finrank_top, F.dimension] at he
  omega

lemma extension_rank (F : CompleteFlag K V N) (W : Submodule K V)
    {v : V} (hv : v ∉ F.forbidden W) :
    finrank K (W ⊔ Submodule.span K {v} : Submodule K V) = finrank K W + 1 := by
  apply Submodule.finrank_sup_span_singleton
  exact fun h => hv ((show W ≤ F.forbidden W from le_sup_left) h)

lemma opposed_extension (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N)
    {v : V} (hv : v ∉ F.forbidden W) :
    F.Opposed (W ⊔ Submodule.span K {v}) := by
  let A := F.space ⟨N-finrank K W-1, by omega⟩
  have hr : finrank K (W ⊔ Submodule.span K {v} : Submodule K V) = finrank K W + 1 :=
    F.extension_rank W hv
  have ht : W ⊔ Submodule.span K {v} ⊔ A = ⊤ := by
    have hb := Submodule.finrank_sup_span_singleton hv
    rw [F.forbidden_rank W hW hlt] at hb
    have he : F.forbidden W ⊔ Submodule.span K {v} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [F.dimension]
      omega
    simpa [forbidden, A, sup_assoc, sup_comm, sup_left_comm] using he
  have hai : (⟨N-finrank K (W ⊔ Submodule.span K {v} : Submodule K V), by omega⟩ : Fin (N+1)) =
      ⟨N-finrank K W-1, by omega⟩ := by
    apply Fin.ext
    dsimp
    omega
  rw [F.opposed_iff_disjoint, hai]
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  have he := Submodule.finrank_sup_add_finrank_inf_eq (W ⊔ Submodule.span K {v}) A
  rw [ht, finrank_top, F.dimension, hr, F.rank] at he
  dsimp [A] at he ⊢
  omega

lemma good_extension (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Good W) (hlt : finrank K W + 1 < N)
    {v : V} (hv : v ∉ F.forbidden W) :
    F.Good (W ⊔ Submodule.span K {v}) := by
  refine ⟨?_, ?_, F.opposed_extension W hW.2.2 hW.2.1 hv⟩ <;>
    rw [F.extension_rank W hv] <;> omega

lemma opposed_line (F : CompleteFlag K V N) (hN : 0 < N) {v : V}
    (hv : v ∉ F.space ⟨N-1, by omega⟩) : F.Opposed (Submodule.span K {v}) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact Submodule.zero_mem _)
  rw [F.opposed_iff_disjoint]
  simpa only [finrank_span_singleton hv0] using (Submodule.disjoint_span_singleton_of_notMem hv).symm

lemma good_line (F : CompleteFlag K V N) (hN : 1 < N) {v : V}
    (hv : v ∉ F.space ⟨N-1, by omega⟩) : F.Good (Submodule.span K {v}) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact Submodule.zero_mem _)
  refine ⟨?_, ?_, F.opposed_line (by omega) hv⟩ <;>
    rw [finrank_span_singleton hv0] <;> omega

omit [FiniteDimensional K V] in
lemma opposed_sup_above (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (i : Fin (N+1)) (hi : N-finrank K W ≤ i.val) :
    W ⊔ F.space i = ⊤ := by
  apply top_unique
  rw [← hW.sup_eq_top]
  exact sup_le_sup_left (F.mono hi) W

lemma lower_rank (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (i : Fin (finrank K W+1)) :
    finrank K ((F.space ⟨N-finrank K W+i.val, by
      have := F.rank_le W
      omega⟩).comap W.subtype) = i.val := by
  rw [← Submodule.finrank_map_subtype_eq W, Submodule.map_comap_subtype]
  have he := Submodule.finrank_sup_add_finrank_inf_eq W
    (F.space ⟨N-finrank K W+i.val, by have := F.rank_le W; omega⟩)
  rw [F.opposed_sup_above W hW _ (by dsimp; omega), finrank_top,
    F.dimension, F.rank] at he
  dsimp only [Fin.val_mk] at he
  have := F.rank_le W
  omega

def lower (F : CompleteFlag K V N) (W : Submodule K V) (hW : F.Opposed W) :
    CompleteFlag K W (finrank K W) where
  space i := (F.space ⟨N-finrank K W+i.val, by have := F.rank_le W; omega⟩).comap W.subtype
  mono := by
    intro i j hij
    apply Submodule.comap_mono
    apply F.mono
    change N-finrank K W+i.val ≤ N-finrank K W+j.val
    omega
  dimension := rfl
  rank := F.lower_rank W hW

omit [FiniteDimensional K V] in
lemma disjoint_map_subtype_iff (W : Submodule K V) (A : Submodule K W) (B : Submodule K V) :
    Disjoint (A.map W.subtype) B ↔ Disjoint A (B.comap W.subtype) := by
  rw [Submodule.disjoint_def, Submodule.disjoint_def]
  constructor
  · intro h x hx hy
    apply Subtype.ext
    exact h x.val ⟨x, hx, rfl⟩ hy
  · intro h x hx hy
    obtain ⟨y, hyA, rfl⟩ := hx
    exact congrArg Subtype.val (h y hyA hy)

lemma opposed_lower_iff (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K W) :
    (F.lower W hW).Opposed A ↔ F.Opposed (A.map W.subtype) := by
  rw [(F.lower W hW).opposed_iff_disjoint, F.opposed_iff_disjoint,
    disjoint_map_subtype_iff]
  have ha := Submodule.finrank_le A
  have hw := F.rank_le W
  have eqi : (⟨N-finrank K W+(⟨finrank K W-finrank K A, by omega⟩ :
        Fin (finrank K W+1)).val, by omega⟩ : Fin (N+1)) =
      ⟨N-finrank K (A.map W.subtype), by omega⟩ := by
    apply Fin.ext
    dsimp
    rw [Submodule.finrank_map_subtype_eq]
    omega
  change Disjoint A ((F.space _).comap W.subtype) ↔ _
  rw [eqi]

lemma good_lower_map (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K W) (hA : (F.lower W hW).Good A) :
    F.Good (A.map W.subtype) := by
  refine ⟨?_, ?_, (F.opposed_lower_iff W hW A).mp hA.2.2⟩
  · simpa only [Submodule.finrank_map_subtype_eq] using hA.1
  · rw [Submodule.finrank_map_subtype_eq]
    exact lt_of_lt_of_le hA.2.1 (F.rank_le W)

lemma face_has_greatest (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) :
    ∃ W ∈ s, ∀ U ∈ s, U ≤ W := by
  obtain ⟨W, hW, hmax⟩ := s.exists_max_image (fun U => finrank K U) hne
  refine ⟨W, hW, fun U hU => ?_⟩
  by_cases he : U = W
  · exact he.le
  · rcases hs.2 hU hW he with h | h
    · exact h
    · exact (Submodule.eq_of_le_of_finrank_le h (hmax U hU)).ge

lemma sup_mem_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) : s.sup id ∈ s := by
  obtain ⟨W, hW, hmax⟩ := F.face_has_greatest s hs hne
  have he : s.sup id = W := le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := id) hW)
  exact he ▸ hW

def safeComplex (F : CompleteFlag K V N) (v : V) :
    InfiniteChains.Complex (Submodule K V) where
  faces := {s | s ∈ F.complex.faces ∧
    ∀ W ∈ s, finrank K W + 1 < N ∧ v ∉ F.forbidden W}
  empty_mem := ⟨F.complex.empty_mem, by simp⟩
  downward := fun hs hts => ⟨F.complex.downward hs.1 hts, fun W hW => hs.2 W (hts hW)⟩

def carrierApex (_ : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V)) :
    Submodule K V := s.sup id ⊔ Submodule.span K {v}

omit [FiniteDimensional K V] in
lemma carrierApex_mono (F : CompleteFlag K V N) (v : V)
    {s t : Finset (Submodule K V)} (hst : s ⊆ t) :
    F.carrierApex v s ≤ F.carrierApex v t := by
  apply sup_le_sup_right
  exact Finset.sup_mono hst

lemma carrierApex_good (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) : F.Good (F.carrierApex v s) := by
  rcases s.eq_empty_or_nonempty with he | he
  · subst s
    simpa [carrierApex] using F.good_line hN hv
  · have hm := F.sup_mem_face s hs.1 he
    exact F.good_extension (s.sup id) (hs.1.1 _ hm) (hs.2 _ hm).1 (hs.2 _ hm).2

def carrier (F : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V)) :
    Set (Finset (Submodule K V)) :=
  {t | t ∈ F.complex.faces ∧ ∀ W ∈ t, W ≤ F.carrierApex v s}

omit [FiniteDimensional K V] in
lemma self_mem_carrier (F : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) : s ∈ F.carrier v s :=
  ⟨hs.1, fun _ hW => (Finset.le_sup (f := id) hW).trans le_sup_left⟩

omit [FiniteDimensional K V] in
lemma carrier_mono (F : CompleteFlag K V N) (v : V) {s t : Finset (Submodule K V)}
    (hst : s ⊆ t) : F.carrier v s ⊆ F.carrier v t :=
  fun _ ha => ⟨ha.1, fun W hW => (ha.2 W hW).trans (F.carrierApex_mono v hst)⟩

lemma carrier_cone (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) (t : Finset (Submodule K V))
    (ht : t ∈ F.carrier v s) : insert (F.carrierApex v s) t ∈ F.carrier v s := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact F.carrierApex_good hN v hv s hs
    · exact ht.1.1 W hW
  · intro W hW U hU hne
    rcases Finset.mem_insert.mp hW with rfl | hW
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact False.elim (hne rfl)
      · exact Or.inr (ht.2 U hU)
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact Or.inl (ht.2 W hW)
      · exact ht.1.2 hW hU hne
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact le_rfl
    · exact ht.2 W hW

omit [FiniteDimensional K V] in
lemma map_comap_lower (W A : Submodule K V) (hA : A ≤ W) :
    (A.comap W.subtype).map W.subtype = A := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hA]

omit [FiniteDimensional K V] in
lemma rank_comap_lower (W A : Submodule K V) (hA : A ≤ W) :
    finrank K (A.comap W.subtype) = finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq, map_comap_lower W A hA]

lemma good_lower_comap (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K V) (hA : F.Good A) (hAW : A < W) :
    (F.lower W hW).Good (A.comap W.subtype) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rank_comap_lower W A hAW.le]
    exact hA.1
  · rw [rank_comap_lower W A hAW.le]
    exact Submodule.finrank_strictMono hAW
  · rw [F.opposed_lower_iff W hW, map_comap_lower W A hAW.le]
    exact hA.2.2

lemma lower_face_map (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (s : Finset (Submodule K W))
    (hs : s ∈ (F.lower W hW).complex.faces) :
    s.image (Submodule.map W.subtype) ∈ F.complex.faces ∧
      ∀ A ∈ s.image (Submodule.map W.subtype), A < W := by
  have hinj := Submodule.map_injective_of_injective W.injective_subtype
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact F.good_lower_map W hW B (hs.1 B hB)
  · intro A hA B hB hab
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact (hs.2 hA' hB' (fun e => hab (congrArg _ e))).imp Submodule.map_mono Submodule.map_mono
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    refine lt_of_le_of_ne ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact y.property
    · intro he
      have hr := congrArg (fun U : Submodule K V => finrank K U) he
      rw [Submodule.finrank_map_subtype_eq] at hr
      exact (ne_of_lt (hs.1 B hB).2.1) hr

lemma lower_face_comap (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hsW : ∀ A ∈ s, A < W) :
    s.image (Submodule.comap W.subtype) ∈ (F.lower W hW).complex.faces := by
  refine ⟨?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact F.good_lower_comap W hW B (hs.1 B hB) (hsW B hB)
  · intro A hA B hB hab
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact (hs.2 hA' hB' (fun e => hab (congrArg _ e))).imp Submodule.comap_mono Submodule.comap_mono

omit [FiniteDimensional K V] in
lemma comap_injOn_lower (W : Submodule K V) (s : Finset (Submodule K V))
    (hs : ∀ A ∈ s, A ≤ W) : Set.InjOn (Submodule.comap W.subtype) (s : Set (Submodule K V)) := by
  intro A hA B hB he
  have hm := congrArg (Submodule.map W.subtype) he
  rwa [map_comap_lower W A (hs A hA), map_comap_lower W B (hs B hB)] at hm

lemma hyperplane_link_lower (F : CompleteFlag K V N) (W : Submodule K V)
    (hr : finrank K W = N-1) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hW : W ∈ s) :
    ∀ A ∈ s.erase W, A < W := by
  intro A hA
  obtain ⟨hne, hAs⟩ := Finset.mem_erase.mp hA
  rcases hs.2 hAs hW hne with h | h
  · exact lt_of_le_of_ne h hne
  · have he : W = A := Submodule.eq_of_le_of_finrank_le h (by
      have ha := (hs.1 A hAs).2.1
      omega)
    exact False.elim (hne he.symm)

omit [FiniteDimensional K V] in
lemma insert_greatest_face (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Good W) (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces)
    (hsW : ∀ A ∈ s, A ≤ W) : insert W s ∈ F.complex.faces := by
  refine ⟨?_, ?_⟩
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAs
    · exact hW
    · exact hs.1 A hAs
  · intro A hA B hB hab
    rcases Finset.mem_insert.mp hA with heA | hAs
    · subst A
      rcases Finset.mem_insert.mp hB with heB | hBs
      · exact False.elim (hab heB.symm)
      · exact Or.inr (hsW B hBs)
    · rcases Finset.mem_insert.mp hB with heB | hBs
      · subst B
        exact Or.inl (hsW A hAs)
      · exact hs.2 hAs hBs hab

end CompleteFlag

theorem exists_vector_avoiding [Fintype K] [Fintype V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] (P : ι → Submodule K V)
    (hP : ∀ i, P i ≠ ⊤) (hι : Fintype.card ι < Fintype.card K)
    (hdim : 0 < finrank K V) : ∃ v : V, ∀ i, v ∉ P i := by
  classical
  let bad : Finset V := Finset.univ.biUnion (fun i => (P i : Set V).toFinset)
  have hbound (i : ι) : (P i : Set V).toFinset.card ≤
      Fintype.card K ^ (finrank K V - 1) := by
    rw [Set.toFinset_card]
    change Fintype.card (P i) ≤ _
    rw [Module.card_eq_pow_finrank (K := K)]
    exact Nat.pow_le_pow_right Fintype.card_pos (by have := Submodule.finrank_lt (hP i); omega)
  have hcard : bad.card < Finset.univ.card (α := V) := by
    calc
      bad.card ≤ ∑ i : ι, (P i : Set V).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, Fintype.card K ^ (finrank K V - 1) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = Fintype.card ι * Fintype.card K ^ (finrank K V - 1) := by simp
      _ < Fintype.card K * Fintype.card K ^ (finrank K V - 1) :=
        Nat.mul_lt_mul_of_pos_right hι (Nat.pow_pos Fintype.card_pos)
      _ = Fintype.card K ^ finrank K V := by
        rw [← pow_succ']
        congr 1
        omega
      _ = Finset.univ.card (α := V) := by rw [Finset.card_univ, Module.card_eq_pow_finrank (K := K) (V := V)]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨v, fun i hi => hv ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hi⟩

theorem exists_vector_avoiding_finset [Fintype K] [Fintype V] [FiniteDimensional K V]
    (S : Finset (Submodule K V)) (hS : ∀ P ∈ S, P ≠ ⊤)
    (hcard : S.card < Fintype.card K) (hdim : 0 < finrank K V) :
    ∃ v : V, ∀ P ∈ S, v ∉ P := by
  classical
  obtain ⟨v, hv⟩ := exists_vector_avoiding (fun P : S => P.val)
    (fun P => hS P.val P.property) (by simpa using hcard) hdim
  exact ⟨v, fun P hP => hv ⟨P, hP⟩⟩

theorem exists_common_good_line [Fintype K] [Fintype V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] [Nonempty ι] (F : ι → CompleteFlag K V N)
    (hN : 1 < N) (hι : Fintype.card ι < Fintype.card K) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, (F i).Good (Submodule.span K {v}) := by
  classical
  let base : ι := Classical.choice inferInstance
  obtain ⟨v, hv⟩ := exists_vector_avoiding
    (fun i => (F i).space ⟨N-1, by omega⟩) (fun i => by
      intro he
      have hr := (F i).rank ⟨N-1, by omega⟩
      rw [he, finrank_top, (F i).dimension] at hr
      dsimp at hr
      omega) hι (by rw [(F base).dimension]; omega)
  refine ⟨v, ?_, fun i => (F i).good_line hN (hv i)⟩
  intro he
  exact hv base (by rw [he]; exact Submodule.zero_mem _)

end CoboundaryExpanders.SphericalOpposition

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma safe_filling (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (r : ℕ) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded (F.safeComplex v).faces r)) (hz : rawBoundary c = 0) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+1)) ∧
      rawBoundary b = c ∧ size b ≤ carrierBound r * size c := by
  classical
  let T := carrierMap (F.carrierApex v)
  have hsingle (s : Finset (Submodule K V)) (hs : s ∈ (F.safeComplex v).faces) :
      T (Finsupp.single s 1) ∈ supported (graded F.complex.faces (s.card+1)) := by
    have hb := carrierFill_supported (F.safeComplex v) (F.carrier v) (F.carrierApex v)
      (F.self_mem_carrier v) (fun _ _ _ h => F.carrier_mono v h)
      (F.carrier_cone hN v hv) s hs
    have hcarr : graded (F.carrier v s) (s.card+1) ⊆ graded F.complex.faces (s.card+1) :=
      fun _ ht => ⟨ht.1.1, ht.2⟩
    simpa [T] using supported_mono hcarr hb
  refine ⟨T c, ?_, ?_, ?_⟩
  · apply map_supported T (graded (F.safeComplex v).faces r) _ _ c hc
    intro s hs a
    have he : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [he, map_smul]
    apply Submodule.smul_mem
    simpa [hs.2] using hsingle s hs.1
  · have hh := LinearMap.congr_fun (carrierMap_contraction (F.carrierApex v)) c
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hz, map_zero, add_zero] using hh
  · apply size_map_le T (graded (F.safeComplex v).faces r) (carrierBound r) _ c hc
    intro s hs
    simpa [T, hs.2] using carrierFill_size (F.carrierApex v) s

def TopBad (F : CompleteFlag K V N) (W : Submodule K V) : Prop :=
  F.Good W ∧ finrank K W = N-1

lemma no_top_filling [Fintype K] [Fintype V] (F : CompleteFlag K V N)
    (hN : 1 < N) (r : ℕ) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded (allowed F.complex F.TopBad ∅).faces r))
    (hz : rawBoundary c = 0) (hq : 1+r*size c < Fintype.card K) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+1)) ∧
      rawBoundary b = c ∧ size b ≤ carrierBound r * size c := by
  classical
  have hvert (W : Submodule K V) (hW : W ∈ vertices c) :
      F.Good W ∧ finrank K W + 1 < N := by
    obtain ⟨s, hs, hWs⟩ := Finset.mem_biUnion.mp hW
    have hsf := (mem_supported _ _).mp hc s (Finsupp.mem_support_iff.mp hs)
    have hg := hsf.1.1.1 W hWs
    have hne : finrank K W ≠ N-1 := fun hr =>
      Finset.notMem_empty W (hsf.1.2 W hWs ⟨hg, hr⟩)
    exact ⟨hg, by have := hg.2.1; omega⟩
  let Z : Submodule K V := F.space ⟨N-1, by omega⟩
  let S := insert Z ((vertices c).image F.forbidden)
  have hS : ∀ P ∈ S, P ≠ ⊤ := by
    intro P hP
    rcases Finset.mem_insert.mp hP with he | hP
    · subst P
      intro he
      have hr := F.rank ⟨N-1, by omega⟩
      change finrank K Z = N-1 at hr
      rw [he, finrank_top, F.dimension] at hr
      omega
    · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hP
      exact F.forbidden_ne_top W (hvert W hW).1.2.2 (hvert W hW).1.2.1
  have hcard : S.card < Fintype.card K := by
    have hi := Finset.card_insert_le Z ((vertices c).image F.forbidden)
    have him := Finset.card_image_le (s := vertices c) (f := F.forbidden)
    have hv := vertices_card_le (allowed F.complex F.TopBad ∅).faces r c hc
    dsimp [S]
    omega
  obtain ⟨v, hv⟩ := exists_vector_avoiding_finset S hS hcard (by rw [F.dimension]; omega)
  apply F.safe_filling hN v (hv Z (Finset.mem_insert_self _ _)) r c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1.1, ?_⟩, (hc s hs).2⟩
  intro W hW
  have hWv := mem_vertices c s hs W hW
  refine ⟨(hvert W hWv).2, ?_⟩
  exact hv (F.forbidden W) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨W, hWv, rfl⟩))

lemma hyperplane_link_filling (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.TopBad W) (n R r : ℕ)
    (H : BoundedCone (F.lower W hW.1.2.2).complex n R) (hr : r ≤ n)
    (c : Raw (Submodule K V)) (hc : c ∈ supported (graded F.complex.faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ b : Raw (Submodule K V),
      b ∈ supported (graded {s | s ∈ F.complex.faces ∧
        (∀ A ∈ s, ¬F.TopBad A) ∧ insert W s ∈ F.complex.faces} (r+1)) ∧
      rawBoundary b = link W c ∧ size b ≤ R * size c := by
  classical
  let L := F.lower W hW.1.2.2
  let P : Set (Finset (Submodule K V)) :=
    {s | s ∈ F.complex.faces ∧ ∀ A ∈ s, A < W}
  let f : Submodule K W → Submodule K V := Submodule.map W.subtype
  let g : Submodule K V → Submodule K W := Submodule.comap W.subtype
  have hinj : Function.Injective f := Submodule.map_injective_of_injective W.injective_subtype
  have hl : link W c ∈ supported (graded P r) := by
    apply link_graded W F.complex.faces P r _ c hc
    intro s hs hWs
    exact ⟨F.complex.downward hs (Finset.erase_subset _ _), F.hyperplane_link_lower W hW.2 s hs hWs⟩
  let a := relabel g (link W c)
  have ha : a ∈ supported (graded L.complex.faces r) := by
    apply relabel_graded g P L.complex.faces r _ _ _ hl
    · intro s hs
      exact F.lower_face_comap W hW.1.2.2 s hs.1 hs.2
    · intro s hs
      exact comap_injOn_lower W s (fun A hA => (hs.2 A hA).le)
  have hret : relabel f a = link W c := by
    apply relabel_retraction f g (graded P r) _ _ hl
    intro s hs A hA
    exact map_comap_lower W A (hs.1.2 A hA).le
  have haz : rawBoundary a = 0 := by
    apply relabel_injective f hinj
    rw [map_zero]
    have nat := LinearMap.congr_fun (relabel_boundary f hinj) a
    change rawBoundary (relabel f a) = relabel f (rawBoundary a) at nat
    rw [← nat, hret, link_cycle W c hz]
  let b := relabel f (H.hom a)
  refine ⟨b, ?_, ?_, ?_⟩
  · apply relabel_graded f L.complex.faces _ (r+1) _ (fun _ _ => hinj.injOn)
      (H.hom a) (H.map_graded r hr a ha)
    intro s hs
    have hm := F.lower_face_map W hW.1.2.2 s hs
    refine ⟨hm.1, ?_, F.insert_greatest_face W hW.1 _ hm.1 (fun A hA => (hm.2 A hA).le)⟩
    intro A hA hbad
    have hrank := Submodule.finrank_strictMono (hm.2 A hA)
    have hArank := hbad.2
    change finrank K A < finrank K W at hrank
    rw [hW.2, hArank] at hrank
    exact Nat.lt_irrefl _ hrank
  · have nat := LinearMap.congr_fun (relabel_boundary f hinj) (H.hom a)
    change rawBoundary b = relabel f (rawBoundary (H.hom a)) at nat
    rw [nat, H.fills r hr a ha haz, hret]
  · calc
      size b ≤ size (H.hom a) := relabel_size f _
      _ ≤ R * size a := H.size_apply r hr a ha
      _ ≤ R * size (link W c) := Nat.mul_le_mul_left R (relabel_size g _)
      _ ≤ R * size c := Nat.mul_le_mul_left R (link_size W c)

def eliminationBound (R r S : ℕ) : ℕ := (2*R+2)^(r*S)*S

def fillingBound (R r S : ℕ) : ℕ := (1+carrierBound r)*eliminationBound R r S

def fieldBound (R r S : ℕ) : ℕ := 1+r*eliminationBound R r S

lemma small_filling [Fintype K] [Fintype V] (F : CompleteFlag K V N)
    (hN : 1 < N) (n R r S : ℕ)
    (H : ∀ W, ∀ hW : F.TopBad W, BoundedCone (F.lower W hW.1.2.2).complex n R)
    (hr : r ≤ n) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded F.complex.faces (r+1))) (hz : rawBoundary c = 0)
    (hsize : size c ≤ S) (hq : fieldBound R (r+1) S < Fintype.card K) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+2)) ∧
      rawBoundary b = c ∧ size b ≤ fillingBound R (r+1) S := by
  classical
  let A := (vertices c).filter F.TopBad
  have hA : ∀ W ∈ A, F.TopBad W := fun _ h => (Finset.mem_filter.mp h).2
  have hcA : c ∈ supported (graded (allowed F.complex F.TopBad A).faces (r+1)) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    refine ⟨⟨(hc s hs).1, ?_⟩, (hc s hs).2⟩
    intro W hW hbad
    exact Finset.mem_filter.mpr ⟨mem_vertices c s hs W hW, hbad⟩
  obtain ⟨e, c', he, hc', hz', hec, htotal⟩ :=
    removeBad F.complex F.TopBad (r+1) R
      (fun W hW c hc hz => F.hyperplane_link_filling W hW n R r (H W hW) hr c hc hz)
      A hA c hcA hz
  have hAc : A.card ≤ (r+1)*S :=
    (Finset.card_filter_le _ _).trans ((vertices_card_le F.complex.faces (r+1) c hc).trans
      (Nat.mul_le_mul_left (r+1) hsize))
  have hE : size e + size c' ≤ eliminationBound R (r+1) S := by
    apply htotal.trans
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < 2*R+2) hAc) hsize
  have hcE : size c' ≤ eliminationBound R (r+1) S := (Nat.le_add_left _ _).trans hE
  have hq' : 1+(r+1)*size c' < Fintype.card K :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left (r+1) hcE) 1).trans_lt hq
  obtain ⟨b, hb, hdb, hsz⟩ := F.no_top_filling hN (r+1) c' hc' hz' hq'
  refine ⟨e+b, Submodule.add_mem _ he hb, ?_, ?_⟩
  · rw [map_add, hdb, hec]
  · have hadd := size_add_le e b
    have hbE := hsz.trans (Nat.mul_le_mul_left (carrierBound (r+1)) hcE)
    dsimp [fillingBound]
    nlinarith

theorem exists_uniform_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K]
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V],
      ∀ (N : ℕ) (F : CompleteFlag K V N), n+2 ≤ N → Q < Fintype.card K →
        Nonempty (BoundedCone F.complex n R) := by
  classical
  induction n with
  | zero =>
    refine ⟨1, 1, ?_⟩
    intro K _ _ V _ _ _ _ N F hN hq
    obtain ⟨v, hv, hg⟩ := exists_common_good_line (ι := Unit) (fun _ => F) (by omega)
      (by simpa using hq)
    refine ⟨BoundedCone.initial F.complex (Submodule.span K {v}) ?_⟩
    refine ⟨?_, ?_⟩
    · intro W hW
      have he : W = Submodule.span K {v} := Finset.mem_singleton.mp hW
      exact he ▸ hg ()
    · simp
  | succ n ih =>
    obtain ⟨Q, R, hcones⟩ := ih
    let S := 1+R*(n+1)
    refine ⟨max Q (fieldBound R (n+1) S), max R (fillingBound R (n+1) S), ?_⟩
    intro K _ _ V _ _ _ _ N F hN hq
    have hqQ : Q < Fintype.card K := (Nat.le_max_left _ _).trans_lt hq
    have hqF : fieldBound R (n+1) S < Fintype.card K := (Nat.le_max_right _ _).trans_lt hq
    let H : BoundedCone F.complex n R := (hcones K V N F (by omega) hqQ).some
    have hlower (W : Submodule K V) (hW : F.TopBad W) :
        Nonempty (BoundedCone (F.lower W hW.1.2.2).complex n R) := by
      apply hcones K W (finrank K W) (F.lower W hW.1.2.2)
      · rw [hW.2]
        omega
      · exact hqQ
    exact ⟨H.extend (fillingBound R (n+1) S)
      (fun c hc hz hs => F.small_filling (by omega) n R n S
        (fun W hW => (hlower W hW).some) le_rfl c hc hz hs hqF)⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone

theorem uniform_spherical_exactness (n : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K]
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V],
      ∀ (N : ℕ) (F : CompleteFlag K V N), n+2 ≤ N → Q < Fintype.card K →
        ∀ r ≤ n, ExactIn F.complex.faces r := by
  classical
  obtain ⟨Q, R, h⟩ := exists_uniform_cones n
  refine ⟨Q, ?_⟩
  intro K _ _ V _ _ _ _ N F hN hq r hr
  exact (h K V N F hN hq).some.exactIn r hr

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def Opposite (F E : CompleteFlag K V N) : Prop :=
  ∀ i : Fin (N+1), IsCompl (F.space i) (E.space ⟨N-i.val, by omega⟩)

omit [FiniteDimensional K V] in
lemma opposite_symm {F E : CompleteFlag K V N} (h : F.Opposite E) : E.Opposite F := by
  intro i
  have hh := (h ⟨N-i.val, by omega⟩).symm
  convert hh using 1
  congr 1
  apply Fin.ext
  dsimp
  omega

lemma opposite_line_rank {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin N) :
    finrank K (F.space i.succ ⊓ E.space ⟨N-i.val, by omega⟩ : Submodule K V) = 1 := by
  have hs : F.space i.succ ⊔ E.space ⟨N-i.val, by omega⟩ = ⊤ := by
    apply top_unique
    rw [← (h i.castSucc).sup_eq_top]
    exact sup_le_sup_right (F.mono (by simp [Fin.le_def])) _
  have hh := Submodule.finrank_sup_add_finrank_inf_eq (F.space i.succ)
    (E.space ⟨N-i.val, by omega⟩)
  rw [hs, finrank_top, F.dimension, F.rank, E.rank] at hh
  dsimp at hh
  omega

lemma opposite_line_vector {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin N) :
    ∃ v : V, v ∈ F.space i.succ ∧ v ∈ E.space ⟨N-i.val, by omega⟩ ∧
      v ∉ F.space i.castSucc := by
  have hn : (F.space i.succ ⊓ E.space ⟨N-i.val, by omega⟩ : Submodule K V) ≠ ⊥ := by
    intro he
    have hh := opposite_line_rank h i
    rw [he, finrank_bot] at hh
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨v,hv.1,hv.2,?_⟩
  intro hvF
  have hz : v ∈ (F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ : Submodule K V) :=
    ⟨hvF,hv.2⟩
  have hb : F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ = ⊥ :=
    (h i.castSucc).inf_eq_bot
  rw [hb] at hz
  exact hv0 hz

lemma step_span (F : CompleteFlag K V N) (i : Fin N) {v : V}
    (hv : v ∈ F.space i.succ) (hnot : v ∉ F.space i.castSucc) :
    F.space i.succ = F.space i.castSucc ⊔ span K {v} := by
  have hv0 : v ≠ 0 := fun he => hnot (he ▸ (F.space i.castSucc).zero_mem)
  have hd : Disjoint (F.space i.castSucc) (span K {v}) := disjoint_span_singleton_of_notMem hnot
  apply (Submodule.eq_of_le_of_finrank_eq
    (sup_le (F.mono (by simp [Fin.le_def])) (span_le.mpr (by simpa using hv))) ?_).symm
  have hh := finrank_sup_add_finrank_inf_eq (F.space i.castSucc) (span K {v})
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv0, F.rank] at hh
  simpa only [F.rank, Fin.val_succ, Fin.val_castSucc] using hh

theorem exists_adapted_basis {F E : CompleteFlag K V N} (h : F.Opposite E) :
    ∃ b : Basis (Fin N) K V, ∀ i : Fin N,
      b i ∈ F.space i.succ ∧ b i ∈ E.space ⟨N-i.val, by omega⟩ := by
  choose v hvF hvE hvnot using opposite_line_vector h
  have hs : ∀ i : Fin (N+1), F.space i ≤ span K (Set.range v) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [F.space_zero]; exact bot_le
    | succ i hi =>
      rw [F.step_span i (hvF i) (hvnot i)]
      exact sup_le hi (span_le.mpr (by
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact subset_span (Set.mem_range_self i)))
  have htop : ⊤ ≤ span K (Set.range v) := by simpa [F.space_last] using hs (Fin.last N)
  let b := basisOfTopLeSpanOfCardEqFinrank v htop (by simpa using F.dimension.symm)
  refine ⟨b, fun i => ?_⟩
  simpa [b] using And.intro (hvF i) (hvE i)

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def prefixIndex (i : Fin (N+1)) (j : Fin i.val) : Fin N := ⟨j.val, by omega⟩
def suffixIndex (i : Fin (N+1)) (j : Fin (N-i.val)) : Fin N := ⟨i.val+j.val, by omega⟩

lemma prefixIndex_injective (i : Fin (N+1)) : Function.Injective (prefixIndex i) := by
  intro a b h
  apply Fin.ext
  simpa only [prefixIndex] using congrArg (fun j : Fin N => j.val) h

lemma suffixIndex_injective (i : Fin (N+1)) : Function.Injective (suffixIndex i) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [suffixIndex] at hh
  omega

lemma adapted_prefix (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ j : Fin N, b j ∈ F.space j.succ) (i : Fin (N+1)) :
    span K (Set.range (fun j : Fin i.val => b (prefixIndex i j))) = F.space i := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact F.mono (by change j.val+1 ≤ i.val; omega) (hb (prefixIndex i j))
  · simpa only [Function.comp_def, Fintype.card_fin, F.rank] using
      finrank_span_eq_card (b.linearIndependent.comp _ (prefixIndex_injective i))

lemma adapted_suffix (E : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ j : Fin N, b j ∈ E.space ⟨N-j.val, by omega⟩) (i : Fin (N+1)) :
    span K (Set.range (fun j : Fin (N-i.val) => b (suffixIndex i j))) =
      E.space ⟨N-i.val, by omega⟩ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact E.mono (by change N-(i.val+j.val) ≤ N-i.val; omega) (hb (suffixIndex i j))
  · simpa only [Function.comp_def, Fintype.card_fin, E.rank] using
      finrank_span_eq_card (b.linearIndependent.comp _ (suffixIndex_injective i))

omit [FiniteDimensional K V] in
lemma basis_equiv_span_range {α : Type} (b b' : Basis (Fin N) K V) (v : α → Fin N) :
    (span K (Set.range (fun a => b (v a)))).map (b.equiv b' (Equiv.refl _)).toLinearMap =
      span K (Set.range (fun a => b' (v a))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]

theorem exists_flag_stabilizing_equiv {F E E' : CompleteFlag K V N}
    (h : F.Opposite E) (h' : F.Opposite E') :
    ∃ e : V ≃ₗ[K] V,
      (∀ i, (F.space i).map e.toLinearMap = F.space i) ∧
      (∀ i, (E.space i).map e.toLinearMap = E'.space i) := by
  obtain ⟨b,hb⟩ := exists_adapted_basis h
  obtain ⟨b',hb'⟩ := exists_adapted_basis h'
  refine ⟨b.equiv b' (Equiv.refl _), ?_, ?_⟩
  · intro i
    calc
      (F.space i).map _ = (span K (Set.range (fun j : Fin i.val => b (prefixIndex i j)))).map _ := by
        congr 1
        exact (adapted_prefix F b (fun j => (hb j).1) i).symm
      _ = span K (Set.range (fun j : Fin i.val => b' (prefixIndex i j))) := basis_equiv_span_range b b' _
      _ = F.space i := adapted_prefix F b' (fun j => (hb' j).1) i
  · intro i
    let k : Fin (N+1) := ⟨N-i.val, by omega⟩
    have he : (⟨N-k.val, by omega⟩ : Fin (N+1)) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    rw [← he, ← adapted_suffix E b (fun j => (hb j).2) k,
      basis_equiv_span_range, adapted_suffix E' b' (fun j => (hb' j).2) k]

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma opposed_bot (F : CompleteFlag K V N) : F.Opposed ⊥ := by
  unfold Opposed
  simp only [finrank_bot, Nat.sub_zero]
  have hh : (⟨N, by omega⟩ : Fin (N+1)) = Fin.last N := rfl
  rw [hh, F.space_last]
  exact isCompl_bot_top

lemma opposed_top (F : CompleteFlag K V N) : F.Opposed ⊤ := by
  unfold Opposed
  simp only [finrank_top, F.dimension, Nat.sub_self]
  rw [show (⟨0, by omega⟩ : Fin (N+1)) = 0 from rfl, F.space_zero]
  exact isCompl_top_bot

lemma extend_opposed (F : CompleteFlag K V N) (A : Submodule K V) (hA : F.Opposed A)
    (j : ℕ) (hAj : finrank K A ≤ j) (hj : j ≤ N) :
    ∃ W : Submodule K V, A ≤ W ∧ finrank K W = j ∧ F.Opposed W := by
  have hd := F.opposed_disjoint_below A hA ⟨N-j, by omega⟩ (by dsimp; omega)
  obtain ⟨W,hAW,hW⟩ := hd.exists_isCompl
  have hr : finrank K W = j := by
    have hh := finrank_sup_add_finrank_inf_eq W (F.space ⟨N-j, by omega⟩)
    rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_bot, add_zero, finrank_top,
      F.dimension, F.rank] at hh
    dsimp at hh
    omega
  refine ⟨W,hAW,hr,?_⟩
  unfold Opposed
  simpa only [hr] using hW

lemma interval_opposed (F : CompleteFlag K V N) (A B : Submodule K V)
    (hA : F.Opposed A) (hB : F.Opposed B) (hAB : A ≤ B)
    (j : ℕ) (hAj : finrank K A ≤ j) (hjB : j ≤ finrank K B) :
    ∃ W : Submodule K V, A ≤ W ∧ W ≤ B ∧ finrank K W = j ∧ F.Opposed W := by
  have hAc : (F.lower B hB).Opposed (A.comap B.subtype) := by
    rw [F.opposed_lower_iff B hB, map_comap_lower B A hAB]
    exact hA
  obtain ⟨W,hAW,hr,hW⟩ := (F.lower B hB).extend_opposed (A.comap B.subtype) hAc j
    (by simpa only [rank_comap_lower B A hAB] using hAj) hjB
  refine ⟨W.map B.subtype, ?_, Submodule.map_subtype_le B W, ?_,
    (F.opposed_lower_iff B hB W).mp hW⟩
  · rw [← map_comap_lower B A hAB]
    exact Submodule.map_mono hAW
  · simpa only [Submodule.finrank_map_subtype_eq] using hr

lemma rank_injective_on_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) : Set.InjOn (fun W : Submodule K V => finrank K W) s := by
  intro A hA B hB hr
  by_cases he : A = B
  · exact he
  · rcases hs.2 hA hB he with hAB | hBA
    · exact Submodule.eq_of_le_of_finrank_eq hAB hr
    · exact (Submodule.eq_of_le_of_finrank_eq hBA hr.symm).symm

lemma face_order_of_rank_le (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) {A B : Submodule K V} (hA : A ∈ s) (hB : B ∈ s)
    (hr : finrank K A ≤ finrank K B) : A ≤ B := by
  by_cases he : A = B
  · exact he.le
  · rcases hs.2 hA hB he with hAB | hBA
    · exact hAB
    · exact (Submodule.eq_of_le_of_finrank_le hBA hr).ge

lemma face_has_least (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) :
    ∃ W ∈ s, ∀ U ∈ s, W ≤ U := by
  obtain ⟨W,hW,hmin⟩ := s.exists_min_image (fun U => finrank K U) hne
  exact ⟨W,hW,fun U hU => F.face_order_of_rank_le s hs hW hU (hmin U hU)⟩

lemma face_lower_bound_at (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (j : ℕ) (hj : 0 < j) :
    ∃ A : Submodule K V, F.Opposed A ∧ finrank K A < j ∧
      (∀ U ∈ s, finrank K U < j → U ≤ A) ∧ (∀ U ∈ s, j ≤ finrank K U → A ≤ U) ∧ (A = ⊥ ∨ A ∈ s) := by
  classical
  let t := s.filter (fun W : Submodule K V => finrank K W < j)
  by_cases ht : t.Nonempty
  · obtain ⟨A,hA,hmax⟩ := F.face_has_greatest t (F.complex.downward hs (Finset.filter_subset _ _)) ht
    obtain ⟨hAs,hAr⟩ := Finset.mem_filter.mp hA
    refine ⟨A,(hs.1 A hAs).2.2,hAr,fun U hU hr => hmax U (Finset.mem_filter.mpr ⟨hU,hr⟩),?_,Or.inr hAs⟩
    intro U hU hr
    exact F.face_order_of_rank_le s hs hAs hU (by omega)
  · refine ⟨⊥,F.opposed_bot, by simpa only [finrank_bot], ?_, fun _ _ _ => bot_le, Or.inl rfl⟩
    intro U hU hr
    exact False.elim (ht ⟨U,Finset.mem_filter.mpr ⟨hU,hr⟩⟩)

lemma face_upper_bound_at (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (j : ℕ) (hj : j < N) :
    ∃ B : Submodule K V, F.Opposed B ∧ j < finrank K B ∧
      (∀ U ∈ s, j < finrank K U → B ≤ U) ∧ (∀ U ∈ s, finrank K U ≤ j → U ≤ B) ∧ (B = ⊤ ∨ B ∈ s) := by
  classical
  let t := s.filter (fun W : Submodule K V => j < finrank K W)
  by_cases ht : t.Nonempty
  · obtain ⟨B,hB,hmin⟩ := F.face_has_least t (F.complex.downward hs (Finset.filter_subset _ _)) ht
    obtain ⟨hBs,hBr⟩ := Finset.mem_filter.mp hB
    refine ⟨B,(hs.1 B hBs).2.2,hBr,fun U hU hr => hmin U (Finset.mem_filter.mpr ⟨hU,hr⟩),?_,Or.inr hBs⟩
    intro U hU hr
    exact F.face_order_of_rank_le s hs hU hBs (by omega)
  · refine ⟨⊤,F.opposed_top, by simpa only [finrank_top,F.dimension], ?_, fun _ _ _ => le_top, Or.inl rfl⟩
    intro U hU hr
    exact False.elim (ht ⟨U,Finset.mem_filter.mpr ⟨hU,hr⟩⟩)

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma insert_rank (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (j : ℕ) (hj0 : 0 < j) (hjN : j < N) :
    ∃ t : Finset (Submodule K V), t ∈ F.complex.faces ∧ s ⊆ t ∧
      ∃ W ∈ t, finrank K W = j := by
  classical
  by_cases hex : ∃ W ∈ s, finrank K W = j
  · exact ⟨s,hs,Finset.Subset.refl s,hex⟩
  obtain ⟨A,hA,hrA,hAl,hAu,hlocA⟩ := F.face_lower_bound_at s hs j hj0
  obtain ⟨B,hB,hrB,hBl,hBu,hlocB⟩ := F.face_upper_bound_at s hs j hjN
  have hAB : A ≤ B := by
    rcases hlocA with rfl | hAs
    · exact bot_le
    · exact hBu A hAs hrA.le
  obtain ⟨W,hAW,hWB,hrW,hW⟩ := F.interval_opposed A B hA hB hAB j hrA.le hrB.le
  have hcomp (U : Submodule K V) (hU : U ∈ s) : U ≤ W ∨ W ≤ U := by
    rcases lt_trichotomy (finrank K U) j with hr | hr | hr
    · exact Or.inl ((hAl U hU hr).trans hAW)
    · exact False.elim (hex ⟨U,hU,hr⟩)
    · exact Or.inr (hWB.trans (hBl U hU hr))
  refine ⟨insert W s,?_,Finset.subset_insert _ _,W,Finset.mem_insert_self _ _,hrW⟩
  constructor
  · intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact ⟨by omega,by omega,hW⟩
    · exact hs.1 U hU
  · intro U hU U' hU' hne
    rcases Finset.mem_insert.mp hU with hUW | hUs
    · subst U
      rcases Finset.mem_insert.mp hU' with hU'W | hU's
      · subst U'; exact False.elim (hne rfl)
      · exact (hcomp U' hU's).symm
    · rcases Finset.mem_insert.mp hU' with hU'W | hU's
      · subst U'; exact hcomp U hUs
      · exact hs.2 hUs hU's hne

lemma exists_extend_ranks (F : CompleteFlag K V N) (I : Finset ℕ)
    (hI : ∀ j ∈ I, 0 < j ∧ j < N) (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces) :
    ∃ t : Finset (Submodule K V), t ∈ F.complex.faces ∧ s ⊆ t ∧
      ∀ j ∈ I, ∃ W ∈ t, finrank K W = j := by
  classical
  induction I using Finset.induction generalizing s with
  | empty => exact ⟨s,hs,Finset.Subset.refl s,by simp⟩
  | @insert a I ha ih =>
    obtain ⟨t,ht,hst,hfull⟩ := ih (fun j hj => hI j (Finset.mem_insert_of_mem hj)) s hs
    obtain ⟨u,hu,htu,hua⟩ := F.insert_rank t ht a
      (hI a (Finset.mem_insert_self _ _)).1 (hI a (Finset.mem_insert_self _ _)).2
    refine ⟨u,hu,hst.trans htu,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hua
    · obtain ⟨W,hW,hr⟩ := hfull j hj
      exact ⟨W,htu hW,hr⟩

def FullFace (F : CompleteFlag K V N) (s : Finset (Submodule K V)) : Prop :=
  s ∈ F.complex.faces ∧ ∀ j, 0 < j → j < N → ∃ W ∈ s, finrank K W = j

lemma exists_full_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) : ∃ t, F.FullFace t ∧ s ⊆ t := by
  obtain ⟨t,ht,hst,hfull⟩ := F.exists_extend_ranks (Finset.Ioo 0 N)
    (fun _ hj => Finset.mem_Ioo.mp hj) s hs
  exact ⟨t,⟨ht,fun j hj0 hjN => hfull j (Finset.mem_Ioo.mpr ⟨hj0,hjN⟩)⟩,hst⟩

lemma fullFace_card (F : CompleteFlag K V N) (s : Finset (Submodule K V)) (hs : F.FullFace s) :
    s.card = N-1 := by
  classical
  have he : s.image (fun W : Submodule K V => finrank K W) = Finset.Ioo 0 N := by
    ext j
    constructor
    · intro hj
      obtain ⟨W,hW,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_Ioo.mpr ⟨(hs.1.1 W hW).1,(hs.1.1 W hW).2.1⟩
    · intro hj
      obtain ⟨W,hW,hr⟩ := hs.2 j (Finset.mem_Ioo.mp hj).1 (Finset.mem_Ioo.mp hj).2
      exact Finset.mem_image.mpr ⟨W,hW,hr⟩
  have hc := Finset.card_image_of_injOn (F.rank_injective_on_face s hs.1)
  rw [he] at hc
  simpa using hc.symm

lemma fullFace_of_card (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hc : s.card = N-1) : F.FullFace s := by
  obtain ⟨t,ht,hst⟩ := F.exists_full_face s hs
  have he : s = t := Finset.eq_of_subset_of_card_le hst (by rw [hc,F.fullFace_card t ht])
  exact he ▸ ht

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma exists_flag_stages (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : F.FullFace s) (i : Fin (N+1)) :
    ∃ W : Submodule K V, finrank K W = i.val ∧ F.Opposed W ∧
      (0 < i.val → i.val < N → W ∈ s) := by
  by_cases hi0 : i.val = 0
  · exact ⟨⊥,by simp [hi0],F.opposed_bot,by omega⟩
  by_cases hiN : i.val = N
  · exact ⟨⊤,by simp [F.dimension,hiN],F.opposed_top,by omega⟩
  obtain ⟨W,hW,hr⟩ := hs.2 i.val (by omega) (by omega)
  exact ⟨W,hr,(hs.1.1 W hW).2.2,fun _ _ => hW⟩

theorem exists_flag_from_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : F.FullFace s) :
    ∃ E : CompleteFlag K V N, F.Opposite E ∧
      ∀ W : Submodule K V, W ∈ s ↔
        ∃ i : Fin (N+1), 0 < i.val ∧ i.val < N ∧ E.space i = W := by
  classical
  choose f hr ho hm using F.exists_flag_stages s hs
  have hmono : Monotone f := by
    intro i j hij
    by_cases hi : i.val = 0
    · have hh : f i = ⊥ := Submodule.finrank_eq_zero.mp ((hr i).trans hi)
      rw [hh]; exact bot_le
    by_cases hj : j.val = N
    · have hh : f j = ⊤ := Submodule.eq_top_of_finrank_eq ((hr j).trans (hj.trans F.dimension.symm))
      rw [hh]; exact le_top
    exact F.face_order_of_rank_le s hs.1 (hm i (by omega) (by omega))
      (hm j (by omega) (by omega)) (by rw [hr,hr]; exact hij)
  let E : CompleteFlag K V N := ⟨f,hmono,F.dimension,hr⟩
  refine ⟨E,?_,?_⟩
  · intro i
    have hh := (ho ⟨N-i.val, by omega⟩).symm
    simp only [hr] at hh
    have he : (⟨N-(N-i.val), by omega⟩ : Fin (N+1)) = i := by apply Fin.ext; dsimp; omega
    simpa only [he] using hh
  · intro W
    constructor
    · intro hW
      let i : Fin (N+1) := ⟨finrank K W, by have := (hs.1.1 W hW).2.1; omega⟩
      have hi0 : 0 < i.val := (hs.1.1 W hW).1
      have hiN : i.val < N := (hs.1.1 W hW).2.1
      exact ⟨i,hi0,hiN,F.rank_injective_on_face s hs.1 (hm i hi0 hiN) hW (hr i)⟩
    · rintro ⟨i,hi0,hiN,rfl⟩
      exact hm i hi0 hiN

open scoped Pointwise

def flagStabilizer (F : CompleteFlag K V N) : Subgroup (V ≃ₗ[K] V) :=
  ⨅ i : Fin (N+1), MulAction.stabilizer (V ≃ₗ[K] V) (F.space i)

omit [FiniteDimensional K V] in
lemma mem_flagStabilizer (F : CompleteFlag K V N) (e : V ≃ₗ[K] V) :
    e ∈ F.flagStabilizer ↔ ∀ i, (F.space i).map e.toLinearMap = F.space i := by
  simp only [flagStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

lemma flagStabilizer_good (F : CompleteFlag K V N) (e : F.flagStabilizer) (W : Submodule K V)
    (hW : F.Good W) : F.Good (e • W) := by
  have he := (F.mem_flagStabilizer e.val).mp e.property
  change F.Good (W.map e.val.toLinearMap)
  refine ⟨by simpa only [e.val.finrank_map_eq] using hW.1,
    by simpa only [e.val.finrank_map_eq] using hW.2.1,?_⟩
  rw [F.opposed_iff_disjoint]
  simp only [e.val.finrank_map_eq]
  rw [← he]
  exact Submodule.disjoint_map e.val.injective hW.2.2.disjoint

lemma flagStabilizer_invariant (F : CompleteFlag K V N) (e : F.flagStabilizer)
    (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces) : e • s ∈ F.complex.faces := by
  classical
  constructor
  · intro W hW
    obtain ⟨U,hU,rfl⟩ := Finset.mem_smul_finset.mp hW
    exact F.flagStabilizer_good e U (hs.1 U hU)
  · intro W hW W' hW' hne
    obtain ⟨U,hU,rfl⟩ := Finset.mem_smul_finset.mp hW
    obtain ⟨U',hU',rfl⟩ := Finset.mem_smul_finset.mp hW'
    exact (hs.2 hU hU' (fun hh => hne (congrArg (fun U => e • U) hh))).imp
      (fun h => Submodule.map_mono h) (fun h => Submodule.map_mono h)

theorem chamber_transitive (F : CompleteFlag K V N)
    (s t : Finset (Submodule K V)) (hs : F.FullFace s) (ht : F.FullFace t) :
    ∃ e : F.flagStabilizer, e • s = t := by
  classical
  obtain ⟨E,hE,hsE⟩ := F.exists_flag_from_face s hs
  obtain ⟨E',hE',htE'⟩ := F.exists_flag_from_face t ht
  obtain ⟨e,heF,heE⟩ := exists_flag_stabilizing_equiv hE hE'
  let ee : F.flagStabilizer := ⟨e,(F.mem_flagStabilizer e).mpr heF⟩
  refine ⟨ee,?_⟩
  ext W
  constructor
  · intro hW
    obtain ⟨U,hU,rfl⟩ := Finset.mem_smul_finset.mp hW
    obtain ⟨i,hi0,hiN,heU⟩ := (hsE U).mp hU
    apply (htE' _).mpr
    refine ⟨i,hi0,hiN,?_⟩
    change E'.space i = U.map e.toLinearMap
    rw [← heU,heE]
  · intro hW
    obtain ⟨i,hi0,hiN,heW⟩ := (htE' W).mp hW
    apply Finset.mem_smul_finset.mpr
    refine ⟨E.space i,(hsE _).mpr ⟨i,hi0,hiN,rfl⟩,?_⟩
    change (E.space i).map e.toLinearMap = W
    rw [heE,heW]

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

omit [FiniteDimensional K V] in
lemma prefix_span_image (b : Basis (Fin N) K V) (i : Fin (N+1)) :
    Set.range (fun j : Fin i.val => b (prefixIndex i j)) =
      b '' {j : Fin N | j.val < i.val} := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨prefixIndex i j,j.isLt,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨j.val,hj⟩,rfl⟩

lemma mem_flag_iff_repr (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (k : Fin (N+1)) (v : V) :
    v ∈ F.space k ↔ ∀ j : Fin N, k.val ≤ j.val → b.repr v j = 0 := by
  rw [← F.adapted_prefix b hb k, prefix_span_image, b.mem_span_image]
  constructor
  · intro h j hj
    by_contra hn
    have hh := h (Finsupp.mem_support_iff.mpr hn)
    exact Nat.not_lt_of_ge hj hh
  · intro h j hj
    by_contra hn
    have hh := h j (Nat.le_of_not_gt hn)
    exact (Finsupp.mem_support_iff.mp hj) hh

omit [FiniteDimensional K V] in
lemma adapted_basis_not_mem_previous {F E : CompleteFlag K V N} (h : F.Opposite E)
    (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ ∧ b i ∈ E.space ⟨N-i.val, by omega⟩)
    (i : Fin N) : b i ∉ F.space i.castSucc := by
  intro hi
  have hh : b i ∈ F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ := ⟨hi,(hb i).2⟩
  have he : F.space i.castSucc ⊓ E.space ⟨N-i.val, by omega⟩ = ⊥ := by
    simpa only [Fin.val_castSucc] using (h i.castSucc).inf_eq_bot
  rw [he] at hh
  exact b.ne_zero i hh

lemma adapted_diagonal_ne_zero (F : CompleteFlag K V N)
    (b c : Basis (Fin N) K V) (hb : ∀ i : Fin N, b i ∈ F.space i.succ)
    (hc : ∀ i : Fin N, c i ∈ F.space i.succ)
    (hnot : ∀ i : Fin N, c i ∉ F.space i.castSucc) (i : Fin N) :
    b.repr (c i) i ≠ 0 := by
  intro hi
  apply hnot i
  apply (F.mem_flag_iff_repr b hb i.castSucc (c i)).mpr
  intro j hj
  by_cases hji : j = i
  · simpa [hji] using hi
  · apply (F.mem_flag_iff_repr b hb i.succ (c i)).mp (hc i) j
    change i.val+1 ≤ j.val
    change i.val ≤ j.val at hj
    have : j.val ≠ i.val := fun h => hji (Fin.ext h)
    omega

theorem exists_normalized_adapted_basis {F E : CompleteFlag K V N} (h : F.Opposite E)
    (b : Basis (Fin N) K V) (hb : ∀ i : Fin N, b i ∈ F.space i.succ) :
    ∃ c : Basis (Fin N) K V, ∀ i : Fin N,
      c i ∈ F.space i.succ ∧ c i ∈ E.space ⟨N-i.val, by omega⟩ ∧ b.repr (c i) i = 1 := by
  classical
  obtain ⟨c,hc⟩ := exists_adapted_basis h
  have hne := F.adapted_diagonal_ne_zero b c hb (fun i => (hc i).1)
    (adapted_basis_not_mem_previous h c hc)
  let u : Fin N → Kˣ := fun i => (Units.mk0 (b.repr (c i) i) (hne i))⁻¹
  refine ⟨c.unitsSMul u,?_⟩
  intro i
  simp only [Basis.unitsSMul_apply, Units.smul_def]
  refine ⟨(F.space i.succ).smul_mem _ (hc i).1,
    (E.space ⟨N-i.val, by omega⟩).smul_mem _ (hc i).2,?_⟩
  simp [u, map_smul, hne i]

def Unitriangular (b : Basis (Fin N) K V) (e : V ≃ₗ[K] V) : Prop :=
  ∀ i j : Fin N, i ≤ j → b.repr (e (b i)) j = if j = i then 1 else 0

theorem exists_unitriangular_equiv {F E E' : CompleteFlag K V N}
    (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ ∧ b i ∈ E.space ⟨N-i.val, by omega⟩)
    (h' : F.Opposite E') :
    ∃ e : V ≃ₗ[K] V, Unitriangular b e ∧
      (∀ i, (F.space i).map e.toLinearMap = F.space i) ∧
      (∀ i, (E.space i).map e.toLinearMap = E'.space i) := by
  classical
  obtain ⟨c,hc⟩ := exists_normalized_adapted_basis h' b (fun i => (hb i).1)
  let e := b.equiv c (Equiv.refl _)
  refine ⟨e,?_,?_,?_⟩
  · intro i j hij
    dsimp [e]
    rw [Basis.equiv_apply, Equiv.refl_apply]
    by_cases hji : j = i
    · simpa [hji] using (hc i).2.2
    · rw [ite_eq_right hji]
      apply (F.mem_flag_iff_repr b (fun i => (hb i).1) i.succ (c i)).mp (hc i).1 j
      change i.val+1 ≤ j.val
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      change i.val ≤ j.val at hij
      omega
  · intro i
    calc
      (F.space i).map e.toLinearMap =
          (span K (Set.range (fun j : Fin i.val => b (prefixIndex i j)))).map e.toLinearMap := by
        rw [adapted_prefix F b (fun i => (hb i).1)]
      _ = span K (Set.range (fun j : Fin i.val => c (prefixIndex i j))) :=
        basis_equiv_span_range b c _
      _ = F.space i := adapted_prefix F c (fun i => (hc i).1) i
  · intro i
    let k : Fin (N+1) := ⟨N-i.val, by omega⟩
    have he : (⟨N-k.val, by omega⟩ : Fin (N+1)) = i := by
      apply Fin.ext; dsimp [k]; omega
    rw [← he, ← adapted_suffix E b (fun i => (hb i).2) k,
      basis_equiv_span_range b c, adapted_suffix E' c (fun i => (hc i).2.1), he]

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

omit [FiniteDimensional K V] in
lemma suffix_span_image (b : Basis (Fin N) K V) (i : Fin (N+1)) :
    Set.range (fun j : Fin (N-i.val) => b (suffixIndex i j)) =
      b '' {j : Fin N | i.val ≤ j.val} := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨suffixIndex i j,by dsimp [suffixIndex]; omega,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    change i.val ≤ j.val at hj
    refine ⟨⟨j.val-i.val,by omega⟩,?_⟩
    dsimp only
    apply congrArg b
    apply Fin.ext
    dsimp [suffixIndex]
    omega

lemma mem_opposite_flag_iff_repr (E : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ j : Fin N, b j ∈ E.space ⟨N-j.val, by omega⟩) (i : Fin (N+1)) (v : V) :
    v ∈ E.space ⟨N-i.val, by omega⟩ ↔
      ∀ j : Fin N, j.val < i.val → b.repr v j = 0 := by
  rw [← E.adapted_suffix b hb i, suffix_span_image, b.mem_span_image]
  constructor
  · intro h j hj
    by_contra hn
    exact Nat.not_lt_of_ge (h (Finsupp.mem_support_iff.mpr hn)) hj
  · intro h j hj
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hj) (h j (Nat.lt_of_not_ge hn))

theorem unitriangular_stabilizer_trivial (E : CompleteFlag K V N)
    (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ E.space ⟨N-i.val, by omega⟩)
    (e : V ≃ₗ[K] V) (he : Unitriangular b e)
    (hE : ∀ i, (E.space i).map e.toLinearMap = E.space i) : e = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro i
  change e (b i) = b i
  apply b.repr.injective
  ext j
  rw [Basis.repr_self, Finsupp.single_apply]
  by_cases hji : j < i
  · have hm : e (b i) ∈ E.space ⟨N-i.val, by omega⟩ := by
      rw [← hE]
      exact Submodule.mem_map_of_mem (hb i)
    have hz := (E.mem_opposite_flag_iff_repr b hb i.castSucc (e (b i))).mp hm j hji
    rw [hz, ite_eq_right (ne_of_gt hji)]
  · have hij : i ≤ j := le_of_not_gt hji
    simpa [eq_comm] using he i j hij

omit [FiniteDimensional K V] in
lemma flagStabilizer_mem (F : CompleteFlag K V N) (e : V ≃ₗ[K] V)
    (he : e ∈ F.flagStabilizer) (i : Fin (N+1)) {x : V} (hx : x ∈ F.space i) :
    e x ∈ F.space i := by
  rw [← (F.mem_flagStabilizer e).mp he i]
  exact Submodule.mem_map_of_mem hx

def unipotentFlagStabilizer (F : CompleteFlag K V N) : Subgroup (V ≃ₗ[K] V) where
  carrier := {e | e ∈ F.flagStabilizer ∧ ∀ i : Fin N, ∀ x ∈ F.space i.succ,
    e x - x ∈ F.space i.castSucc}
  one_mem' := ⟨F.flagStabilizer.one_mem,by intro i x hx; simp⟩
  mul_mem' := by
    rintro e f ⟨he,he'⟩ ⟨hf,hf'⟩
    refine ⟨F.flagStabilizer.mul_mem he hf,?_⟩
    intro i x hx
    have h1 := F.flagStabilizer_mem e he i.castSucc (hf' i x hx)
    have h2 := he' i x hx
    have hadd := (F.space i.castSucc).add_mem h1 h2
    simpa only [map_sub, LinearEquiv.mul_apply, sub_add_sub_cancel] using hadd
  inv_mem' := by
    rintro e ⟨he,he'⟩
    refine ⟨F.flagStabilizer.inv_mem he,?_⟩
    intro i x hx
    have hy := F.flagStabilizer_mem e⁻¹ (F.flagStabilizer.inv_mem he) i.succ hx
    have hh := (F.space i.castSucc).neg_mem (he' i (e⁻¹ x) hy)
    have hex : e (e⁻¹ x) = x := e.apply_symm_apply x
    simpa only [hex, neg_sub] using hh

lemma unitriangular_difference (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V)
    (he : Unitriangular b e) (i : Fin N) : e (b i) - b i ∈ F.space i.castSucc := by
  apply (F.mem_flag_iff_repr b hb i.castSucc _).mpr
  intro j hj
  rw [map_sub, Finsupp.sub_apply, Basis.repr_self, Finsupp.single_apply, he i j hj]
  simp [eq_comm]

lemma unitriangular_grading (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V)
    (he : Unitriangular b e) (i : Fin N) (x : V) (hx : x ∈ F.space i.succ) :
    e x - x ∈ F.space i.castSucc := by
  let D : V →ₗ[K] V := e.toLinearMap - LinearMap.id
  change x ∈ (F.space i.castSucc).comap D
  have hle : F.space i.succ ≤ (F.space i.castSucc).comap D := by
    rw [← F.adapted_prefix b hb i.succ]
    apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    change e (b (prefixIndex i.succ j)) - b (prefixIndex i.succ j) ∈ F.space i.castSucc
    exact F.mono (by change j.val ≤ i.val; have := j.isLt; simp only [Fin.val_succ] at this; omega)
      (F.unitriangular_difference b hb e he (prefixIndex i.succ j))
  exact hle hx

lemma unipotent_unitriangular (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : F.unipotentFlagStabilizer) :
    Unitriangular b e.val := by
  intro i j hij
  have h := (F.mem_flag_iff_repr b hb i.castSucc _).mp (e.property.2 i (b i) (hb i)) j hij
  rw [map_sub, Finsupp.sub_apply, Basis.repr_self, Finsupp.single_apply] at h
  simpa [eq_comm] using sub_eq_zero.mp h

theorem unipotent_transitive {F E E' : CompleteFlag K V N}
    (h : F.Opposite E) (h' : F.Opposite E') :
    ∃ e : F.unipotentFlagStabilizer, ∀ i,
      (E.space i).map e.val.toLinearMap = E'.space i := by
  obtain ⟨b,hb⟩ := exists_adapted_basis h
  obtain ⟨e,he,heF,heE⟩ := exists_unitriangular_equiv b hb h'
  exact ⟨⟨e,(F.mem_flagStabilizer e).mpr heF,
    F.unitriangular_grading b (fun i => (hb i).1) e he⟩,heE⟩

theorem unipotent_stabilizer_trivial {F E : CompleteFlag K V N} (h : F.Opposite E)
    (e : F.unipotentFlagStabilizer)
    (hE : ∀ i, (E.space i).map e.val.toLinearMap = E.space i) : e = 1 := by
  obtain ⟨b,hb⟩ := exists_adapted_basis h
  apply Subtype.ext
  exact unitriangular_stabilizer_trivial E b (fun i => (hb i).2) e
    (F.unipotent_unitriangular b (fun i => (hb i).1) e) hE

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule TypedCosetFaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

open scoped Pointwise
def properIndex (i : Fin (N-1)) : Fin (N+1) := ⟨i.val+1, by omega⟩
def baseSpace (E : CompleteFlag K V N) (i : Fin (N-1)) : Submodule K V :=
  E.space (properIndex (N:=N) i)
omit [FiniteDimensional K V] in
@[simp] lemma baseSpace_rank (E : CompleteFlag K V N) (i : Fin (N-1)) :
    finrank K (E.baseSpace i) = i.val+1 := E.rank _
omit [FiniteDimensional K V] in
lemma baseSpace_injective (E : CompleteFlag K V N) : Function.Injective E.baseSpace := by
  intro i j he
  have hh := congrArg (fun W : Submodule K V => finrank K W) he
  simp only [baseSpace_rank] at hh
  exact Fin.ext (by omega)

omit [FiniteDimensional K V] in
lemma opposed_of_opposite {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin (N+1)) :
    F.Opposed (E.space i) := by
  unfold Opposed
  simp only [E.rank]
  exact opposite_symm h i

omit [FiniteDimensional K V] in
lemma baseSpace_good {F E : CompleteFlag K V N} (h : F.Opposite E) (i : Fin (N-1)) :
    F.Good (E.baseSpace i) := by
  refine ⟨by simp,by simp; omega,opposed_of_opposite h _⟩

def baseSimplex (E : CompleteFlag K V N) : Finset (Submodule K V) := by
  classical
  exact Finset.univ.image E.baseSpace

omit [FiniteDimensional K V] in
lemma baseSimplex_full {F E : CompleteFlag K V N} (h : F.Opposite E) :
    F.FullFace E.baseSimplex := by
  classical
  constructor
  · constructor
    · intro W hW
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
      exact baseSpace_good h i
    · intro W hW W' hW' _
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hW'
      rcases le_total i j with hij | hji
      · exact Or.inl (E.mono (show properIndex (N:=N) i ≤ properIndex (N:=N) j by change i.val+1 ≤ j.val+1; exact Nat.add_le_add_right hij 1))
      · exact Or.inr (E.mono (show properIndex (N:=N) j ≤ properIndex (N:=N) i by change j.val+1 ≤ i.val+1; exact Nat.add_le_add_right hji 1))
  · intro j hj0 hjN
    let i : Fin (N-1) := ⟨j-1,by omega⟩
    refine ⟨E.baseSpace i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
    rw [baseSpace_rank]; dsimp [i]; omega

def vertexStabilizers (F E : CompleteFlag K V N) (i : Fin (N-1)) :
    Subgroup F.unipotentFlagStabilizer :=
  MulAction.stabilizer F.unipotentFlagStabilizer (E.baseSpace i)

def cosetVertexMap (F E : CompleteFlag K V N) :
    Vertex (F.vertexStabilizers E) → Submodule K V :=
  fun x => MulAction.ofQuotientStabilizer F.unipotentFlagStabilizer (E.baseSpace x.1) x.2

omit [FiniteDimensional K V] in
@[simp] lemma cosetVertexMap_vertex (F E : CompleteFlag K V N)
    (g : F.unipotentFlagStabilizer) (i : Fin (N-1)) :
    F.cosetVertexMap E (vertex (F.vertexStabilizers E) g i) = g • E.baseSpace i := rfl

omit [FiniteDimensional K V] in
lemma cosetVertexMap_rank (F E : CompleteFlag K V N) (x : Vertex (F.vertexStabilizers E)) :
    finrank K (F.cosetVertexMap E x) = x.1.val+1 := by
  rcases x with ⟨i,x⟩
  induction x using Quotient.inductionOn with | h g =>
  change finrank K ((E.baseSpace i).map g.val.toLinearMap) = i.val+1
  rw [g.val.finrank_map_eq,baseSpace_rank]

omit [FiniteDimensional K V] in
lemma cosetVertexMap_injective (F E : CompleteFlag K V N) : Function.Injective (F.cosetVertexMap E) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  have hr := congrArg (fun W : Submodule K V => finrank K W) hxy
  rw [cosetVertexMap_rank,cosetVertexMap_rank] at hr
  have hij : i = j := Fin.ext (by dsimp at hr; omega)
  subst j
  congr 1
  exact MulAction.injective_ofQuotientStabilizer F.unipotentFlagStabilizer (E.baseSpace i) hxy

lemma unipotent_good (F : CompleteFlag K V N) (g : F.unipotentFlagStabilizer)
    (W : Submodule K V) (hW : F.Good W) : F.Good (g • W) :=
  F.flagStabilizer_good ⟨g.val,g.property.1⟩ W hW

lemma cosetVertexMap_good {F E : CompleteFlag K V N} (h : F.Opposite E)
    (x : Vertex (F.vertexStabilizers E)) : F.Good (F.cosetVertexMap E x) := by
  rcases x with ⟨i,x⟩
  induction x using Quotient.inductionOn with | h g =>
  exact F.unipotent_good g _ (baseSpace_good h i)

theorem cosetFace_opposed {F E : CompleteFlag K V N} (h : F.Opposite E)
    (s : Finset (Vertex (F.vertexStabilizers E))) (hs : IsFace (F.vertexStabilizers E) s) :
    s.image (F.cosetVertexMap E) ∈ F.complex.faces := by
  classical
  obtain ⟨g,A,rfl⟩ := hs
  have he : (face (F.vertexStabilizers E) g A).image (F.cosetVertexMap E) =
      A.image (fun i => g • E.baseSpace i) := by
    simp only [face,Finset.image_image,Function.comp_def,cosetVertexMap_vertex]
  rw [he]
  constructor
  · intro W hW
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    exact F.unipotent_good g _ (baseSpace_good h i)
  · intro W hW W' hW' _
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hW'
    rcases le_total i j with hij | hji
    · exact Or.inl (Submodule.map_mono (E.mono (by change i.val+1 ≤ j.val+1; exact Nat.add_le_add_right hij 1)))
    · exact Or.inr (Submodule.map_mono (E.mono (by change j.val+1 ≤ i.val+1; exact Nat.add_le_add_right hji 1)))

theorem opposedFace_coset {F E : CompleteFlag K V N} (h : F.Opposite E)
    (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces) :
    ∃ g : F.unipotentFlagStabilizer, ∃ A : Finset (Fin (N-1)),
      (face (F.vertexStabilizers E) g A).image (F.cosetVertexMap E) = s := by
  classical
  obtain ⟨t,ht,hst⟩ := F.exists_full_face s hs
  obtain ⟨E',hE',htE'⟩ := F.exists_flag_from_face t ht
  obtain ⟨g,hg⟩ := unipotent_transitive h hE'
  let A := Finset.univ.filter (fun i : Fin (N-1) => E'.baseSpace i ∈ s)
  refine ⟨g,A,?_⟩
  simp only [face,Finset.image_image,Function.comp_def,cosetVertexMap_vertex]
  have hg' (i : Fin (N-1)) : g • E.baseSpace i = E'.baseSpace i := hg (properIndex (N:=N) i)
  simp_rw [hg']
  ext W
  constructor
  · intro hW
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hW
    exact (Finset.mem_filter.mp hi).2
  · intro hW
    obtain ⟨i,hi0,hiN,hiW⟩ := (htE' W).mp (hst hW)
    let j : Fin (N-1) := ⟨i.val-1,by omega⟩
    have hji : properIndex (N:=N) j = i := by apply Fin.ext; dsimp [properIndex,j]; omega
    have hjW : E'.baseSpace j = W := by rw [baseSpace,hji,hiW]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hjW]; exact hW⟩,hjW⟩

theorem cosetFace_iff {F E : CompleteFlag K V N} (h : F.Opposite E)
    (s : Finset (Vertex (F.vertexStabilizers E))) :
    IsFace (F.vertexStabilizers E) s ↔ s.image (F.cosetVertexMap E) ∈ F.complex.faces := by
  classical
  constructor
  · exact cosetFace_opposed h s
  · intro hs
    obtain ⟨g,A,he⟩ := opposedFace_coset h _ hs
    refine ⟨g,A,?_⟩
    exact Finset.image_injective (F.cosetVertexMap_injective E) he

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def basisFlag (b : Basis (Fin N) K V) : CompleteFlag K V N where
  space i := span K (Set.range (fun j : Fin i.val => b (prefixIndex i j)))
  mono := by
    intro i j hij
    apply span_mono
    rintro v ⟨k,rfl⟩
    exact ⟨⟨k.val,by omega⟩,rfl⟩
  dimension := by simpa using Module.finrank_eq_card_basis b
  rank i := by
    have hi : Function.Injective (prefixIndex i) := by
      intro j k he; apply Fin.ext; exact congrArg (fun x : Fin N => x.val) he
    simpa only [Function.comp_def, Fintype.card_fin] using finrank_span_eq_card (b.linearIndependent.comp _ hi)

omit [FiniteDimensional K V] in
lemma basisFlag_adapted (b : Basis (Fin N) K V) (i : Fin N) :
    b i ∈ (basisFlag b).space i.succ := by
  apply Submodule.subset_span
  refine ⟨⟨i.val,by simp⟩,?_⟩
  rfl

def tailIndex (i : Fin (N+1)) (j : Fin i.val) : Fin N := ⟨N-i.val+j.val,by omega⟩

def oppositeBasisFlag (b : Basis (Fin N) K V) : CompleteFlag K V N where
  space i := span K (Set.range (fun j : Fin i.val => b (tailIndex i j)))
  mono := by
    intro i j hij
    apply span_mono
    rintro v ⟨k,rfl⟩
    refine ⟨⟨j.val-i.val+k.val,by omega⟩,?_⟩
    apply congrArg b
    apply Fin.ext
    dsimp [tailIndex]
    omega
  dimension := by simpa using Module.finrank_eq_card_basis b
  rank i := by
    have hi : Function.Injective (tailIndex i) := by
      intro j k he
      apply Fin.ext
      have hh := congrArg Fin.val he
      dsimp [tailIndex] at hh
      omega
    simpa only [Function.comp_def, Fintype.card_fin] using finrank_span_eq_card (b.linearIndependent.comp _ hi)

omit [FiniteDimensional K V] in
lemma oppositeBasisFlag_adapted (b : Basis (Fin N) K V) (i : Fin N) :
    b i ∈ (oppositeBasisFlag b).space ⟨N-i.val,by omega⟩ := by
  apply Submodule.subset_span
  refine ⟨⟨0,by change 0 < N-i.val; omega⟩,?_⟩
  apply congrArg b
  apply Fin.ext
  dsimp [tailIndex]
  omega

theorem basisFlags_opposite (b : Basis (Fin N) K V) :
    (basisFlag b).Opposite (oppositeBasisFlag b) := by
  intro i
  apply (Submodule.isCompl_iff_disjoint _ _ (by
    rw [(basisFlag b).rank,(oppositeBasisFlag b).rank,(basisFlag b).dimension]
    dsimp; omega)).mpr
  apply disjoint_def.mpr
  intro x hx hy
  apply b.repr.injective
  ext j
  rw [map_zero,Finsupp.zero_apply]
  by_cases hji : j.val < i.val
  · exact ((oppositeBasisFlag b).mem_opposite_flag_iff_repr b
      (oppositeBasisFlag_adapted b) i x).mp hy j hji
  · exact ((basisFlag b).mem_flag_iff_repr b (basisFlag_adapted b) i x).mp hx j (by omega)

lemma unitriangular_flag (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V)
    (he : Unitriangular b e) (i : Fin (N+1)) :
    (F.space i).map e.toLinearMap = F.space i := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← F.adapted_prefix b hb i,Submodule.map_span]
    apply span_le.mpr
    rintro x ⟨v,⟨j,rfl⟩,rfl⟩
    rw [F.adapted_prefix b hb i]
    apply (F.mem_flag_iff_repr b hb i _).mpr
    intro k hik
    have hjk : prefixIndex i j ≤ k := by
      change j.val ≤ k.val
      omega
    have hne : k ≠ prefixIndex i j := by
      intro hh; have := congrArg Fin.val hh; dsimp [prefixIndex] at this; omega
    exact (he _ _ hjk).trans (ite_eq_right hne)
  · exact e.finrank_map_eq _

theorem mem_unipotent_iff_unitriangular (F : CompleteFlag K V N) (b : Basis (Fin N) K V)
    (hb : ∀ i : Fin N, b i ∈ F.space i.succ) (e : V ≃ₗ[K] V) :
    e ∈ F.unipotentFlagStabilizer ↔ Unitriangular b e := by
  constructor
  · intro he; exact F.unipotent_unitriangular b hb ⟨e,he⟩
  · intro he
    exact ⟨(F.mem_flagStabilizer e).mpr (unitriangular_flag F b hb e he),
      F.unitriangular_grading b hb e he⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

end

end OAI
