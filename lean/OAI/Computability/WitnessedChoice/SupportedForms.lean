import OAI.Computability.WitnessedChoice.Homogeneity

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n M : ℕ} {b b' : Vertex n → Scalar}

theorem boundary_eq_incidence : (boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar)) =
    Flows.incidence tail head := rfl

def GiantBound (n M : ℕ) : Prop :=
  ((12*(M:ℝ))/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)

theorem giant_exists_of_bound (hbound : GiantBound n M) (T : Finset (Edge n)) (hT : T.card ≤ 6*M) :
    ∃ v, Flows.IsGiant tail head T v := by
  have hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ) := by
    apply lt_of_le_of_lt _ hbound
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    have hh : (T.card:ℝ) ≤ 6*M := by exact_mod_cast hT
    linarith
  obtain ⟨c,hc⟩ := exists_giant T hnum
  refine ⟨c.out,?_⟩
  change Fintype.card (Vertex n) < 2*(Flows.cell tail head T c).card
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hcard] using hc

theorem defect_transport (hbound : GiantBound n M) (T U : Finset (Edge n)) (hTU : T ⊆ U)
    (hU : U.card ≤ 6*M) (t : Edge n → Scalar) (w : Vertex n)
    (hw : Flows.IsGiant tail head T w) (ht : boundary t = b'-b-Pi.single w 1) :
    ∃ t' : Edge n → Scalar, ∃ w' : Vertex n,
      Flows.IsGiant tail head U w' ∧ boundary t' = b'-b-Pi.single w' 1 ∧ ∀ e ∈ T, t' e = t e := by
  obtain ⟨w',hw'⟩ := giant_exists_of_bound hbound U hU
  have hc := Flows.giants_connected tail head (Flows.giant_mono tail head hTU hw') hw
  obtain ⟨p,hp,hd⟩ := Flows.path_flow tail head T hc
  refine ⟨t+p,w',hw',?_,?_⟩
  · rw [map_add,ht,boundary_eq_incidence,hd]
    abel
  · intro e he; simp [hp e he]

def CompatibleAssignment {I : Type*} [DecidableEq I] (names : Finset I)
    (a : I → Atom b) (a' : I → Atom b') : Prop :=
  ∃ t : Edge n → Scalar, ∃ w : Vertex n,
    Flows.IsGiant tail head (touches names a) w ∧ boundary t = b'-b-Pi.single w 1 ∧
    ∀ i ∈ names, AtomShift t (a i) (a' i)

theorem CompatibleAssignment.mono {I : Type*} [DecidableEq I] {names small : Finset I}
    (hs : small ⊆ names) {a : I → Atom b} {a' : I → Atom b'}
    (h : CompatibleAssignment names a a') : CompatibleAssignment small a a' := by
  obtain ⟨t,w,hw,ht,ha⟩ := h
  exact ⟨t,w,Flows.giant_mono tail head (touches_mono hs a) hw,ht,fun i hi => ha i (hs hi)⟩

theorem CompatibleAssignment.extend (hn : 1 ≤ n) (hbound : GiantBound n M)
    (names : Finset (Fin M)) (a : Fin M → Atom b) (a' : Fin M → Atom b')
    (h : CompatibleAssignment names a a') (i : Fin M) :
    ∃ e : Atom b ≃ Atom b', ∀ x,
      CompatibleAssignment (insert i (names.erase i)) (Function.update a i x) (Function.update a' i (e x)) := by
  obtain ⟨t,w,hw,ht,ha⟩ := h.mono (erase_subset i names)
  let T := touches (names.erase i) a
  have hcard : (names.erase i).card + 1 ≤ M := by
    have hsub : names.erase i ⊆ (univ : Finset (Fin M)).erase i := erase_subset_erase i (subset_univ _)
    have hh := card_le_card hsub
    have hpos := i.isLt
    rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at hh
    omega
  have hj (J : Block n) : (T ∪ blockEdges J).card ≤ 6*M := by
    calc
      _ ≤ T.card + (blockEdges J).card := card_union_le _ _
      _ ≤ 6*(names.erase i).card + 6 := Nat.add_le_add (touches_card _ _) (blockEdges_card _)
      _ ≤ 6*M := by omega
  have hmove (J : Block n) := defect_transport hbound T (T ∪ blockEdges J)
    subset_union_left (hj J) t w hw ht
  choose tj wj hjg hjd hjs using hmove
  have hV : 2 ≤ Fintype.card (Vertex n) := by
    have hc : Fintype.card (Vertex n) = (n+1)^3 := by
      simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
    rw [hc]
    have hh : 2^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hv (v : Vertex n) : boundary (tj (.inr v)) v = b' v-b v := by
    have hwv : wj (.inr v) ≠ v := Flows.giant_ne_isolated tail head hV (hjg (.inr v)) (by
      intro e he
      exact mem_union_right _ (by simpa [blockEdges,incident,or_comm] using he))
    have hh := congrFun (hjd (.inr v)) v
    simpa [Pi.single_apply,Ne.symm hwv] using hh
  let e := blockShiftEquiv (fun e => tj (.inl e)) (fun v => tj (.inr v)) hv
  refine ⟨e,fun x => ?_⟩
  let J := atomBlock x
  refine ⟨tj J,wj J,?_,hjd J,?_⟩
  · rw [touches_insert_update]
    exact hjg J
  · intro j hj'
    rcases mem_insert.mp hj' with rfl | hj'
    · simp only [Function.update_self]
      cases x with
      | inl x => rcases x with ⟨f,s⟩; exact AtomShift.edge f s
      | inr x => rcases x with ⟨v,s⟩; exact AtomShift.config v s (hv v)
    · have hji := (mem_erase.mp hj').1
      simp only [Function.update_of_ne hji]
      exact (ha j hj').congr (fun f hf => (hjs J f (touch_subset_touches _ _ hj' hf)).symm)

theorem base_equivalence_numeric (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    (φ : Counting.Formula AnalysisSymbol (Fin M)) (hφ : φ.free = ∅)
    (a : Fin M → Atom (0 : Vertex n → Scalar))
    (a' : Fin M → Atom (Pi.single vstar 1)) :
    φ.eval (analysisStructure (0 : Vertex n → Scalar)) a ↔
      φ.eval (analysisStructure (Pi.single vstar 1)) a' := by
  have heq : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ i ∈ names, ∀ j ∈ names,
      (v i = v j ↔ w i = w j) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ i hi j hj
    exact (ha i hi).equal_iff (ha j hj)
  have hrel : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      ((analysisStructure (0 : Vertex n → Scalar)).rel r (v i) (v j) ↔
      (analysisStructure (Pi.single vstar 1)).rel r (w i) (w j)) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ r i hi j hj
    exact (ha i hi).analysisRelation (ha j hj) r
  apply Counting.Formula.eval_of_partialBijectionSystem _ _ CompatibleAssignment heq hrel
    (fun names v w hh i => CompatibleAssignment.extend hn hbound names v w hh i) φ ∅ a a' _ (by simp [hφ])
  refine ⟨0,vstar,?_,by simp,by simp⟩
  simpa [touches] using grid_empty_giant vstar

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Forms

noncomputable section

open Classical

open Counting Hereditary

variable {R I J A B : Type*}

inductive Form (J L : Type*)
  | atom (j : J)
  | set (n : ℕ) (child : Fin n → Form J L) (label : Fin n → L)

namespace Form

variable [Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A]

def value (S : Structure R A) (e : J ⊕ J ↪ I) :
    Form J (Set (Formula R I)) → (J → A) → HF A
  | .atom j, a => Hereditary.atom (a j)
  | .set _n child label, a => Hereditary.ofFinset
      (Finset.univ.biUnion fun i =>
        (Finset.univ.filter fun b : J → A =>
          tupleType S e (Sum.elim b a) = label i).image (value S e (child i)))

omit [Fintype I] in
@[simp] theorem value_atom (S : Structure R A) (e : J ⊕ J ↪ I) (j : J) (a : J → A) :
    value S e (.atom j) a = Hereditary.atom (a j) := rfl

omit [Fintype I] in
@[simp] theorem value_set_isSet (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) : isSet (value S e (.set n child label) a) = true := rfl

omit [Fintype I] in
@[simp] theorem mem_value_set (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) (x : HF A) :
    x ∈ value S e (.set n child label) a ↔
      ∃ i b, tupleType S e (Sum.elim b a) = label i ∧ value S e (child i) b = x := by
  classical
  simp only [value,mem_ofFinset,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_filter,true_and]

omit [Fintype I] in

theorem value_iso [Fintype B] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I) (f : A ≃ B)
    (hf : ∀ r a b, S.rel r a b ↔ T.rel r (f a) (f b))
    (φ : Form J (Set (Formula R I))) (a : J → A) :
    Hereditary.map f (value S e φ a) = value T e φ (f ∘ a) := by
  induction φ generalizing a with
  | atom j => rfl
  | set n child label ih =>
    apply Hereditary.ext_sets (by simp [value]) (by simp)
    intro x
    change x ∈ elements (Hereditary.map f (value S e (.set n child label) a)) ↔ _
    rw [Hereditary.elements_map]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e n child label a y).mp hy
      apply (mem_value_set T e n child label (f ∘ a) _).mpr
      refine ⟨i,f ∘ b,?_,(ih i b).symm⟩
      have heq : Sum.elim (f ∘ b) (f ∘ a) = f ∘ Sum.elim b a := by
        funext j; cases j <;> rfl
      rw [heq,← tupleType_iso S T e f hf,ht]
    · intro hx
      obtain ⟨i,b,ht,hx⟩ := (mem_value_set T e n child label (f ∘ a) x).mp hx
      let c := f.symm ∘ b
      have hc : f ∘ c = b := by funext j; simp [c]
      refine ⟨value S e (child i) c,?_,?_⟩
      · apply (mem_value_set S e n child label a _).mpr
        refine ⟨i,c,?_,rfl⟩
        rw [tupleType_iso S T e f hf]
        have heq : f ∘ Sum.elim c a = Sum.elim b (f ∘ a) := by
          funext j; cases j <;> simp [c]
        rw [heq,ht]
      · rw [ih,hc,hx]

end Form

def cross31 : J ⊕ J ↪ (J ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl j))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross42 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl (Sum.inr j)))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross34 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim (fun j => Sum.inl (Sum.inr j)) Sum.inr
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

theorem swap_type [Fintype J] [DecidableEq I] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I)
    (a b : J → A) (a' b' : J → B)
    (h : tupleType S e (Sum.elim a b) = tupleType T e (Sum.elim a' b')) :
    tupleType S e (Sum.elim b a) = tupleType T e (Sum.elim b' a') := by
  have ht := tupleType_project S T e e (Equiv.sumComm J J).toEmbedding _ _ h
  have h1 : Sum.elim a b ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b a := by
    funext j; cases j <;> rfl
  have h2 : Sum.elim a' b' ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b' a' := by
    funext j; cases j <;> rfl
  simpa only [h1,h2] using ht

@[simp] theorem elim_comp_cross31 (a b c : J → A) :
    Sum.elim (Sum.elim a b) c ∘ cross31 = Sum.elim c a := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross42 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross42 = Sum.elim d b := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross34 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross34 = Sum.elim c d := by
  funext j; cases j <;> rfl

section AtomicTransfer

variable [Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

variable (S : Structure R A) (T : Structure R B)

variable (e2 : J ⊕ J ↪ I) (e3 : (J ⊕ J) ⊕ J ↪ I)

variable (e4 : ((J ⊕ J) ⊕ J) ⊕ J ↪ I)

open Form

include e3 e4

private theorem set_subset_transfer
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hsub : ∀ x, x ∈ value S e2 (.set n child label) a →
      x ∈ value S e2 (.set k other lab) b) :
    ∀ x, x ∈ value T e2 (.set n child label) a' →
      x ∈ value T e2 (.set k other lab) b' := by
  intro x hx
  obtain ⟨i,c',hl,rfl⟩ := (mem_value_set T e2 n child label a' x).mp hx
  obtain ⟨c,h3⟩ := tupleType_append T S e2 e3 (Sum.elim a' b') (Sum.elim a b) c' ht.symm
  have hca := tupleType_project T S e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hca
  have hmem : value S e2 (child i) c ∈ value S e2 (.set n child label) a :=
    (mem_value_set S e2 n child label a _).mpr ⟨i,c,hca.symm.trans hl,rfl⟩
  obtain ⟨j,d,hlab,heq⟩ := (mem_value_set S e2 k other lab b _).mp (hsub _ hmem)
  obtain ⟨d',h4⟩ := tupleType_append S T e3 e4 (Sum.elim (Sum.elim a b) c)
    (Sum.elim (Sum.elim a' b') c') d h3.symm
  have hdb := tupleType_project S T e4 e2 cross42 _ _ h4
  have hcd := tupleType_project S T e4 e2 cross34 _ _ h4
  simp only [elim_comp_cross42] at hdb
  simp only [elim_comp_cross34] at hcd
  exact (mem_value_set T e2 k other lab b' _).mpr
    ⟨j,d',hdb.symm.trans hlab,((hc i j c d c' d' hcd).mp heq.symm).symm⟩

private theorem set_eq_forward
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (h : value S e2 (.set n child label) a = value S e2 (.set k other lab) b) :
    value T e2 (.set n child label) a' = value T e2 (.set k other lab) b' := by
  apply Hereditary.ext_sets (by simp) (by simp)
  intro x
  constructor
  · exact set_subset_transfer S T e2 e3 e4 n k child other label lab hc a b a' b' ht
      (fun z hz => by rw [←h]; exact hz) x
  · apply set_subset_transfer S T e2 e3 e4 k n other child lab label
      (fun j i c d c' d' ht' => ?_) b a b' a' (swap_type S T e2 a b a' b' ht)
      (fun z hz => by rw [h]; exact hz) x
    have hh := hc i j d c d' c' (swap_type S T e2 c d c' d' ht')
    exact ⟨fun he => (hh.mp he.symm).symm,fun he => (hh.mpr he.symm).symm⟩

theorem equality_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a = value S e2 ψ b ↔ value T e2 φ a' = value T e2 ψ b' := by
  induction φ generalizing ψ a b a' b' with
  | atom i =>
    cases ψ with
    | atom j =>
      have he := (typeOf_eq_iff S T (tupleNames e2) _ _).mp ht
        (.equal (e2 (.inl i)) (e2 (.inr j))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply,Sum.elim_inl,Sum.elim_inr,
        value_atom,Hereditary.atom_injective.eq_iff] using he
    | set k other lab =>
      have hfalseA : value S e2 (.atom i) a ≠ value S e2 (.set k other lab) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.atom i) a' ≠ value T e2 (.set k other lab) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
  | set n child label ih =>
    cases ψ with
    | atom j =>
      have hfalseA : value S e2 (.set n child label) a ≠ value S e2 (.atom j) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.set n child label) a' ≠ value T e2 (.atom j) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
    | set k other lab =>
      constructor
      · exact set_eq_forward S T e2 e3 e4 n k child other label lab
          (fun i j c d c' d' ht' => ih i (other j) c d c' d' ht') a b a' b' ht
      · exact set_eq_forward T S e2 e3 e4 n k child other label lab
          (fun i j c' d' c d ht' => (ih i (other j) c d c' d' ht'.symm).symm)
          a' b' a b ht.symm

private theorem membership_forward (φ : Form J (Set (Formula R I)))
    (k : ℕ) (other : Fin k → Form J (Set (Formula R I)))
    (lab : Fin k → Set (Formula R I))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hm : value S e2 φ a ∈ value S e2 (.set k other lab) b) :
    value T e2 φ a' ∈ value T e2 (.set k other lab) b' := by
  obtain ⟨i,c,hl,heq⟩ := (mem_value_set S e2 k other lab b _).mp hm
  obtain ⟨c',h3⟩ := tupleType_append S T e2 e3 (Sum.elim b a) (Sum.elim b' a') c
    (swap_type S T e2 a b a' b' ht)
  have hcb := tupleType_project S T e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hcb
  let u : J ⊕ J ↪ (J ⊕ J) ⊕ J :=
    cross31.trans (Function.Embedding.sumMap (Equiv.sumComm J J).toEmbedding
      (Function.Embedding.refl J))
  have hca := tupleType_project S T e3 e2 u _ _ h3
  have hueq (a b c : J → A) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  have hueq' (a b c : J → B) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  rw [hueq,hueq'] at hca
  exact (mem_value_set T e2 k other lab b' _).mpr ⟨i,c',hcb.symm.trans hl,
    (equality_transfer S T e2 e3 e4 (other i) φ c a c' a' hca).mp heq⟩

theorem membership_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a ∈ value S e2 ψ b ↔ value T e2 φ a' ∈ value T e2 ψ b' := by
  cases ψ with
  | atom j => simp
  | set k other lab =>
    exact ⟨membership_forward S T e2 e3 e4 φ k other lab a b a' b' ht,
      membership_forward T S e2 e3 e4 φ k other lab a' b' a b ht.symm⟩

end AtomicTransfer


variable {G : Type*} [Group G] [MulAction G A]

variable [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] {s : ℕ}

variable (S : Structure R A) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

open Form

include hAut in
omit [Fintype I] in
theorem value_smul (g : G) (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    g • value S e2 φ a = value S e2 φ (fun i => g • a i) := by
  exact value_iso S S e2 (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm) φ a

include hAut in
omit [Fintype I] in
theorem value_supported (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    Supports (G := G) a (value S e2 φ a) := by
  intro g hg
  rw [value_smul S e2 hAut]
  exact congrArg (value S e2 φ) (funext hg)

omit [Fintype A] [Nonempty A] in
private theorem hereditary_mem {x y : HF A}
    (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := by
  intro z hz
  exact hx z (hz.trans (Relation.ReflTransGen.single hy))

omit [Fintype A] [Nonempty A] in
private theorem hereditary_intro (x : HF A) (hx : Supported (G := G) s x)
    (hm : ∀ y ∈ x, HereditarilySupported (G := G) s y) :
    HereditarilySupported (G := G) s x := by
  intro y hy
  cases hy with
  | refl => exact hx
  | tail hpath hstep => exact hm _ hstep _ hpath

include hAut in
omit [Fintype I] in
theorem value_hereditarily_supported (φ : Form (Fin s) (Set (Formula R I)))
    (a : Fin s → A) : HereditarilySupported (G := G) s (value S e2 φ a) := by
  induction φ generalizing a with
  | atom i =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    exact (not_mem_atom y (a i) hy).elim
  | set n child label ih =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
    exact ih i b

omit [Fintype A] [Nonempty A] in
private theorem smul_mem (g : G) {x y : HF A} (h : y ∈ x) : g • y ∈ g • x := by
  change Hereditary.map (fun a => g • a) y ∈
    elements (Hereditary.map (fun a => g • a) x)
  let := Hereditary.instDecidableEqHF (A := A)
  rw [elements_map]
  exact Finset.mem_image.mpr ⟨y,h,rfl⟩

include hAut in
omit [Fintype I] in


theorem representation (hs : 0 < s)
    (hHom : ∀ p q : Fin s ⊕ Fin s → A,
      tupleType S e2 p = tupleType S e2 q → ∃ g : G, ∀ i, g • p i = q i)
    (x : HF A) (hx : HereditarilySupported (G := G) s x) :
    ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, value S e2 φ a = x := by
  induction x using mem_wellFounded.induction with
  | h x ih =>
    rcases atom_or_set x with ⟨b,rfl⟩ | hxset
    · exact ⟨.atom ⟨0,hs⟩,fun _ => b,rfl⟩
    · obtain ⟨a,ha⟩ := hx x Relation.ReflTransGen.refl
      have hr : ∀ y : {y // y ∈ elements x},
          ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ b : Fin s → A,
            value S e2 φ b = y.1 := by
        intro y
        exact ih y.1 y.2 (hereditary_mem hx y.2)
      choose form mol hvalue using hr
      let n := Fintype.card {y // y ∈ elements x}
      let en : Fin n ≃ {y // y ∈ elements x} := (Fintype.equivFin _).symm
      let child : Fin n → Form (Fin s) (Set (Formula R I)) := fun i => form (en i)
      let β : Fin n → Fin s → A := fun i => mol (en i)
      let label : Fin n → Set (Formula R I) := fun i => tupleType S e2 (Sum.elim (β i) a)
      refine ⟨.set n child label,a,?_⟩
      apply Hereditary.ext_sets (by simp) (by rw [hxset]; rfl)
      intro y
      constructor
      · intro hy
        obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
        obtain ⟨g,hg⟩ := hHom (Sum.elim (β i) a) (Sum.elim b a) ht.symm
        have hga : ∀ j, g • a j = a j := fun j => hg (.inr j)
        have hgb : (fun j => g • β i j) = b := funext (fun j => hg (.inl j))
        have hyx : (en i).1 ∈ x := (en i).2
        have hmap := smul_mem g hyx
        rw [ha g hga] at hmap
        have hv : value S e2 (child i) b = g • (en i).1 := by
          rw [←hgb,←value_smul S e2 hAut]
          exact congrArg (fun z : HF A => g • z) (hvalue (en i))
        rw [hv]
        exact hmap
      · intro hy
        let y' : {y // y ∈ elements x} := ⟨y,hy⟩
        let i := en.symm y'
        apply (mem_value_set S e2 n child label a y).mpr
        refine ⟨i,β i,rfl,?_⟩
        have hv := hvalue (en i)
        simpa only [child,β,i,Equiv.apply_symm_apply] using hv


end

end WitnessedSeparation.Forms



namespace WitnessedSeparation.Counting

noncomputable section

open Classical

variable {R I J A B : Type*} [DecidableEq I]

def triangular {X Y : Type*} (e : X ≃ Y) (f : X → A ≃ B) : X × A ≃ Y × B where
  toFun p := (e p.1, f p.1 p.2)
  invFun p := (e.symm p.1, (f (e.symm p.1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def snocTuple {n : ℕ} (a : Fin n → A) (x : A) : Fin (n+1) → A :=
  Fin.lastCases x a

@[simp] theorem snocTuple_castSucc {n : ℕ} (a : Fin n → A) (x : A) (i : Fin n) :
    snocTuple a x i.castSucc = a i := by simp [snocTuple]

@[simp] theorem snocTuple_last {n : ℕ} (a : Fin n → A) (x : A) :
    snocTuple a x (Fin.last n) = x := by simp [snocTuple]

def snocEquiv (n : ℕ) : (Fin (n+1) → A) ≃ (Fin n → A) × A where
  toFun a := (fun i => a i.castSucc, a (Fin.last n))
  invFun p := snocTuple p.1 p.2
  left_inv a := by
    funext i
    induction i using Fin.lastCases <;> simp
  right_inv p := by ext <;> simp

def appendPosition (J : Type*) (n : ℕ) : (J ⊕ Fin n) ⊕ Unit ≃ J ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun i => Sum.inr i.castSucc)) (fun _ => Sum.inr (Fin.last n))
  invFun := Sum.elim (fun j => Sum.inl (Sum.inl j))
    (Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)))
  left_inv p := by rcases p with (j|i)|u <;> simp
  right_inv p := by
    rcases p with j|i
    · rfl
    · induction i using Fin.lastCases <;> simp


variable [Fintype I] [Fintype J] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append_one_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ Unit ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : A ≃ B, ∀ x, tupleType S E (Sum.elim a (fun _ => x)) =
      tupleType T E (Sum.elim b (fun _ => f x)) := by
  let ep := Function.Embedding.inl.trans E
  let i := E (Sum.inr ())
  have hp := tupleType_project S T e ep (Function.Embedding.refl J) a b ht
  change tupleType S ep a = tupleType T ep b at hp
  have hi : i ∉ tupleNames ep := by
    rintro hh
    obtain ⟨j,hj⟩ := (mem_tupleNames ep i).mp hh
    have hh := E.injective hj
    cases hh
  have hn : insert i (tupleNames ep) = tupleNames E := by
    ext p
    simp only [Finset.mem_insert,mem_tupleNames]
    constructor
    · rintro (rfl|⟨j,rfl⟩)
      · exact ⟨Sum.inr (),rfl⟩
      · exact ⟨Sum.inl j,rfl⟩
    · rintro ⟨j,rfl⟩
      rcases j with j|u
      · exact Or.inr ⟨j,rfl⟩
      · cases u; exact Or.inl rfl
  have ha (x : A) : tupleType S E (Sum.elim a (fun _ => x)) =
      typeOf S (tupleNames E) (Function.update (tupleAssignment ep a) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep a j
    · cases u; simp [i]
  have hb (x : B) : tupleType T E (Sum.elim b (fun _ => x)) =
      typeOf T (tupleNames E) (Function.update (tupleAssignment ep b) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep b j
    · cases u; simp [i]
  obtain ⟨f,hf⟩ := extension_bijection S T (tupleNames ep) i hi
    (tupleAssignment ep a) (tupleAssignment ep b) hp
  refine ⟨f,fun x => ?_⟩
  rw [ha,hb]
  simpa only [hn] using hf x

theorem tupleType_append_fin_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (n : ℕ) (E : J ⊕ Fin n ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (Fin n → A) ≃ (Fin n → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  induction n with
  | zero =>
    let f : (Fin 0 → A) ≃ (Fin 0 → B) :=
      ⟨fun _ => Fin.elim0,fun _ => Fin.elim0,
        fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _⟩
    refine ⟨f,fun c => ?_⟩
    let u : J ⊕ Fin 0 ↪ J :=
      ⟨Sum.elim id Fin.elim0,by
        intro x y h
        rcases x with x|x
        · rcases y with y|y
          · exact congrArg Sum.inl h
          · exact Fin.elim0 y
        · exact Fin.elim0 x⟩
    have h := tupleType_project S T e E u a b ht
    have ha : a ∘ u = Sum.elim a c := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    have hb : b ∘ u = Sum.elim b (f c) := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    simpa only [ha,hb] using h
  | succ n ih =>
    let pre : J ⊕ Fin n ↪ J ⊕ Fin (n+1) :=
      Function.Embedding.sumMap (Function.Embedding.refl J) Fin.castSuccEmb
    let ep := pre.trans E
    obtain ⟨f,hf⟩ := ih ep
    let E1 := (appendPosition J n).toEmbedding.trans E
    have h1 (c : Fin n → A) : ∃ g : A ≃ B, ∀ x,
        tupleType S E1 (Sum.elim (Sum.elim a c) (fun _ => x)) =
        tupleType T E1 (Sum.elim (Sum.elim b (f c)) (fun _ => g x)) :=
      tupleType_append_one_bijection S T ep E1 _ _ (hf c)
    choose g hg using h1
    let F := (snocEquiv (A:=A) n).trans
      ((triangular f g).trans (snocEquiv (A:=B) n).symm)
    refine ⟨F,fun c => ?_⟩
    have hh := tupleType_project S T E1 E (appendPosition J n).symm.toEmbedding
      _ _ (hg (fun i => c i.castSucc) (c (Fin.last n)))
    have ha : (Sum.elim (Sum.elim a (fun i => c i.castSucc))
        (fun _ => c (Fin.last n))) ∘ (appendPosition J n).symm = Sum.elim a c := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;> simp [appendPosition]
    have hb : (Sum.elim (Sum.elim b (f (fun i => c i.castSucc)))
        (fun _ => g (fun i => c i.castSucc) (c (Fin.last n)))) ∘
        (appendPosition J n).symm = Sum.elim b (F c) := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;>
          simp [appendPosition,F,snocEquiv,triangular,snocTuple]
    simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_append_bijection {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (D → A) ≃ (D → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  let en := Fintype.equivFin D
  let E' := (Equiv.sumCongr (Equiv.refl J) en.symm).toEmbedding.trans E
  obtain ⟨f,hf⟩ := tupleType_append_fin_bijection S T e (Fintype.card D) E' a b ht
  let F := (Equiv.arrowCongr en (Equiv.refl A)).trans
    (f.trans (Equiv.arrowCongr en.symm (Equiv.refl B)))
  refine ⟨F,fun c => ?_⟩
  have hh := tupleType_project S T E' E
    (Equiv.sumCongr (Equiv.refl J) en).toEmbedding _ _ (hf (c ∘ en.symm))
  have ha : (Sum.elim a (c ∘ en.symm)) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim a c := by
    funext j; rcases j with j|j <;> simp
  have hb : (Sum.elim b (f (c ∘ en.symm))) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim b (F c) := by
    funext j; rcases j with j|j <;> rfl
  simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_extension_equiv {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) (τ : Set (Formula R I)) :
    Nonempty ({c : D → A // tupleType S E (Sum.elim a c) = τ} ≃
      {d : D → B // tupleType T E (Sum.elim b d) = τ}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T e E a b ht
  exact ⟨f.subtypeEquiv (fun c => by rw [hf c])⟩


end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.Forms

noncomputable section

open Classical Counting Hereditary

open scoped BigOperators

private theorem card_eq_mul_fiber {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (y₀ : Y)
    (h : ∀ y, Fintype.card {x // f x = y} = Fintype.card {x // f x = y₀}) :
    Fintype.card X = Fintype.card Y * Fintype.card {x // f x = y₀} := by
  calc
    Fintype.card X = Fintype.card (Σ y, {x // f x = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ y, Fintype.card {x // f x = y} := Fintype.card_sigma
    _ = _ := by simp only [h,Finset.sum_const,Finset.card_univ,smul_eq_mul]

private theorem card_eq_of_uniform_fibers {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (f : X → Y) (f' : X' → Y') (y : Y) (y' : Y')
    (hx : Fintype.card X = Fintype.card X')
    (hf : ∀ z, Fintype.card {x // f x = z} = Fintype.card {x // f x = y})
    (hf' : ∀ z, Fintype.card {x // f' x = z} = Fintype.card {x // f' x = y'})
    (hy : 0 < Fintype.card {x // f x = y})
    (he : Fintype.card {x // f x = y} = Fintype.card {x // f' x = y'}) :
    Fintype.card Y = Fintype.card Y' := by
  have h := (card_eq_mul_fiber f y hf).symm.trans
    (hx.trans (card_eq_mul_fiber f' y' hf'))
  rw [←he] at h
  exact Nat.eq_of_mul_eq_mul_right hy h

private theorem range_card_mul_fiber {X Y : Type*} [Fintype X]
    (f : X → Y) (x₀ : X)
    (h : ∀ x, Nat.card {z // f z = f x} = Nat.card {z // f z = f x₀}) :
    Fintype.card X = Nat.card (Set.range f) * Nat.card {z // f z = f x₀} := by
  let := (Set.finite_range f).fintype
  let fR : X → Set.range f := fun x => ⟨f x,⟨x,rfl⟩⟩
  have k (y : Set.range f) : Nat.card {x // fR x = y} =
      Nat.card {z // f z = f x₀} := by
    have hp (x : X) : fR x = y ↔ f x = y.1 := Subtype.ext_iff
    rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
    obtain ⟨x,hx⟩ := y.2
    rw [←hx]
    exact h x
  have hh := card_eq_mul_fiber fR (fR x₀) (fun y => by
    simpa only [←Nat.card_eq_fintype_card] using (k y).trans (k (fR x₀)).symm)
  have hh' : Nat.card X = Nat.card (Set.range f) * Nat.card {x // fR x = fR x₀} := by
    simpa only [←Nat.card_eq_fintype_card] using hh
  rw [k] at hh'
  simpa only [←Nat.card_eq_fintype_card] using hh'

variable {R I A B P : Type*} [Fintype I] [DecidableEq I]

variable [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [Fintype P]

variable {s : ℕ}

def Molecules (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) :=
  {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ}

instance (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) : Fintype (Molecules S ep p τ) :=
  inferInstanceAs (Fintype {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ})

def labelValues (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Set (HF A) :=
  Set.range (fun a : Molecules S ep p τ => Form.value S e2 φ a.1)

instance (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Fintype (labelValues S ep e2 p τ φ) :=
  (Set.finite_range _).fintype

section Group

variable {G : Type*} [Group G] [MulAction G A]

variable (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (p : P → A) (τ : Set (Formula R I))

include hAut in
omit [Fintype I] [Fintype A] in
private theorem mol_type_smul (g : G) (hp : ∀ i, g • p i = p i) (a : Fin s → A) :
    tupleType S ep (Sum.elim p (fun i => g • a i)) = tupleType S ep (Sum.elim p a) := by
  have hh := tupleType_iso S S ep (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm)
    (Sum.elim p a)
  have hh' : (MulAction.toPerm g) ∘ Sum.elim p a = Sum.elim p (fun i => g • a i) := by
    funext i; rcases i with i|i
    · exact hp i
    · rfl
  rw [hh'] at hh
  exact hh.symm

def moleculesPerm (g : G) (hp : ∀ i, g • p i = p i) :
    Molecules S ep p τ ≃ Molecules S ep p τ :=
  (Equiv.piCongrRight (fun _ : Fin s => MulAction.toPerm g)).subtypeEquiv
    (fun a => by
      change tupleType S ep (Sum.elim p a) = τ ↔
        tupleType S ep (Sum.elim p (fun i => g • a i)) = τ
      rw [mol_type_smul S ep hAut p g hp a])

include hAut in
omit [Fintype I] in


theorem uniform_value_fibers
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (a a' : Molecules S ep p τ) :
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} =
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a'.1} := by
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p a'.1) (a.2.trans a'.2.symm)
  have hp : ∀ i, g • p i = p i := fun i => hg (.inl i)
  have ha : (fun i => g • a.1 i) = a'.1 := funext (fun i => hg (.inr i))
  let f := moleculesPerm S ep hAut p τ g hp
  have hv (b : Molecules S ep p τ) :
      Form.value S e2 φ (f b).1 = g • Form.value S e2 φ b.1 := by
    exact (value_smul S e2 hAut g φ b.1).symm
  have hv' : Form.value S e2 φ a'.1 = g • Form.value S e2 φ a.1 := by
    rw [←ha]
    exact (value_smul S e2 hAut g φ a.1).symm
  apply Fintype.card_congr
  apply f.subtypeEquiv
  intro b
  rw [hv,hv']
  exact (MulAction.injective g).eq_iff.symm

include hAut in
omit [Fintype I] in
private theorem label_orbit
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (x y : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hy : y ∈ labelValues S ep e2 p τ φ) :
    ∃ g : G, (∀ i, g • p i = p i) ∧ g • x = y := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p b.1) (a.2.trans b.2.symm)
  refine ⟨g,fun i => hg (.inl i),?_⟩
  rw [value_smul S e2 hAut]
  exact congrArg (Form.value S e2 φ) (funext (fun i => hg (.inr i)))

include hAut in
omit [Fintype I] in
private theorem label_smul_mem (g : G) (hp : ∀ i, g • p i = p i)
    (φ : Form (Fin s) (Set (Formula R I))) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) : g • x ∈ labelValues S ep e2 p τ φ := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨moleculesPerm S ep hAut p τ g hp a,?_⟩
  exact (value_smul S e2 hAut g φ a.1).symm

include hAut in
omit [Fintype I] in


theorem label_partition
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (σ : Set (Formula R I)) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hx' : x ∈ labelValues S ep e2 p σ ψ) :
    labelValues S ep e2 p τ φ = labelValues S ep e2 p σ ψ := by
  ext y
  constructor
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p τ hHom φ x y hx hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p σ g hp ψ x hx'
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p σ hHom ψ x y hx' hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p τ g hp φ x hx

end Group


variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

private def skipMiddle : P ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inl (Function.Embedding.refl _)

private def lastTwo : Fin s ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inr (Function.Embedding.refl _)

omit [Fintype A] [Nonempty A] [Fintype P] in
@[simp] private theorem elim_skipMiddle (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ skipMiddle = Sum.elim p b := by
  funext j; cases j <;> rfl

omit [Fintype A] [Nonempty A] [Fintype P] in
@[simp] private theorem elim_lastTwo (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ lastTwo = Sum.elim a b := by
  funext j; cases j <;> rfl

include epp e3 e4 in




theorem value_fiber_equiv (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nonempty ({b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} ≃
    {b : Molecules T ep q τ // Form.value T e2 φ b.1 = Form.value T e2 φ a'.1}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T ep epp
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  have htype (b : Fin s → A) : tupleType S ep (Sum.elim p b) =
      tupleType T ep (Sum.elim q (f b)) := by
    have hh := tupleType_project S T epp ep skipMiddle _ _ (hf b)
    simpa only [elim_skipMiddle] using hh
  have hval (b : Fin s → A) : Form.value S e2 φ b = Form.value S e2 φ a.1 ↔
      Form.value T e2 φ (f b) = Form.value T e2 φ a'.1 := by
    have hh := tupleType_project S T epp e2 lastTwo _ _ (hf b)
    simp only [elim_lastTwo] at hh
    simpa only [eq_comm] using equality_transfer S T e2 e3 e4 φ φ a.1 b a'.1 (f b) hh
  let F : {b : Fin s → A // tupleType S ep (Sum.elim p b) = τ ∧
      Form.value S e2 φ b = Form.value S e2 φ a.1} ≃
      {b : Fin s → B // tupleType T ep (Sum.elim q b) = τ ∧
      Form.value T e2 φ b = Form.value T e2 φ a'.1} := f.subtypeEquiv (fun b => show
      (tupleType S ep (Sum.elim p b) = τ ∧ Form.value S e2 φ b = Form.value S e2 φ a.1) ↔
      (tupleType T ep (Sum.elim q (f b)) = τ ∧ Form.value T e2 φ (f b) = Form.value T e2 φ a'.1)
    from and_congr (by rw [htype b]) (hval b))
  exact ⟨(Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (F.trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)⟩

include epp e3 e4 in


theorem label_overlap_transfer (e0 : P ↪ I) (p : P → A) (q : P → B)
    (hp : tupleType S e0 p = tupleType T e0 q)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (τ σ : Set (Formula R I))
    (hx : ∃ x, x ∈ labelValues S ep e2 p τ φ ∧ x ∈ labelValues S ep e2 p σ ψ) :
    ∃ y, y ∈ labelValues T ep e2 q τ φ ∧ y ∈ labelValues T ep e2 q σ ψ := by
  obtain ⟨x,⟨a,ha⟩,⟨b,hb⟩⟩ := hx
  obtain ⟨a',ha'⟩ := tupleType_append S T e0 ep p q a.1 hp
  obtain ⟨b',hb'⟩ := tupleType_append S T ep epp
    (Sum.elim p a.1) (Sum.elim q a') b.1 ha'
  have ht := tupleType_project S T epp ep skipMiddle _ _ hb'
  simp only [elim_skipMiddle] at ht
  have he := tupleType_project S T epp e2 lastTwo _ _ hb'
  simp only [elim_lastTwo] at he
  have hv := (equality_transfer S T e2 e3 e4 φ ψ a.1 b.1 a' b' he).mp (ha.trans hb.symm)
  refine ⟨Form.value T e2 φ a',?_,?_⟩
  · exact ⟨⟨a',ha'.symm.trans a.2⟩,rfl⟩
  · exact ⟨⟨b',ht.symm.trans b.2⟩,hv.symm⟩

include epp e3 e4 in



theorem label_values_card
    {G H : Type*} [Group G] [MulAction G A] [Group H] [MulAction H B]
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nat.card (labelValues S ep e2 p τ φ) = Nat.card (labelValues T ep e2 q τ φ) := by
  let va : Molecules S ep p τ → HF A := fun b => Form.value S e2 φ b.1
  let vb : Molecules T ep q τ → HF B := fun b => Form.value T e2 φ b.1
  have ha := range_card_mul_fiber va a (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers S ep e2 hAutA p τ hHomA φ b a)
  have hb := range_card_mul_fiber vb a' (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers T ep e2 hAutB q τ hHomB φ b a')
  let e0 := Function.Embedding.inl.trans ep
  have hp := tupleType_project S T ep e0 Function.Embedding.inl
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  change tupleType S e0 p = tupleType T e0 q at hp
  obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp τ
  have hn : Fintype.card (Molecules S ep p τ) = Fintype.card (Molecules T ep q τ) :=
    Fintype.card_congr f
  obtain ⟨fv⟩ := value_fiber_equiv S T ep epp e2 e3 e4 p q τ φ a a'
  have he : Nat.card {b // va b = va a} = Nat.card {b // vb b = vb a'} :=
    Nat.card_congr fv
  have hpos : 0 < Nat.card {b // va b = va a} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨a,rfl⟩⟩
  have hc := ha.symm.trans (hn.trans hb)
  rw [←he] at hc
  have hh := Nat.eq_of_mul_eq_mul_right hpos hc
  simpa only [←Nat.card_eq_fintype_card,labelValues,va,vb] using hh


end

end WitnessedSeparation.Forms



namespace WitnessedSeparation

noncomputable section

open Classical

private def cellSetoid {L X : Type*} (C : L → Set X) : Setoid L :=
  ⟨fun l k => C l = C k,⟨fun _ => rfl,Eq.symm,Eq.trans⟩⟩

theorem glue_finite_cells {L X Y : Type*} (C : L → Set X) (D : L → Set Y)
    (coverC : ∀ x, ∃ l, x ∈ C l) (coverD : ∀ y, ∃ l, y ∈ D l)
    (partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k)
    (partD : ∀ l k y, y ∈ D l → y ∈ D k → D l = D k)
    (same : ∀ l k, C l = C k ↔ D l = D k)
    (finC : ∀ l, (C l).Finite) (finD : ∀ l, (D l).Finite)
    (card : ∀ l, Nat.card (C l) = Nat.card (D l)) :
    ∃ f : X ≃ Y, ∀ x, ∃ l, x ∈ C l ∧ f x ∈ D l := by
  let Q := Quotient (cellSetoid C)
  let lc : X → L := fun x => (coverC x).choose
  let ld : Y → L := fun y => (coverD y).choose
  have hc (x : X) : x ∈ C (lc x) := (coverC x).choose_spec
  have hd (y : Y) : y ∈ D (ld y) := (coverD y).choose_spec
  let c : X → Q := fun x => Quotient.mk _ (lc x)
  let d : Y → Q := fun y => Quotient.mk _ (ld y)
  have ce (x : X) (q : Q) : c x = q ↔ x ∈ C q.out := by
    constructor
    · intro h
      have he : C (lc x) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←he]; exact hc x
    · intro h
      have he := partC (lc x) q.out x (hc x) h
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have de (y : Y) (q : Q) : d y = q ↔ y ∈ D q.out := by
    constructor
    · intro h
      have he : C (ld y) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←(same _ _).mp he]; exact hd y
    · intro h
      have he := (same _ _).mpr (partD (ld y) q.out y (hd y) h)
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have ef (q : Q) : Nonempty ({x // c x = q} ≃ {y // d y = q}) := by
    let := (finC q.out).fintype
    let := (finD q.out).fintype
    have hcard : Fintype.card (C q.out) = Fintype.card (D q.out) := by
      simpa only [Nat.card_eq_fintype_card] using card q.out
    let e := Fintype.equivOfCardEq hcard
    exact ⟨(Equiv.subtypeEquivRight (fun x => ce x q)).trans
      (e.trans (Equiv.subtypeEquivRight (fun y => de y q)).symm)⟩
  let F := Equiv.ofFiberEquiv (fun q => Classical.choice (ef q))
  refine ⟨F,fun x => ⟨(c x).out,(ce x (c x)).mp rfl,?_⟩⟩
  apply (de (F x) (c x)).mp
  exact Equiv.ofFiberEquiv_map _ x

end

end WitnessedSeparation

end OAI
