import OAI.Computability.WLIdentification.NumericRefinement

namespace OAI

namespace WLIdentification

namespace NumericWL
open NumericKernel

theorem pair_bound {N a b : ℕ} (ha : a<N) (hb : b<N) : Nat.pair a b < Nat.pair N N+1 := by
  have h1 := Nat.pair_lt_pair_left b ha
  have h2 := Nat.pair_lt_pair_right N hb
  omega

theorem pairTable_lookup (N : ℕ) (p : ℕ → ℕ → Bool) (a b : Fin N) :
    lookup (pairTable N p) a b = p a b := by
  simp only [lookup, pairTable, List.getElem?_map,
    List.getElem?_range (pair_bound a.isLt b.isLt), Option.map_some, Option.getD_some, Nat.unpair_pair]

theorem transTable_lookup (N width branch : ℕ) (p : ℕ → ℕ → ℕ → ℕ → Bool)
    (a : Fin N) (z : Fin branch) (i : Fin width) (y : Fin N) :
    (transTable N width branch p)[Nat.pair a (Nat.pair z (Nat.pair i y))]?.getD false = p a z i y := by
  have h (a b c d : ℕ) (ha : a<c) (hb : b<d) : Nat.pair a b < Nat.pair c d :=
    (Nat.pair_lt_pair_left b ha).trans (Nat.pair_lt_pair_right c hb)
  have hh := h _ _ _ _ a.isLt (h _ _ _ _ z.isLt (h _ _ _ _ i.isLt y.isLt))
  simp only [transTable, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_lt hh),
    Option.map_some, Option.getD_some, Nat.unpair_pair]

abbrev sides (t : ℕ) : Fin t ⊕ Fin t ≃ Fin (t+t) := finSumFinEquiv

@[simp] theorem sides_inl (t : ℕ) (x : Fin t) : (sides t (.inl x)).val = x.val := rfl
@[simp] theorem sides_inr (t : ℕ) (x : Fin t) : (sides t (.inr x)).val = t+x.val := rfl
@[simp] theorem left_inl (t : ℕ) (x : Fin t) : left t (sides t (.inl x)) = true := by
  simp [left, x.isLt]
@[simp] theorem left_inr (t : ℕ) (x : Fin t) : left t (sides t (.inr x)) = false := by
  simp [left]
@[simp] theorem code_inl (t : ℕ) (x : Fin t) : code t (sides t (.inl x)) = x.val := by
  simp [code, x.isLt]
@[simp] theorem code_inr (t : ℕ) (x : Fin t) : code t (sides t (.inr x)) = x.val := by
  simp [code]

theorem equalCounts_correct {t : ℕ} (W : Word) {C : Type} [DecidableEq C]
    (c : Fin (t+t) → C) (hW : ∀ a b : Fin (t+t), lookup W a b = true ↔ c a = c b) :
    equalCounts t W = true ↔
    (Finset.univ.val.map (fun x => c (sides t (.inl x)))) =
    (Finset.univ.val.map (fun x => c (sides t (.inr x)))) := by
  let L : Multiset (Fin (t+t)) := Finset.univ.val.map (fun x => sides t (.inl x))
  let R : Multiset (Fin (t+t)) := Finset.univ.val.map (fun x => sides t (.inr x))
  suffices h : equalCounts t W = true ↔ L.map c = R.map c by
    simpa only [L, R, Multiset.map_map, Function.comp_def] using h
  rw [FiniteRefinement.map_eq_iff_counts]
  simp only [equalCounts, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  have hc (a : Fin (t+t)) (f : Fin t → Fin (t+t)) :
      ((Finset.univ : Finset (Fin t)).val.map f).countP (fun b => c b = c a) =
      ∑ b : Fin t, if lookup W (f b) a then 1 else 0 := by
    rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter, multiset_countP_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [hW]
  constructor
  · intro h a
    rw [hc, hc]
    have he := h a a.isLt
    simp only [sum_range_fin, sides_inl, sides_inr] at he ⊢
    convert he using 1 <;> rfl
  · intro h a ha
    have he := h ⟨a,ha⟩
    rw [hc, hc] at he
    simp only [sum_range_fin, sides_inl, sides_inr] at he ⊢
    convert he using 1 <;> rfl

def neighborData (n : ℕ) (W V : Word) : Data (n+n) 1 n where
  active a z := neighborActive n W V a z
  next a z _ := sides n (match (sides n).symm a with | .inl _ => .inl z | .inr _ => .inr z)

theorem neighborEncoded (n : ℕ) (W V : Word) :
    Encoded (neighborData n W V)
      (pairTable (n+n) (neighborActive n W V)) (transTable (n+n) 1 n (neighborTrans n)) := by
  constructor
  · intro a z
    exact pairTable_lookup _ _ a ⟨z.val,by omega⟩
  · intro a z i y
    rw [transTable_lookup]
    obtain ⟨a,rfl⟩ := (sides n).surjective a
    obtain ⟨y,rfl⟩ := (sides n).surjective y
    cases a <;> cases y <;>
      simp only [neighborTrans, neighborData, Equiv.symm_apply_apply, left_inl, left_inr,
        code_inl, code_inr, Equiv.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, decide_true, decide_false,
        Bool.true_and, Fin.ext_iff]
    all_goals simp [eq_comm]

def nc (n : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : Fin (n+n)) : NeighborColor s :=
  FiniteWL.neighbor (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) s ((sides n).symm a)

theorem neighbor_vectors (n : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : Fin n ⊕ Fin n) :
    ((neighborData n W V).vectors (sides n a)).map (fun v i => nc n W V hW hV s (v i)) =
    ((FiniteWL.neighbors (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) a).map
      (FiniteWL.neighbor (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) s)).map
      (fun c (_ : Fin 1) => c) := by
  cases a <;>
    simp only [Data.vectors, neighborData, neighborActive, selectedEdge, nc, FiniteWL.neighbors,
      NumericGraph.ofWord, Multiset.map_map, Function.comp_def, Equiv.symm_apply_apply,
      left_inl, left_inr, code_inl, code_inr, Bool.false_eq_true,
      ↓reduceIte, Finset.filter_val]

theorem neighbor_correct (n cap : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true) (hcap : n+n ≤ cap) :
    neighbor n cap W V = true ↔
    Equivalent 1 (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) := by
  classical
  let c := nc n W V hW hV
  have hnext (s : ℕ) (a b : Fin (n+n)) : c (s+1) a = c (s+1) b ↔ c s a = c s b ∧
      ((neighborData n W V).vectors a).map (fun v i => c s (v i)) =
      ((neighborData n W V).vectors b).map (fun v i => c s (v i)) := by
    obtain ⟨a,rfl⟩ := (sides n).surjective a
    obtain ⟨b,rfl⟩ := (sides n).surjective b
    rw [neighbor_vectors, neighbor_vectors]
    have hinj : Function.Injective (fun x : NeighborColor s => fun _ : Fin 1 => x) :=
      fun x y h => congrFun h 0
    rw [(Multiset.map_injective hinj).eq_iff]
    simp only [c, nc, Equiv.symm_apply_apply]
    exact FiniteWL.neighbor_update (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) s a b
  have hi (a b : Fin (n+n)) : true = true ↔ c 0 a = c 0 b := by
    exact iff_of_true rfl (@Subsingleton.elim Unit inferInstance _ _)
  have hr : Represents (pairTable (n+n) (fun _ _ => true)) (fun _ _ : Fin (n+n) => true) :=
    pairTable_lookup _ _
  have htab := table_correct (neighborData n W V) (neighborEncoded n W V) hr cap
    (by simpa using hcap) ((n+n)^2)
  have hc (a b : Fin (n+n)) := FiniteRefinement.table_correct c (neighborData n W V).vectors hnext
      (fun _ _ => true) hi ((n+n)^2) a b
  rw [neighbor, ← pow_two, equalCounts_correct _ (c ((n+n)^2)) (fun a b => by rw [htab a b]; exact hc a b)]
  rw [FiniteWL.equivalent_cutoff]
  simp only [↓reduceIte, c, nc, Equiv.symm_apply_apply, FiniteWL.neighbor, Sum.elim_inl,
    Sum.elim_inr, neighborHistogram, NumericGraph.ofWord]

end NumericWL

namespace NumericWL
open NumericKernel

abbrev tuples (n k : ℕ) := (Fin k → Fin n) ⊕ (Fin k → Fin n)

def te (n k : ℕ) : tuples n k ≃ Fin (n^k+n^k) :=
  (Equiv.sumCongr finFunctionFinEquiv finFunctionFinEquiv).trans (sides (n^k))

@[simp] theorem te_inl (n k : ℕ) (v : Fin k → Fin n) :
    te n k (.inl v) = sides (n^k) (.inl (finFunctionFinEquiv v)) := rfl
@[simp] theorem te_inr (n k : ℕ) (v : Fin k → Fin n) :
    te n k (.inr v) = sides (n^k) (.inr (finFunctionFinEquiv v)) := rfl

@[simp] theorem te_symm_inl (n k : ℕ) (x : Fin (n^k)) :
    (te n k).symm (sides (n^k) (.inl x)) = .inl (finFunctionFinEquiv.symm x) := by
  change Sum.map finFunctionFinEquiv.symm finFunctionFinEquiv.symm
    ((sides (n^k)).symm ((sides (n^k)) _)) = _
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem te_symm_inr (n k : ℕ) (x : Fin (n^k)) :
    (te n k).symm (sides (n^k) (.inr x)) = .inr (finFunctionFinEquiv.symm x) := by
  change Sum.map finFunctionFinEquiv.symm finFunctionFinEquiv.symm
    ((sides (n^k)).symm ((sides (n^k)) _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem digit_function {n k : ℕ} (v : Fin k → Fin n) (i : Fin k) :
    digit n (finFunctionFinEquiv v) i = (v i).val :=
  congrArg (fun f => (f i).val) (finFunctionFinEquiv.symm_apply_apply v)

def tupleData (n k : ℕ) : Data (n^k+n^k) k n where
  active _ _ := true
  next a z i := te n k (match (te n k).symm a with
    | .inl v => .inl (Function.update v i z)
    | .inr v => .inr (Function.update v i z))

theorem digits_update {n k : ℕ} (v w : Fin k → Fin n) (i : Fin k) (z : Fin n) :
    (∀ j<k, digit n (finFunctionFinEquiv w) j =
      if j=i.val then z.val else digit n (finFunctionFinEquiv v) j) ↔ Function.update v i z = w := by
  constructor
  · intro h
    funext j
    apply Fin.ext
    have hh := h j j.isLt
    rw [digit_function w j, digit_function v j] at hh
    by_cases he : j=i
    · subst j
      simpa only [Function.update_self, ↓reduceIte] using hh.symm
    · have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
      simpa only [Function.update_of_ne he, hn, ↓reduceIte] using hh.symm
  · rintro rfl j hj
    let jj : Fin k := ⟨j,hj⟩
    rw [digit_function (Function.update v i z) jj, digit_function v jj]
    by_cases he : jj=i
    · have hv : j=i.val := congrArg Fin.val he
      simp only [he, Function.update_self, hv, ↓reduceIte]
    · have hn : j ≠ i.val := fun h => he (Fin.ext h)
      simp only [Function.update_of_ne he, hn, ↓reduceIte]

theorem tupleEncoded (n k : ℕ) (hk : 0<k) : Encoded (tupleData n k)
    (pairTable (n^k+n^k) (fun _ _ => true))
    (transTable (n^k+n^k) k n (tupleTrans n k (n^k))) := by
  constructor
  · intro a z
    unfold lookup pairTable
    -- Active is true; this table stores slots at least as far as every branch.
    have hz : z.val < n^k+n^k := by
      have hn : 0<n := Nat.zero_lt_of_lt z.isLt
      have hn' : n ≤ n^k := by simpa using Nat.pow_le_pow_right hn hk
      omega
    simp only [List.getElem?_map, List.getElem?_range (pair_bound a.isLt hz),
      Option.map_some, Option.getD_some, tupleData]
  · intro a z i y
    rw [transTable_lookup]
    obtain ⟨a,rfl⟩ := (te n k).surjective a
    obtain ⟨y,rfl⟩ := (te n k).surjective y
    simp only [tupleData, Equiv.symm_apply_apply]
    cases a <;> cases y <;>
      simp only [Equiv.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [tupleTrans, te_inl, te_inr, left_inl, left_inr, code_inl, code_inr,
      Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    all_goals first | simpa only [true_and] using digits_update _ _ _ _ | simp

end NumericWL

namespace NumericWL
open NumericKernel

def tc (n k : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : Fin (n^k+n^k)) : TupleColor k s :=
  FiniteWL.tuple (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k s ((te n k).symm a)

theorem tuple_vectors (n k : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : tuples n k) :
    ((tupleData n k).vectors (te n k a)).map (fun v i => tc n k W V hW hV s (v i)) =
    (FiniteWL.vectors (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k a).map
      (fun v i => FiniteWL.tuple (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k s (v i)) := by
  cases a <;>
    simp only [Data.vectors, tupleData, tc, FiniteWL.vectors, Equiv.symm_apply_apply,
      Finset.filter_true, Multiset.map_map, Function.comp_def]

theorem forall_bound2 {k : ℕ} {p : ℕ → ℕ → Prop} :
    (∀ i<k, ∀ j<k, p i j) ↔ ∀ i j : Fin k, p i j := by
  exact ⟨fun h i j => h i i.isLt j j.isLt, fun h i hi j hj => h ⟨i,hi⟩ ⟨j,hj⟩⟩

theorem tupleInitial_correct (n k : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (a b : Fin (n^k+n^k)) : tupleInitial n k (n^k) W V a b = true ↔ tc n k W V hW hV 0 a = tc n k W V hW hV 0 b := by
  obtain ⟨a,rfl⟩ := (te n k).surjective a
  obtain ⟨b,rfl⟩ := (te n k).surjective b
  simp only [tc, Equiv.symm_apply_apply]
  cases a <;> cases b <;>
    dsimp only [FiniteWL.tuple, Sum.elim, tupleColor, TupleColor]
  all_goals
    simp only [
      Prod.mk.injEq, funext_iff, tupleInitial, List.all_eq_true, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, forall_bound2, te_inl, te_inr, code_inl, code_inr,
      digit_function, selectedEdge, left_inl, left_inr, Bool.false_eq_true, ↓reduceIte,
      Fin.ext_iff, decide_eq_decide, forall_and, eq_iff_iff]

theorem tuple_correct (n k cap : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (hk : 0<k) (hk1 : k≠1) (ht : n^k ≤ cap) (hcap : (n^k+n^k)^k ≤ cap) :
    tuple n k cap W V = true ↔
    Equivalent k (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) := by
  classical
  let c := tc n k W V hW hV
  have hnext (s : ℕ) (a b : Fin (n^k+n^k)) : c (s+1) a = c (s+1) b ↔ c s a = c s b ∧
      ((tupleData n k).vectors a).map (fun v i => c s (v i)) =
      ((tupleData n k).vectors b).map (fun v i => c s (v i)) := by
    obtain ⟨a,rfl⟩ := (te n k).surjective a
    obtain ⟨b,rfl⟩ := (te n k).surjective b
    rw [tuple_vectors, tuple_vectors]
    simp only [c, tc, Equiv.symm_apply_apply]
    exact FiniteWL.tuple_update (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k s a b
  have hi := tupleInitial_correct n k W V hW hV
  have hr : Represents (pairTable (n^k+n^k) (tupleInitial n k (n^k) W V))
      (fun a b : Fin (n^k+n^k) => tupleInitial n k (n^k) W V a b) := pairTable_lookup _ _
  have htab := table_correct (tupleData n k) (tupleEncoded n k hk) hr cap hcap ((n^k+n^k)^2)
  have hc (a b : Fin (n^k+n^k)) := FiniteRefinement.table_correct c (tupleData n k).vectors hnext
      (fun a b => tupleInitial n k (n^k) W V a b) hi ((n^k+n^k)^2) a b
  rw [tuple, min_eq_left ht, ← pow_two,
    equalCounts_correct _ (c ((n^k+n^k)^2)) (fun a b => by rw [htab a b]; exact hc a b)]
  rw [FiniteWL.equivalent_cutoff, ite_eq_right hk1]
  have he (X : Graph) (s : ℕ) :
      (Finset.univ : Finset (Fin (X.order^k))).val.map (fun x =>
        tupleColor X k s (finFunctionFinEquiv.symm x)) = tupleHistogram X k s := by
    unfold tupleHistogram
    rw [← Multiset.map_univ_val_equiv (finFunctionFinEquiv.symm : Fin (X.order^k) ≃ (Fin k → Fin X.order)),
      Multiset.map_map]
    rfl
  -- The concrete equality below is proved by multiset reindexing, without
  -- identifying tuple colors pointwise between distinct dimension types.
  simp only [c, tc, te_symm_inl, te_symm_inr, FiniteWL.tuple, Sum.elim_inl, Sum.elim_inr]
  rw [he (NumericGraph.ofWord n W hW) ((n^k+n^k)^2), he (NumericGraph.ofWord n V hV) ((n^k+n^k)^2)]

end NumericWL

namespace WordExpressions.Poly
variable {n : ℕ}

theorem eqtest {u v : (Fin n → Word) → Word} (hu : Poly u) (hv : Poly v) :
    BoolPoly (fun S => decide (u S=v S)) := by
  have h := BoolPoly.and (NatPoly.eqtest (NatPoly.length hu) (NatPoly.length hv))
    (BoolPoly.allRange (p := fun S i => decide ((u S)[i]?.getD false = (v S)[i]?.getD false)) (NatPoly.length hu) (BoolPoly.eqtest
      (Poly.nth (hu.rename Fin.castSucc) (NatPoly.var (Fin.last n)))
      (Poly.nth (hv.rename Fin.castSucc) (NatPoly.var (Fin.last n)))))
  apply h.congr
  intro S
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hl,h⟩
    apply List.ext_getElem hl
    intro i hi hi'
    have hh := h i hi
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some] using hh
  · intro he
    rw [he]
    exact ⟨rfl, fun _ _ => rfl⟩

end WordExpressions.Poly

end WLIdentification

end OAI
