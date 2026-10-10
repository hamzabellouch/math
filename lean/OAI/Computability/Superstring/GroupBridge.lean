import OAI.Computability.Superstring.LexCode

namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical LayerArray
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def data (K : Code α) (g : ℕ) : GroupData α :=
  (layerWord K g,(List.range (aligned K g).length).map (layerExits K g))

@[fun_prop] theorem poly_data : Poly (fun q : Code α × ℕ => data q.1 q.2) := by
  have hm : Poly (fun q : Code α × ℕ => (List.range (aligned q.1 q.2).length).map (layerExits q.1 q.2)) :=
    BitCode.Poly.mapFn (f := fun q : (Code α × ℕ) × ℕ => layerExits q.1.1 q.1.2 q.2) (by fun_prop) (by fun_prop)
  unfold data
  fun_prop

theorem data_represents {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) :
    LayerArray.Represents (data K g.val).1 (exits (data K g.val) j.val)
      (C.layer closed (period_spec h g).1.periodic j) := by
  have he : exits (data K g.val) j.val = layerExits K g.val j.val := by
    have hj : j.val < (aligned K g.val).length := by rw [aligned_length h]; exact j.isLt
    simp only [exits,data,List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some]
  refine ⟨text_layerWord h g,length_layerWord h g,?_⟩
  · funext x
    rw [he,exit_layerExits K g.val j.val (period_spec h g).1.positive,exit_eq h closed]

theorem data_size {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    (data K g.val).2.length = Fintype.card (C.Aligned (C.text g)) := by
  simp only [data,List.length_map,List.length_range,aligned_length h]

omit [Coded α] in
theorem aligned_length_le (K : Code α) (g : ℕ) : (aligned K g).length ≤ K.1.length := by
  exact (List.length_filter_le ..).trans_eq List.length_range

omit [Coded α] in
theorem letters_mem {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (g : Fin K.1.length) (x : ℤ) : [C.text g x] ∈ V := by
  exact (C.layer closed (period_spec h g).1.periodic
    ⟨0,Fintype.card_pos_iff.mpr ⟨⟨g,rfl⟩⟩⟩).letters closed x
end Superstring.ThreadArray


namespace Superstring.UpperCode
open BitCode Hierarchical WalkCode LayerArray
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Book (α : Type) := List (List α × List ℕ)
def lookup (B : Book α) (i : ℕ) : List α × List ℕ := B[i]?.getD ([],[])
def upper (m cut : ℕ) : List ℕ := (List.range m).filter (lessEq cut)
@[simp] theorem mem_upper (m cut i : ℕ) : i ∈ upper m cut ↔ cut ≤ i ∧ i < m := by
  simp only [upper,List.mem_filter,List.mem_range,lessEq,decide_eq_true_eq,and_comm]
theorem length_upper (m cut : ℕ) : (upper m cut).length = m-cut := by
  have he : (upper m cut).toFinset = Finset.Ico cut m := by ext i; simp
  have hn : (upper m cut).Nodup := List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hn,he,Nat.card_Ico]
theorem upper_filter {m cut lo : ℕ} (h : cut ≤ lo) :
    (upper m cut).filter (lessEq lo) = upper m lo := by
  simp only [upper,List.filter_filter]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,lessEq,decide_eq_true_eq]
  omega

abbrev Param := ℕ × ℕ × RecordCode.Code
def params (B : Book α) (ids : List ℕ) (m M : ℕ) (t : ℤ) : List Param :=
  (List.range (m+1)).flatMap (fun k => ids.flatMap (fun i =>
    (RecordCode.pool (lookup B i).1.length M t).map (fun r => (k,i,r))))

def test (D : GroupData α) (B : Book α) (cut : ℕ) (t : ℤ) (v : Param) : Bool :=
  let m := D.2.length
  let p := D.1.length
  let k := v.1
  let T := lookup B v.2.1
  let r := v.2.2
  less 0 k && lessEq k (m-cut) &&
    RecordCode.check D.1 T.1 T.2 r &&
    decide (RecordCode.start r ≤ t) && decide (t < RecordCode.stop r) &&
    decide (GeoCode.first (exits D (m-1)) t ≤ RecordCode.stop r+(k*p : ℕ)) &&
    decide (GeoCode.first (exits D (m-1)) t-GeoCode.exit (exits D (m-k)) t ≤ ((k-1)*p : ℕ)) &&
    ((upper m cut).filter (fun i => less i (m-k))).all
      (fun i => decide (GeoCode.first (exits D i) (RecordCode.start r) ≤ RecordCode.stop r))

-- A foreign-text filter is deliberately separate: its equality test uses only
-- a common product period, not a potentially unbounded infinite stream.
def choose (D : GroupData α) (B : Book α) (ids : List ℕ) (cut M : ℕ) (t : ℤ)
    (foreign : Param → Bool) : Param :=
  ((params B ids D.2.length M t).filter (fun v => test D B cut t v && foreign v)).headD (0,0,0,0,0)

omit [Inhabited α] [DecidableEq α] in
theorem params_mem {B : Book α} {ids : List ℕ} {m M k i : ℕ} {t : ℤ} {r : RecordCode.Code}
    (hk : k ≤ m) (hi : i ∈ ids) (hr : r ∈ RecordCode.pool (lookup B i).1.length M t) :
    (k,i,r) ∈ params B ids m M t := by
  exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (by omega),List.mem_flatMap.mpr
    ⟨i,hi,List.mem_map.mpr ⟨r,hr,rfl⟩⟩⟩

theorem choose_spec (D : GroupData α) (B : Book α) (ids : List ℕ) (cut M : ℕ) (t : ℤ)
    (foreign : Param → Bool)
    (hex : ∃ v ∈ params B ids D.2.length M t, test D B cut t v = true ∧ foreign v = true) :
    let v := choose D B ids cut M t foreign
    v ∈ params B ids D.2.length M t ∧ test D B cut t v = true ∧ foreign v = true := by
  let vs := (params B ids D.2.length M t).filter (fun v => test D B cut t v && foreign v)
  have hn : vs ≠ [] := by
    obtain ⟨v,hv,ht,hf⟩ := hex
    have hm : v ∈ vs := List.mem_filter.mpr ⟨hv,by simp only [ht,hf,Bool.and_true]⟩
    exact List.ne_nil_of_mem hm
  have hm : vs.headD (0,0,0,0,0) ∈ vs := by
    cases he : vs with
    | nil => exact False.elim (hn he)
    | cons a as => simp
  simpa only [vs,List.mem_filter,Bool.and_eq_true,choose] using hm

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_lookup : Poly (fun q : Book α × ℕ => lookup q.1 q.2) := by
  exact BitCode.Poly.getD ([],[])
@[fun_prop] theorem poly_upper : Poly (fun q : ℕ × ℕ => upper q.1 q.2) := by
  unfold upper
  exact BitCode.Poly.filterFn (p := fun q : (ℕ × ℕ) × ℕ => lessEq q.1.2 q.2) (by fun_prop) (by fun_prop)
abbrev ParamsInput (α : Type) := Book α × List ℕ × ℕ × ℕ × ℤ
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_params : Poly (fun q : ParamsInput α => params q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold params
  apply BitCode.Poly.flatMapFn (f := fun q : ParamsInput α × ℕ => q.1.2.1.flatMap (fun i =>
    (RecordCode.pool (lookup q.1.1 i).1.length q.1.2.2.2.1 q.1.2.2.2.2).map (fun r => (q.2,i,r))))
  · apply BitCode.Poly.flatMapFn (f := fun q : (ParamsInput α × ℕ) × ℕ =>
      (RecordCode.pool (lookup q.1.1.1 q.2).1.length q.1.1.2.2.2.1 q.1.1.2.2.2.2).map (fun r => (q.1.2,q.2,r)))
    · exact BitCode.Poly.mapFn (f := fun q : ((ParamsInput α × ℕ) × ℕ) × RecordCode.Code =>
        (q.1.1.2,q.1.2,q.2)) (by fun_prop) (by fun_prop)
    · fun_prop
  · fun_prop
abbrev TestInput (α : Type) := GroupData α × Book α × ℕ × ℤ × Param
instance codedTestInput : Coded (TestInput α) := codedProd
@[fun_prop] theorem poly_test : Poly (fun q : TestInput α => test q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold test
  dsimp only
  have ha : Poly (fun q : TestInput α =>
      ((upper q.1.2.length q.2.2.1).filter (fun i => less i (q.1.2.length-q.2.2.2.2.1))).all
        (fun i => decide (GeoCode.first (exits q.1 i) (RecordCode.start q.2.2.2.2.2.2) ≤ RecordCode.stop q.2.2.2.2.2.2))) := by
    apply BitCode.Poly.allFn (p := fun q : TestInput α × ℕ =>
      decide (GeoCode.first (exits q.1.1 q.2) (RecordCode.start q.1.2.2.2.2.2.2) ≤ RecordCode.stop q.1.2.2.2.2.2.2))
    · unfold RecordCode.start RecordCode.stop
      fun_prop
    · exact BitCode.Poly.filterFn (p := fun q : TestInput α × ℕ => less q.2 (q.1.1.2.length-q.1.2.2.2.2.1)) (by fun_prop) (by fun_prop)
  have hr : Poly (fun q : TestInput α => RecordCode.check q.1.1 (lookup q.2.1 q.2.2.2.2.2.1).1 (lookup q.2.1 q.2.2.2.2.2.1).2 q.2.2.2.2.2.2) :=
    RecordCode.poly_check.comp (f := fun q : TestInput α => ((q.1.1,(lookup q.2.1 q.2.2.2.2.2.1).1,(lookup q.2.1 q.2.2.2.2.2.1).2),q.2.2.2.2.2.2)) (by fun_prop)
  unfold RecordCode.start RecordCode.stop at *
  fun_prop
end Superstring.UpperCode


namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α : Type} [Inhabited α] [DecidableEq α]

def different (U W : List α) (d : ℤ) : Bool :=
  !equal (window U 0 (U.length*W.length : ℕ)) (window W d (d+(U.length*W.length : ℕ)))

theorem different_iff (U W : List α) (d : ℤ) (hU : 0 < U.length) (hW : 0 < W.length) :
    different U W d = true ↔ text U ≠ fun x => text W (x+d) := by
  have hm : 0 < U.length*W.length := Nat.mul_pos hU hW
  have perU : Function.Periodic (text U) ((U.length*W.length : ℕ) : ℤ) := by
    simpa only [nsmul_eq_mul,Nat.cast_mul,mul_comm] using (periodic U).nsmul W.length
  have perW : Function.Periodic (fun x => text W (x+d)) ((U.length*W.length : ℕ) : ℤ) := by
    have hp := (periodic W).nsmul U.length
    intro x
    simpa only [nsmul_eq_mul,Nat.cast_mul,add_right_comm] using hp (x+d)
  have he : window U 0 (U.length*W.length : ℕ) = window W d (d+(U.length*W.length : ℕ)) ↔
      text U = fun x => text W (x+d) := by
    rw [window_eq,window_eq]
    have hr := textWord_reindex (text W) d 0 (U.length*W.length : ℕ)
    simp only [zero_add] at hr
    rw [add_comm d,← hr]
    constructor
    · intro h
      funext x
      let r := x % ((U.length*W.length : ℕ) : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
      have hrm : r < (U.length*W.length : ℕ) := Int.emod_lt_of_pos _ (by omega)
      have hri : r.toNat < U.length*W.length := by omega
      have ha := congrArg (fun w : List α => w[r.toNat]?) h
      simp only [textWord,List.getElem?_ofFn] at ha
      have hlen : (((U.length*W.length : ℕ) : ℤ)-0).toNat = U.length*W.length := by omega
      simp only [hlen,hri,↓reduceDIte,zero_add,Option.some.injEq,Int.toNat_of_nonneg hr0] at ha
      have hu := periodic_emod (text U) ((U.length*W.length : ℕ) : ℤ) perU x
      have hw := periodic_emod (fun x => text W (x+d)) ((U.length*W.length : ℕ) : ℤ) perW x
      exact hu.symm.trans (ha.trans hw)
    · intro h
      rw [h]
  simpa only [different,equal,Bool.not_eq_true',decide_eq_false_iff_not] using not_congr he

variable [Coded α]
@[fun_prop] theorem poly_different : Poly (fun q : List α × List α × ℤ => different q.1 q.2.1 q.2.2) := by
  unfold different
  fun_prop
end Superstring.PeriodWord


namespace Superstring.UpperCode
open BitCode Hierarchical LayerArray
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

def foreign (D : GroupData α) (B : Book α) (v : Param) : Bool :=
  PeriodWord.different D.1 (lookup B v.2.1).1 (RecordCode.offset v.2.2)

theorem supply_params (C : LayerCollection V G) (g : G) (supply : C.RecordSupply)
    (D : GroupData α) (B : Book α) (ids : List ℕ) (encode : C.Id → ℕ)
    (hsize : D.2.length = C.size g)
    (hD : ∀ i : Fin (C.size g), Represents D.1 (exits D i.val) (C.layer g i))
    (hB : ∀ i : C.Id, Represents (lookup B (encode i)).1 (lookup B (encode i)).2 (C.layerAt i))
    (hids : ∀ i, encode i ∈ ids) (M : ℕ) (len : ∀ w ∈ V, w.length ≤ M)
    (cut : ℕ) (hcut : cut < C.size g)
    (he : ¬ (C.layer g ⟨C.size g-1,by have := C.nonempty g; omega⟩).first (C.distinguished g) - C.distinguished g
      ≤ ((C.size g-cut)*C.period g : ℕ))
    (hb : ¬ ∃ base : Fin (C.size g), base.val+1=cut ∧
      (C.layer g ⟨C.size g-1,by have := C.nonempty g; omega⟩).first (C.distinguished g) -
        (C.layer g base).last (C.distinguished g) ≤ ((C.size g-cut)*C.period g : ℕ)) :
    ∃ v ∈ params B ids D.2.length M (C.distinguished g),
      test D B cut (C.distinguished g) v = true ∧ foreign D B v = true := by
  classical
  let n := C.size g-cut
  let top : Fin (C.size g) := ⟨C.size g-1,by have := C.nonempty g; omega⟩
  let t := C.distinguished g
  let H := (C.layer g top).first t
  have hn : 0 < n := by dsimp only [n]; omega
  have hnm : n ≤ C.size g := Nat.sub_le ..
  have hz : Monotone (fun i : Fin (C.size g) => (C.layer g i).last t) :=
    fun i j hij => C.ordered g i j hij t
  have hstopn : (Processing.qualifying (fun i => (C.layer g i).last t) H (C.period g) n).card ≤ n := by
    by_cases hzero : cut = 0
    · have hh := Finset.card_le_univ (Processing.qualifying (fun i => (C.layer g i).last t) H (C.period g) n)
      simpa only [Fintype.card_fin,n,hzero,Nat.sub_zero] using hh
    · let base : Fin (C.size g) := ⟨cut-1,by omega⟩
      have hfail : (C.layer g base).last t < H-(n*C.period g : ℕ) := by
        by_contra hh
        apply hb
        exact ⟨base,by dsimp only [base]; omega,by dsimp only [H,t,n,top] at hh ⊢; omega⟩
      have hh := Processing.qualifying_bound _ hz H (C.period g) n base hfail
      change _ ≤ C.size g-1-(cut-1) at hh
      dsimp only [n] at hh ⊢
      omega
  obtain ⟨k,hk,hkn,hstop,hsharp⟩ := Processing.choose_k hn hnm _ hz H
    (C.period g) ((C.layer g top).first_le_last t) hstopn
  have hkm : k ≤ C.size g := hkn.trans hnm
  have hmul : k*C.period g ≤ n*C.period g := Nat.mul_le_mul_right _ hkn
  have hhard : t+(k*C.period g : ℕ) < (C.layer g top).first t := by
    dsimp only [t,top] at *
    dsimp only [n] at hmul
    omega
  obtain ⟨d,R,ha,hh,hd⟩ := supply g top t k hk hhard hstop
  have ht : t < R.stop := by omega
  let R' := R.normalize (C.periodic d.1)
  let r : RecordCode.Code := (R'.offset,R.start,R.stop)
  have htext := (hD top).text_eq
  have hp := (hD top).length_eq
  have hr : r ∈ RecordCode.pool (lookup B (encode d)).1.length M t := by
    rw [(hB d).length_eq]
    exact RecordCode.normalized_mem_pool (C.positive d.1) (C.periodic d.1) R ha ht len
  refine ⟨(k,encode d,r),params_mem (by omega) (hids d) hr,?_,?_⟩
  · have hc : RecordCode.check D.1 (lookup B (encode d)).1 (lookup B (encode d)).2 r = true :=
      RecordCode.check_record htext (hB d) R'
    have htop : GeoCode.first (exits D (D.2.length-1)) t = (C.layer g top).first t := by
      rw [hsize]
      exact congrFun (hD top).exit_eq (t-1)
    have hlo : GeoCode.exit (exits D (D.2.length-k)) t = (C.layer g ⟨C.size g-k,by omega⟩).last t := by
      rw [hsize]
      exact congrFun (hD ⟨C.size g-k,by omega⟩).exit_eq t
    have hall : ((upper D.2.length cut).filter (fun i => less i (D.2.length-k))).all
        (fun i => decide (GeoCode.first (exits D i) R.start ≤ R.stop)) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      have hi' : cut ≤ i ∧ i < C.size g ∧ i < C.size g-k := by
        simpa only [List.mem_filter,mem_upper,less,decide_eq_true_eq,hsize,and_assoc] using hi
      let j : Fin (C.size g) := ⟨i,hi'.2.1⟩
      have hj := Processing.below_stopped _ hz H (C.period g) k hstop j hi'.2.2
      have hfa := (C.layer g j).first_mono ha
      have hfl := (C.layer g j).first_le_last t
      have hg : GeoCode.first (exits D i) R.start = (C.layer g j).first R.start :=
        congrFun (hD j).exit_eq (R.start-1)
      apply decide_eq_true
      rw [hg]
      dsimp only [H] at hj
      omega
    simp only [test,less,lessEq,Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨hk,by omega⟩,hc⟩,ha⟩,ht⟩,?_⟩,?_⟩,?_⟩
    · change GeoCode.first _ t ≤ R.stop+(k*D.1.length : ℕ)
      rw [htop,hp]
      omega
    · change GeoCode.first _ t-GeoCode.exit _ t ≤ ((k-1)*D.1.length : ℕ)
      rw [htop,hlo,hp]
      dsimp only [H] at hsharp
      omega
    · exact hall
  · unfold foreign
    apply (PeriodWord.different_iff _ _ _ (by rw [hp]; exact C.positive g)
      (by rw [(hB d).length_eq]; exact C.positive d.1)).mpr
    rw [htext,(hB d).text_eq]
    change C.text g ≠ fun x => C.text d.1 (x+R'.offset)
    rw [R.normalize_text (C.periodic d.1)]
    exact hd
end Superstring.UpperCode

end OAI
