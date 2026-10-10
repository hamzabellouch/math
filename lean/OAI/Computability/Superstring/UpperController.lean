import OAI.Computability.Superstring.HostComplete

namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode UpperCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def complete (X : Env α) (g cut M : ℕ) (P : Walk α) : Plan α :=
  let D := data X g
  let m := D.2.length
  let p := D.1.length
  let t := phase X g
  let H := GeoCode.first (exits D (m-1)) t
  let I := upper m cut
  if m ≤ cut then (P,[],[])
  else if H-t ≤ ((m-cut)*p : ℕ) then
    (join P (rootUpper D I (m-1) t),[],[])
  else if 0 < cut ∧ H-GeoCode.exit (exits D (cut-1)) t ≤ ((m-cut)*p : ℕ) then
    (attachBand D I (cut-1) (m-1) P t,[],[])
  else
    let v := choose D (book X) (ids X) cut M t (foreign D (book X))
    let o := hardPlan X g cut v
    (join P o.1,o.2.1,o.2.2)
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem first_eq (g : G) {i : ℕ} (hi : i < C.size g) (t : ℤ) :
    GeoCode.first (exits (data X (h.group g)) i) t = (h.natLayer g i).first t := by
  simp only [GeoCode.first,(h.nat_rep g hi).exit_eq,Layer.first]
theorem last_eq (g : G) {i : ℕ} (hi : i < C.size g) (t : ℤ) :
    GeoCode.exit (exits (data X (h.group g)) i) t = (h.natLayer g i).last t :=
  congrFun (h.nat_rep g hi).exit_eq t

theorem complete_spec (closed : SubstringClosed V) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ V, w.length ≤ M) (g : G) (cut : ℕ) (hcut : cut ≤ C.size g)
    (P : Walk α) (hP : Runs V [] [] P)
    (hp : ∀ i : Fin (C.size g), i.val < cut → ∀ w ∈ (C.layer g i).Content, w ∈ P) :
    let o := complete X (h.group g) cut M P
    GoodPlan h o ∧ planBudget X o ≤ cost P+2*((C.size g-cut)*C.period g) ∧
      (∀ w ∈ P, w ∈ o.1) ∧
      (∀ i : Fin (C.size g), cut ≤ i.val → Covered X o (h.encode ⟨g,i⟩)) ∧
      (∀ r ∈ o.2.2, r.source = h.group g) ∧ o.2.2.length ≤ 1 := by
  let m := C.size g
  let p := C.period g
  let t := C.distinguished g
  let top : Fin (C.size g) := ⟨C.size g-1,by have := C.nonempty g; omega⟩
  have ht : (h.natLayer g (C.size g-1)) = C.layer g top := by
    exact h.natLayer_fin g top
  have htop : C.size g-1 < C.size g := top.isLt
  let I := upper (C.size g) cut
  have hib (i : ℕ) (hi : i ∈ I) : i < C.size g := ((mem_upper ..).mp hi).2
  have hirep := fun i hi => h.nat_rep g (hib i hi)
  have hie : I.length = C.size g-cut := length_upper ..
  have hu (i : ℕ) (hi : i ∈ I) (x : ℤ) : (h.natLayer g i).z x ≤ (h.natLayer g (C.size g-1)).z x :=
    h.nat_order g (by have := hib i hi; omega) x
  have hrefl (Q : Walk α) (hQ : Runs V [] [] Q) : GoodPlan h (Q,[],[]) := ⟨hQ,by simp,by simp⟩
  have heasy (Q : Walk α) (hQ : Runs V [] [] Q)
      (hc : cost Q ≤ cost P+2*((C.size g-cut)*C.period g))
      (hv : ∀ w ∈ P, w ∈ Q)
      (hi : ∀ i : Fin (C.size g), cut ≤ i.val → ∀ w ∈ (C.layer g i).Content, w ∈ Q) :
      GoodPlan h (Q,[],[]) ∧ planBudget X (Q,[],[]) ≤ cost P+2*((C.size g-cut)*C.period g) ∧
        (∀ w ∈ P, w ∈ Q) ∧
        (∀ i : Fin (C.size g), cut ≤ i.val → Covered X (Q,[],[]) (h.encode ⟨g,i⟩)) ∧
        (∀ r ∈ ([] : List Request), r.source = h.group g) ∧ ([] : List Request).length ≤ 1 := by
    refine ⟨hrefl Q hQ,by simpa only [planBudget,List.map_nil,List.sum_nil,Nat.add_zero] using hc,hv,?_,by simp,by simp⟩
    intro i hi' ; exact Or.inl (fun w hw => hi i hi' w ((h.content_iff ⟨g,i⟩ w).mp hw))
  unfold complete
  simp only [h.size,show (data X (h.group g)).1.length = C.period g from h.per_eq g,h.phase_eq]
  by_cases hem : C.size g ≤ cut
  · rw [ite_eq_left hem]
    apply heasy P hP (by omega) (fun _ hw => hw)
    intro i hi; have := i.isLt; omega
  · rw [ite_eq_right hem]
    have hct : cut < C.size g := by omega
    rw [h.first_eq g htop,ht]
    by_cases he : (C.layer g top).first (C.distinguished g)-C.distinguished g ≤ ((C.size g-cut)*C.period g : ℕ)
    · rw [ite_eq_left he]
      obtain ⟨hr,hc,hv⟩ := rootUpper_spec (h.natLayer g) hirep (h.nat_rep g htop) hu
        closed (C.positive g) (C.periodic g) (C.distinguished g) (by simpa only [hie,ht] using he)
      apply heasy _ (runs_join hP hr)
      · rw [cost_join _ _ [] hP.2.2 hr.2.1]
        rw [hie] at hc
        omega
      · exact fun w hw => (mem_join hP.2.2 hr.2.1).mpr (Or.inl hw)
      · intro i hi w hw
        apply (mem_join hP.2.2 hr.2.1).mpr
        exact Or.inr (hv i.val ((mem_upper ..).mpr ⟨hi,i.isLt⟩) w ((h.natLayer_fin g i).symm ▸ hw))
    · rw [ite_eq_right he]
      by_cases hb : 0 < cut ∧ (C.layer g top).first (C.distinguished g) -
          GeoCode.exit (exits (data X (h.group g)) (cut-1)) (C.distinguished g) ≤ ((C.size g-cut)*C.period g : ℕ)
      · rw [ite_eq_left hb]
        have hl : cut-1 < C.size g := by omega
        have hlo (i : ℕ) (hi : i ∈ I) (x : ℤ) :
            (h.natLayer g (cut-1)).z x ≤ (h.natLayer g i).z x :=
          h.nat_order g (by have := ((mem_upper ..).mp hi).1; omega) x
        have hband := hb.2
        rw [h.last_eq g hl] at hband
        obtain ⟨hr,hc,hv,hi⟩ := attachBand_spec (h.natLayer g) hirep (h.nat_rep g hl) (h.nat_rep g htop)
          hlo hu (h.nat_order g (by omega)) closed (C.positive g) (C.periodic g) (C.letters closed g)
          (C.distinguished g) (by simpa only [ht,hie] using hband) hP
          (by simpa only [h.natLayer_fin g (⟨cut-1,hl⟩ : Fin (C.size g))] using hp ⟨cut-1,hl⟩ (by change cut-1<cut; omega))
        apply heasy _ hr (by simpa only [hie] using hc) hv
        intro i hi' w hw
        exact hi i.val ((mem_upper ..).mpr ⟨hi',i.isLt⟩) w ((h.natLayer_fin g i).symm ▸ hw)
      · rw [ite_eq_right hb]
        have hb' : ¬ ∃ base : Fin (C.size g), base.val+1=cut ∧
            (C.layer g top).first (C.distinguished g)-(C.layer g base).last (C.distinguished g) ≤
              ((C.size g-cut)*C.period g : ℕ) := by
          rintro ⟨base,hbase,hbnd⟩
          apply hb
          have heq : cut-1=base.val := by omega
          refine ⟨by omega,?_⟩
          rw [heq,h.last_eq g base.isLt,h.natLayer_fin]
          exact hbnd
        have hex := supply_params C g supply (data X (h.group g)) (book X) (ids X) h.encode
          (h.size g) (h.rep g) (h.book_rep) (h.id_mem) M len cut hct he hb'
        rw [← h.phase_eq g] at hex
        let v := choose (data X (h.group g)) (book X) (ids X) cut M (phase X (h.group g))
          (foreign (data X (h.group g)) (book X))
        obtain ⟨hv,htest,hforeign⟩ := choose_spec _ _ _ _ _ _ _ hex
        have hvid : v.2.1 ∈ ids X := by
          obtain ⟨k,_,hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨r,_,heq⟩ := List.mem_map.mp hv
          have heq' : v.2.1 = j := (congrArg (fun x : UpperCode.Param => x.2.1) heq).symm
          exact heq'.symm ▸ hj
        obtain ⟨hg,hc,hv',hs,hn⟩ := h.hardPlan_spec closed g cut v hct hvid htest hforeign
        rw [← h.phase_eq g]
        change GoodPlan h (join P (hardPlan X (h.group g) cut v).1,_,_) ∧ _
        refine ⟨⟨runs_join hP hg.1,hg.2⟩,?_,?_,?_,hs,hn⟩
        · dsimp only [planBudget] at hc ⊢
          rw [cost_join _ _ [] hP.2.2 hg.1.2.1]
          dsimp only [v] at hc ⊢
          omega
        · exact fun w hw => (mem_join hP.2.2 hg.1.2.1).mpr (Or.inl hw)
        · intro i hi
          rcases hv' i hi with hvis|hblock|hreq
          · exact Or.inl (fun w hw => (mem_join hP.2.2 hg.1.2.1).mpr (Or.inr (hvis w hw)))
          · exact Or.inr (Or.inl hblock)
          · exact Or.inr (Or.inr hreq)
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
structure RequestAt {X : Env α} {C : LayerCollection V G} (h : Model X C) (d : C.Id) (r : Request) where
  source : G
  source_eq : h.group source = r.source
  record : (C.layerAt d).Record (C.text source)
  offset : record.offset = RecordCode.offset r.code
  start : record.start = RecordCode.start r.code
  stop : record.stop = RecordCode.stop r.code
  foreign : C.text source ≠ fun x => C.text d.1 (x+record.offset)
  nonempty : r.members ≠ []
  nodup : r.members.Nodup
  bound : ∀ i ∈ r.members, i < C.size source
  long : ∀ i ∈ r.members, record.start+C.period source < (h.natLayer source i).first record.start
  margin : ∀ i ∈ r.members, (h.natLayer source i).last record.start < record.stop-C.period source


namespace RequestAt
variable {X : Env α} {C : LayerCollection V G} {h : Model X C} {r : Request} {d : C.Id}
    (w : RequestAt h d r)
def hosted : HostedGroup (C.layerAt d) where
  text := fun x => C.text w.source (x-w.record.offset)
  period := C.period w.source
  positive := C.positive w.source
  periodic := fun x => by simpa only [add_sub_right_comm] using C.periodic w.source (x-w.record.offset)
  start := w.record.start+w.record.offset
  stop := w.record.stop+w.record.offset
  first_le := w.record.first_le
  le_last := w.record.le_last
  agree := by
    intro x hx hy
    have hh := w.record.agree (x-w.record.offset) (by omega) (by omega)
    simpa only [sub_add_cancel] using hh
  foreign := by
    intro he
    apply w.foreign
    funext x
    simpa only [add_sub_cancel_right] using congrFun he (x+w.record.offset)

def request (i : {j // j ∈ r.members}) : w.hosted.Request where
  layer := (h.natLayer w.source i.val).translate w.record.offset
  stop := (h.natLayer w.source i.val).first w.record.start+w.record.offset
  first_le := by simp [hosted]
  le_last := by
    simp only [hosted,Layer.translate_last,add_sub_cancel_right]
    have hh := (h.natLayer w.source i.val).first_le_last w.record.start
    omega
  long := by
    have hh := w.long i.val i.property
    change w.record.start+w.record.offset+C.period w.source < _
    omega
  margin := by
    have hh := w.margin i.val i.property
    have hf := (h.natLayer w.source i.val).first_le_last w.record.start
    change _ ≤ w.record.stop+w.record.offset-C.period w.source
    omega

theorem data_rep (i : {j // j ∈ r.members}) :
    Represents (UpperCode.lookup (book X) (r.source*stride X+i.val)).1
      (UpperCode.lookup (book X) (r.source*stride X+i.val)).2 (h.natLayer w.source i.val) := by
  rw [← w.source_eq,lookup_encode X _ _ (h.bound _) (lt_of_lt_of_le (w.bound i.val i.property) (h.capacity _))]
  exact h.nat_rep w.source (w.bound i.val i.property)

theorem entry_eq (i : {j // j ∈ r.members}) : Request.entry X r i.val =
    (r.source,PeriodWord.shift (data X r.source).1 w.record.offset,
      w.hosted.start,w.hosted.stop,(w.request i).stop) := by
  simp only [Request.entry,← w.source_eq,← w.offset,← w.start,← w.stop,hosted,request]
  simp only [GeoCode.first,(h.nat_rep w.source (w.bound i.val i.property)).exit_eq,Layer.first]
end RequestAt
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem requestAt {r : Request} (hr : ValidRequest h r) (d : C.Id) (hd : h.encode d = r.target) :
    Nonempty (RequestAt h d r) := by
  obtain ⟨w⟩ := hr
  have he : w.target = d := h.encode_inj (w.target_eq.trans hd.symm)
  cases he
  exact ⟨⟨w.source,w.source_eq,w.record,w.offset,w.start,w.stop,w.foreign,w.nonempty,w.nodup,
    w.bound,w.long,w.margin⟩⟩
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def entries (X : Env α) (R : List Request) : List (HostCode.Entry α) :=
  R.flatMap (fun r => r.members.map (Request.entry X r))
def requestedData (X : Env α) (R : List Request) : List (LayerData α) :=
  R.flatMap (fun r => (r.ids X).map (UpperCode.lookup (book X)))
def fibrePool (X : Env α) (t : ℕ) (R : List Request) : List (Walk α) :=
  let D := UpperCode.lookup (book X) t
  HostCode.completePool D.1 D.2 (entries X R) (requestedData X R)

def SourcesDistinct (R : List Request) : Prop :=
  ∀ r ∈ R, ∀ s ∈ R, r.source = s.source → r = s
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem fibrePool_complete (closed : SubstringClosed V) (d : C.Id) (R : List Request)
    (hne : R ≠ []) (valid : ∀ r ∈ R, ValidRequest h r)
    (target : ∀ r ∈ R, r.target = h.encode d) (distinct : SourcesDistinct R) :
    ∃ P ∈ fibrePool X (h.encode d) R,
      Runs V [] [] P ∧ cost P ≤ 2*C.period d.1+(R.map (Request.reserve X)).sum ∧
        (∀ w ∈ ls X (h.encode d), w ∈ P) ∧
        ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
  classical
  let J := {r // r ∈ R}
  let W : ∀ j : J, RequestAt h d j.val := fun j => (h.requestAt (valid j.val j.property) d (target j.val j.property).symm).some
  let K := Σ j : J, {i // i ∈ j.val.members}
  let I : List K := R.attach.flatMap (fun j => j.val.members.attach.map (fun i => ⟨j,i⟩))
  let H := fun j : J => (W j).hosted
  let req := fun i : K => (W i.1).request i.2
  let Ws := fun j : J => PeriodWord.shift (data X j.val.source).1 (W j).record.offset
  let D' := fun i : K => UpperCode.lookup (book X) (i.1.val.source*stride X+i.2.val)
  have htag : Function.Injective (fun j : J => j.val.source) := by
    intro j k he
    exact Subtype.ext (distinct j.val j.property k.val k.property he)
  have hdiff (j k : J) (hjk : j ≠ k) (c : ℤ) : (H j).text ≠ fun x => (H k).text (x+c) := by
    intro he
    have hn : (W j).source ≠ (W k).source := by
      intro hs
      apply hjk
      apply htag
      exact (W j).source_eq.symm.trans ((congrArg h.group hs).trans (W k).source_eq)
    apply C.different _ _ hn ((W j).record.offset+c-(W k).record.offset)
    funext x
    have hh := congrFun he (x+(W j).record.offset)
    change C.text (W j).source (x+(W j).record.offset-(W j).record.offset) =
      C.text (W k).source (x+(W j).record.offset+c-(W k).record.offset) at hh
    simpa only [add_sub_cancel_right,show x+(W j).record.offset+c-(W k).record.offset =
      x+((W j).record.offset+c-(W k).record.offset) by omega] using hh
  have hWs (j : J) : (Ws j).length = (H j).period := by
    simp only [Ws,PeriodWord.length_shift,← (W j).source_eq]
    exact h.per_eq (W j).source
  have hWst (j : J) : PeriodWord.text (Ws j) = (H j).text := by
    dsimp only [Ws]
    rw [PeriodWord.text_shift (by rw [← (W j).source_eq]; change 0 < per X (h.group (W j).source); rw [h.per_eq]; exact C.positive (W j).source)]
    simp only [← (W j).source_eq,h.text_eq,H,RequestAt.hosted]
  have hiMem (j : J) (i : {i // i ∈ j.val.members}) : (⟨j,i⟩ : K) ∈ I :=
    List.mem_flatMap.mpr ⟨j,List.mem_attach R j,List.mem_map.mpr ⟨i,List.mem_attach _ i,rfl⟩⟩
  have hine : I ≠ [] := by
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil R hne
    let j : J := ⟨r,hr⟩
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil r.members (W j).nonempty
    exact List.ne_nil_of_mem (hiMem j ⟨i,hi⟩)
  obtain ⟨P,hP,hr,hb,hd,hi⟩ := HostCode.completePool_complete closed (C.layerAt d)
    (C.positive d.1) (C.periodic d.1) (C.letters closed d.1) H Sigma.fst req Ws (fun j => j.val.source)
    htag (UpperCode.lookup (book X) (h.encode d)).1 (UpperCode.lookup (book X) (h.encode d)).2
    (h.book_rep d) hWs hWst
    (fun j x => C.letters closed (W j).source (x-(W j).record.offset)) hdiff
    (fun i : K => C.text (W i.1).source) (fun i : K => h.natLayer (W i.1).source i.2.val)
    D' I hine (fun i _ => (W i.1).data_rep i.2) (fun i _ => C.periodic (W i.1).source)
    (fun i _ => (Layer.translate_content _ _).symm)
  have hent : I.map (HostCode.entryOf H Sigma.fst req Ws (fun j => j.val.source)) = entries X R := by
    simp only [I,entries,List.map_flatMap,List.map_map]
    rw [List.flatMap_subtype (g := fun r : Request => r.members.map (Request.entry X r))]
    · simp
    · intro r hr
      rw [List.map_subtype (g := Request.entry X r)]
      · simp
      · intro i hi
        exact ((W ⟨r,hr⟩).entry_eq ⟨i,hi⟩).symm
  have hdata : I.map D' = requestedData X R := by
    simp only [I,requestedData,List.map_flatMap,List.map_map,Request.ids,D',Function.comp_def]
    rw [List.flatMap_subtype (g := fun r : Request => r.members.map
      (fun i => UpperCode.lookup (book X) (r.source*stride X+i)))]
    · simp
    · intro r hr
      simp
  have sum_flatMap_nat {β : Type} (L : List β) (f : β → List ℕ) :
      (L.flatMap f).sum = (L.map (fun x => (f x).sum)).sum := by
    induction L with
    | nil => simp
    | cons a l ih => simp [ih]
  have hsum : (I.map (fun i => (H i.1).period)).sum = (R.map (fun r => r.members.length*per X r.source)).sum := by
    simp only [I,List.map_flatMap,List.map_map,sum_flatMap_nat]
    congr 1
    rw [List.map_subtype (g := fun r : Request => r.members.length*per X r.source)]
    · simp
    · intro r hr
      change (r.members.attach.map (fun _ => C.period (W ⟨r,hr⟩).source)).sum = _
      simp only [List.map_const',List.sum_replicate,List.length_attach,nsmul_eq_mul,Nat.cast_id,
        ← (W ⟨r,hr⟩).source_eq,h.per_eq]
  refine ⟨P,?_,hr,?_,fun w hw => hd w ((h.content_iff d w).mp hw),?_⟩
  · simpa only [fibrePool,hent,hdata] using hP
  · rw [hsum] at hb
    have he : (R.map (Request.reserve X)).sum = 2*(R.map (fun r => r.members.length*per X r.source)).sum := by
      exact List.sum_map_mul_left R (fun r => r.members.length*per X r.source) 2
    rw [he]
    nlinarith
  · intro r hr' i hi' w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi'
    let a : J := ⟨r,hr'⟩
    let b : {j // j ∈ a.val.members} := ⟨j,hj⟩
    apply hi ⟨a,b⟩ (hiMem a b) w
    have hbnd := (W a).bound b.val b.property
    change w ∈ ls X (r.source*stride X+j) at hw
    have he : h.group (W a).source = r.source := (W a).source_eq
    rw [← he,ls_encode X _ _ (h.bound _) (lt_of_lt_of_le hbnd (h.capacity _))] at hw
    exact (mem_content (h.nat_rep (W a).source hbnd) (C.positive (W a).source)
      (C.periodic (W a).source) w).mp hw
end Model
end Superstring.CollectionCode

end OAI
