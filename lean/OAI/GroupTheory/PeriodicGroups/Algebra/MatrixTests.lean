import Mathlib
import OAI.GroupTheory.PeriodicGroups.Algebra.DirectCancellation
import OAI.GroupTheory.PeriodicGroups.Algebra.HierarchyGrowth

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α β K : Type*} [CommRing K]
def wordHom (T : Table α) : FreeMonoid α →* T.Algebra (K:=K) where
  toFun := T.word
  map_one' := T.word_one
  map_mul' := T.word_mul

def substitution (U : Table α) (T : Table β) (f : FreeMonoid α →* FreeMonoid β)
    (hr : ∀a b,U.rep a b → T.word (K:=K) (f a)=T.word (f b))
    (hz : ∀a∈U.zero,T.word (K:=K) (f a)=0) : U.Algebra (K:=K) →ₐ[K] T.Algebra (K:=K) := by
  let F := MonoidAlgebra.lift K (T.Algebra (K:=K)) (FreeMonoid α) ((wordHom T).comp f)
  have H : U.ideal (K:=K) ≤ TwoSidedIdeal.ker F := by
    apply TwoSidedIdeal.span_le.mpr
    rintro v (⟨a,b,hab,rfl⟩|⟨a,ha,rfl⟩)
    · change F (monomial a-monomial b)=0
      simp only [map_sub,F,monomial,MonoidAlgebra.lift_single,one_smul,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk]
      exact sub_eq_zero.mpr (hr a b hab)
    · change F (monomial a)=0
      simpa only [F,monomial,MonoidAlgebra.lift_single,one_smul,
        MonoidHom.comp_apply,wordHom,MonoidHom.coe_mk,OneHom.coe_mk] using hz a ha
  apply RingCon.liftₐ _ F
  intro a b hab
  change F a=F b
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact H ((U.ideal (K:=K)).rel_iff a b |>.mp hab)
@[simp] lemma substitution_word (U : Table α) (T : Table β) (f : FreeMonoid α →* FreeMonoid β)
    (hr : ∀a b,U.rep a b → T.word (K:=K) (f a)=T.word (f b))
    (hz : ∀a∈U.zero,T.word (K:=K) (f a)=0) (w : FreeMonoid α) :
    substitution U T f hr hz (U.word w)=T.word (f w) := by
  change (MonoidAlgebra.lift K (T.Algebra (K:=K)) (FreeMonoid α) ((wordHom T).comp f)) (monomial w)=_
  simp [monomial,MonoidAlgebra.lift_single,wordHom]
end
end SourceBurnside.WordAlgebra.Table
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
lemma simulate_replacement {h : ℕ} (hh : A.threshold ≤ h) {v w : List (Codec.Raw (D*h))}
    (he : Codec.replacement (A.height_pos (A.next_large hh))
      (A.schedule (D*h) (A.next_large hh)) (10000*(D*(D*h))) v w) :
    Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) (embedding h D v) (embedding h D w) := by
  obtain ⟨hlen,hn,hk⟩ := Codec.replacement_lengths (A.threshold_four.trans (A.next_large hh)) _ _ v w he
  let task : Task := ⟨⟨v.length-1,by omega⟩,false⟩
  have htask : task.arity.val+1=v.length := by dsimp [task];omega
  let u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h) := fun s i =>
    if s then w[i.val]'(by have := i.isLt;omega) else v[i.val]'(by have := i.isLt;omega)
  have hv : List.ofFn (u false)=v := by
    apply List.ext_getElem (by simpa [List.length_ofFn] using htask)
    intro i hi hj
    simp only [List.getElem_ofFn,u,Bool.false_eq_true,ite_false]
  have hw : List.ofFn (u true)=w := by
    apply List.ext_getElem (by simpa [List.length_ofFn] using htask.trans hlen)
    intro i hi hj
    simp only [List.getElem_ofFn,u,ite_true]
  have HH := A.simulate hh task u (by
    change Codec.entry _ _ _ false (List.ofFn (u false)) (List.ofFn (u true))=true
    rw [hv,hw]
    exact (Codec.entry_replacement _ _ _ _ _).mpr he)
  simpa only [hv,hw] using HH.1 rfl
lemma simulate_zero {h : ℕ} (hh : A.threshold ≤ h) {v : List (Codec.Raw (D*h))}
    (he : Codec.zero (A.height_pos (A.next_large hh))
      (A.schedule (D*h) (A.next_large hh)) (10000*(D*(D*h))) v) :
    ∃p z s, Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) (embedding h D v) (p++z++s) ∧
      Codec.zero (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) z := by
  obtain ⟨hn,hk⟩ := Codec.zero_lengths _ _ _ v he
  let task : Task := ⟨⟨v.length-1,by omega⟩,true⟩
  have htask : task.arity.val+1=v.length := by dsimp [task];omega
  let u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h) := fun _ i => v[i.val]'(by have := i.isLt;omega)
  have hv : List.ofFn (u false)=v := by
    apply List.ext_getElem (by simpa [List.length_ofFn] using htask)
    intro i hi hj
    simp only [List.getElem_ofFn,u]
  have HH := A.simulate hh task u (by
    change Codec.entry _ _ _ true (List.ofFn (u false)) []=true
    rw [hv]
    exact (Codec.entry_zero _ _ _ _ _).mpr ⟨rfl,he⟩)
  simpa only [hv] using HH.2 rfl

def substitutionWords (h : ℕ) : FreeMonoid (Codec.Raw (D*h)) →* FreeMonoid (Codec.Raw h) where
  toFun := fun w => FreeMonoid.ofList (embedding h D w.toList)
  map_one' := by simp [embedding,encodeWord]
  map_mul' := by intro v w;simp [embedding,encodeWord,List.flatMap_append]

def embeddingHom (K : Type*) [CommRing K] {h : ℕ} (hh : A.threshold ≤ h) :
    A.Algebra K (D*h) (A.next_large hh) →ₐ[K] A.Algebra K h hh :=
  WordAlgebra.Table.substitution _ _ (substitutionWords (D:=D) h)
    (by
      intro a b hab
      apply (A.table h hh).word_reach
      exact Codec.reach_iff_table.mp (A.simulate_replacement hh hab))
    (by
      intro a ha
      obtain ⟨p,z,s,hr,hz⟩ := A.simulate_zero hh ha
      apply (A.table h hh).word_eq_zero_of_vanishes
      exact ⟨FreeMonoid.ofList p,FreeMonoid.ofList z,FreeMonoid.ofList s,hz,Codec.reach_iff_table.mp hr⟩)
lemma embeddingHom_word (K : Type*) [CommRing K] {h : ℕ} (hh : A.threshold ≤ h) (w : List (Codec.Raw (D*h))) :
    A.embeddingHom K hh ((A.table (D*h) (A.next_large hh)).word (FreeMonoid.ofList w))=
      (A.table h hh).word (FreeMonoid.ofList (embedding h D w)) := by
  exact WordAlgebra.Table.substitution_word (K:=K) _ _ _ _ _ _
end
end SourceBurnside.SourceMachine.MachineHierarchy
namespace SourceBurnside.DirectCancellation
noncomputable section
open Classical
variable {T : Type*}

lemma maximal_of_uniform (eligible : T → Prop) (q : ℕ) {w v : List T}
    (hv : v <:+: w) (hn : 0<v.length) (hq : q ≤ 100*v.length)
    (t : T) (ht : eligible t) (hall : ∀x∈v,x=t) :
    ∃a e,EligibleInterval eligible q w a e := by
  let P : ℕ → Prop := fun n => ∃p s,w=p++List.replicate n t++s
  have hP : P v.length := by
    obtain ⟨p,s,he⟩ := hv
    exact ⟨p,s,by simpa only [←List.eq_replicate_of_mem hall] using he.symm⟩
  let n := Nat.findGreatest P w.length
  have hle : v.length ≤ n := Nat.le_findGreatest hv.length_le hP
  obtain ⟨p,s,he⟩ := Nat.findGreatest_spec hv.length_le hP
  change w=p++List.replicate n t++s at he
  have hlen : w.length=p.length+n+s.length := by simp [he,Nat.add_assoc]
  have hp : p.getLast?≠some t := by
    intro hp
    obtain ⟨a,ha⟩ := List.getLast?_eq_some_iff.mp hp
    have hP' : P (n+1) := by
      refine ⟨a,s,?_⟩
      simp only [he,ha,List.replicate_succ,List.append_assoc,List.singleton_append]
    exact Nat.findGreatest_is_greatest (show n<n+1 from Nat.lt_succ_self _) (by simp [ha] at hlen;omega) hP'
  have hs : s.head?≠some t := by
    intro hs
    obtain ⟨b,hb⟩ := List.head?_eq_some_iff.mp hs
    have hP' : P (n+1) := by
      refine ⟨p,b,?_⟩
      simp only [he,hb,List.replicate_succ',List.append_assoc,List.singleton_append]
    exact Nat.findGreatest_is_greatest (show n<n+1 from Nat.lt_succ_self _) (by simp [hb] at hlen;omega) hP'
  refine ⟨p.length,p.length+n,?_,by omega,by omega,t,ht,?_,?_,?_⟩
  · omega
  · simp [he,List.append_assoc]
  · simpa only [he,←List.append_assoc,List.take_append_of_le_length (by simp : p.length ≤ (p++List.replicate n t).length),List.take_left] using hp
  · have hh : w.drop (p.length+n)=s := by
      have hpl : (p++List.replicate n t).length=p.length+n := by simp
      rw [←hpl,he,List.drop_left]
    rwa [hh]
end
end SourceBurnside.DirectCancellation
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
variable {K : Type*} [Ring K]
def letter (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (a : Raw h) :
    (algebraTable hh S d).Algebra (K:=K) := (algebraTable hh S d).word (FreeMonoid.ofList [a])
lemma eval_letter (w : List (Raw h)) :
    DirectCancellation.eval (letter (K:=K) hh S d) w =
      (algebraTable hh S d).word (FreeMonoid.ofList w) := by
  induction w with
  | nil => exact (algebraTable hh S d).word_one.symm
  | cons a w ih =>
    change letter hh S d a * DirectCancellation.eval (letter hh S d) w = _
    rw [ih]
    exact ((algebraTable hh S d).word_mul (FreeMonoid.ofList [a]) (FreeMonoid.ofList w)).symm
lemma surviving_of_eval_ne_zero (w : List (Raw h))
    (hw : DirectCancellation.eval (letter (K:=K) hh S d) w ≠ 0) : Survives hh S d w := by
  apply (survives_iff_not_vanishes w).mpr
  intro hz
  exact hw ((eval_letter w).trans ((algebraTable hh S d).word_eq_zero_of_vanishes hz))
lemma noncolor_isPalette (c : Cell (2^h)) : (noncolor c).isPalette ↔ c.isPalette := by
  unfold noncolor
  split_ifs with hc
  · exact iff_of_true (erased_palette c hc) hc
  · rfl
lemma noncolor_headFree (c : Cell (2^h)) : (noncolor c).HeadFree ↔ c.HeadFree := by
  unfold noncolor
  split_ifs <;> rfl
lemma eligible_decode {a : Raw h} (ha : eligibleFields (fields hh a)) :
    ∃c, decode hh a=some c ∧ c.isPalette ∧ c.HeadFree := by
  obtain ⟨c,he,hp,hf⟩ := ha
  cases hd : decode hh a with
  | none => simp [fields,hd] at he
  | some b =>
    have he' : noncolor b=c := by simpa [fields,hd] using he
    exact ⟨b,rfl, (noncolor_isPalette b).mp (he' ▸ hp), (noncolor_headFree b).mp (he' ▸ hf)⟩
lemma letter_commute (h4 : 4 ≤ h) (t : Option (Cell (2^h))) (ht : eligibleFields t)
    (x y : Raw h) (hx : fields hh x=t) (hy : fields hh y=t) :
    Commute (letter (K:=K) hh S d x) (letter hh S d y) := by
  by_cases hx0 : letter (K:=K) hh S d x=0
  · simp [hx0]
  by_cases hy0 : letter (K:=K) hh S d y=0
  · simp [hy0]
  obtain ⟨a,ha,hap,haf⟩ := eligible_decode (hx ▸ ht)
  obtain ⟨b,hb,hbp,hbf⟩ := eligible_decode (hy ▸ ht)
  obtain rfl := (decode_eq_some_iff h4 x a).mp ha
  obtain rfl := (decode_eq_some_iff h4 y b).mp hb
  have hfa : a.Format S d := by
    by_contra! he
    apply hx0
    apply (algebraTable hh S d).word_zero
    exact (zero_encode h4 S d _).mpr (Or.inl ⟨a,rfl,Or.inl he⟩)
  have hfb : b.Format S d := by
    by_contra! he
    apply hy0
    apply (algebraTable hh S d).word_zero
    exact (zero_encode h4 S d _).mpr (Or.inl ⟨b,rfl,Or.inl he⟩)
  have he : a.eraseColor=b.eraseColor := by
    have he' := hx.trans hy.symm
    simpa [fields_encode h4,noncolor,hap,hbp] using he'
  have hr : replacement hh S d [encode a,encode b] [encode b,encode a] := by
    exact (replacement_encode h4 S d _ _).mpr (replacement_swap_of_same_fields hap hbp hfa hfb he haf hbf)
  have he := (algebraTable hh S d).word_rep (K:=K) hr
  change letter hh S d (encode a)*letter hh S d (encode b)=_
  simpa only [letter,←WordAlgebra.Table.word_mul] using (show (algebraTable hh S d).word (K:=K) (FreeMonoid.ofList [encode a] * FreeMonoid.ofList [encode b]) = (algebraTable hh S d).word (FreeMonoid.ofList [encode b] * FreeMonoid.ofList [encode a]) from he)
lemma letter_square (h4 : 4 ≤ h) (x : Raw h) (hx : eligibleFields (fields hh x)) :
    letter (K:=K) hh S d x * letter hh S d x = 0 := by
  obtain ⟨a,ha,hap,haf⟩ := eligible_decode hx
  obtain rfl := (decode_eq_some_iff h4 x a).mp ha
  obtain ⟨c,hc⟩ := hap
  have hz : zero hh S d [encode a,encode a] :=
    (zero_encode h4 S d _).mpr (Or.inr ⟨a,a,rfl,Or.inr (Or.inl ⟨c,hc,hc⟩)⟩)
  rw [letter,←WordAlgebra.Table.word_mul]
  exact (algebraTable hh S d).word_zero (K:=K) hz
lemma long_eligible_interval (h4 : 4 ≤ h) (w : List (Raw h))
    (hn : 2*fragmentBound (2^h)+1 ≤ w.length)
    (hw : DirectCancellation.eval (letter (K:=K) hh S d) w ≠ 0) :
    ∃a e,DirectCancellation.EligibleInterval eligibleFields (2^h) (w.map (fields hh)) a e := by
  obtain ⟨v,hv,hnv,hq,t,ht,he⟩ := (surviving_of_eval_ne_zero w hw).long_uniform h4 (by omega)
  apply DirectCancellation.maximal_of_uniform eligibleFields (2^h) (hv.map (fields hh)) (by simpa using (by omega : 0<v.length)) (by simpa using hq) t ht
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  exact he a ha
end
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.CutReduction
open scoped BigOperators
open Classical
noncomputable section
variable {α Γ R : Type*} [Fintype α] [Fintype Γ] [Semiring R]

def candidates (α : Type*) [Fintype α] (n : ℕ) : Finset (List α) :=
  Finset.univ.image (fun s : Σ r : Fin (n+1), Fin r.val → α => List.ofFn s.2)

lemma mem_candidates (n : ℕ) (s : List Γ) : s ∈ candidates Γ n ↔ s.length ≤ n := by
  simp only [candidates,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨r,f⟩,rfl⟩; simp only [List.length_ofFn]; omega
  · intro hs; exact ⟨⟨⟨s.length,by omega⟩,s.get⟩,List.ofFn_get s⟩

def eval (f : α → R) (w : List α) : R := (w.map f).prod
omit [Fintype α] [Fintype Γ] in
@[simp] lemma eval_append (f : α → R) (u v : List α) :
    eval f (u++v) = eval f u * eval f v := by simp [eval]

omit [Semiring R] [Fintype α] [Fintype Γ] in
lemma length_flatMap (token : Γ → List α) (len : Γ → ℕ) (L : ℕ)
    (hl : ∀ c, (token c).length=L*len c) (gs : List Γ) :
    (gs.flatMap token).length = L * (gs.map len).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.flatMap_cons,List.length_append,hl,ih,
      List.map_cons,List.sum_cons,Nat.mul_add]

omit [Semiring R] [Fintype α] [Fintype Γ] in
lemma length_le_sum (len : Γ → ℕ) (hl : ∀ c, 1 ≤ len c) (gs : List Γ) :
    gs.length ≤ (gs.map len).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; have := hl g; omega

omit [Fintype α] [Fintype Γ] in
lemma eval_flatMap (f : α → R) (token : Γ → List α) (gs : List Γ) :
    eval f (gs.flatMap token) = eval (fun c => eval f (token c)) gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons,eval_append,ih]
    rfl

def chunkSum (len : Γ → ℕ) (weight : Γ → R) (m : ℕ) : R :=
  ∑ gs ∈ (candidates Γ m).filter (fun gs => (gs.map len).sum=m), eval weight gs

def letterSum (f : α → R) (n : ℕ) : R :=
  ∑ w ∈ (candidates α n).filter (fun w => w.length=n), eval f w

def join (token : Γ → List α) (x : List α × List α × List Γ) : List α :=
  x.1 ++ x.2.2.flatMap token ++ x.2.1

def language (token : Γ → List α) (ps ss : Finset (List α)) (n : ℕ) :
    Finset (List α × List α × List Γ) :=
  (ps.product (ss.product (candidates Γ n))).filter (fun x => (join token x).length=n)

omit [Fintype α] in
lemma mem_language (token : Γ → List α) (ps ss : Finset (List α)) (n : ℕ)
    (p s : List α) (gs : List Γ) :
    (p,s,gs) ∈ language token ps ss n ↔
      p∈ps ∧ s∈ss ∧ gs.length≤n ∧ (p++gs.flatMap token++s).length=n := by
  rw [language,Finset.mem_filter]
  simp only [Finset.product_eq_sprod,Finset.mem_product,mem_candidates,join]
  tauto

omit [Fintype α] in
lemma join_injective (cut : α → Prop) (token : Γ → List α)
    (hinj : Function.Injective token) (ht : ∀ c, Cuts.Interval cut (token c))
    (ps ss : Finset (List α)) (hp : ∀ p∈ps, Cuts.NoCut cut p)
    (hs : ∀ s∈ss, Cuts.Interval cut s) (n : ℕ) :
    Set.InjOn (join token) (language token ps ss n : Set _) := by
  rintro ⟨p,s,gs⟩ hx ⟨p',s',gs'⟩ hy he
  obtain ⟨hp0,hs0,_,_⟩ := (mem_language token ps ss n p s gs).mp hx
  obtain ⟨hp1,hs1,_,_⟩ := (mem_language token ps ss n p' s' gs').mp hy
  have ht0 : ∀ t ∈ gs.map token, Cuts.Interval cut t := by
    intro t hm; obtain ⟨g,_,rfl⟩ := List.mem_map.mp hm; exact ht g
  have ht1 : ∀ t ∈ gs'.map token, Cuts.Interval cut t := by
    intro t hm; obtain ⟨g,_,rfl⟩ := List.mem_map.mp hm; exact ht g
  have hh := Cuts.language_injective cut (hp p hp0) (hs s hs0) ht0
    (hp p' hp1) (hs s' hs1) ht1 (by simpa only [←List.flatMap_def,join] using he)
  obtain ⟨rfl,hg,rfl⟩ := hh
  have hgs : gs=gs' := (List.map_injective_iff.mpr hinj) hg
  simp only [hgs]

theorem letterSum_eq_language (cut : α → Prop) (token : Γ → List α)
    (hinj : Function.Injective token) (ht : ∀ c, Cuts.Interval cut (token c))
    (ps ss : Finset (List α)) (hp : ∀ p∈ps, Cuts.NoCut cut p)
    (hs : ∀ s∈ss, Cuts.Interval cut s) (f : α → R) (n : ℕ)
    (hcover : ∀ w, w.length=n → eval f w ≠ 0 →
      ∃ p∈ps, ∃ s∈ss, ∃ gs : List Γ, w=p++gs.flatMap token++s) :
    letterSum f n = ∑ x ∈ language token ps ss n, eval f (join token x) := by
  let W := (candidates α n).filter (fun w => w.length=n)
  let T := language token ps ss n
  have hsub : T.image (join token) ⊆ W := by
    intro w hw
    obtain ⟨⟨p,s,gs⟩,hm,rfl⟩ := Finset.mem_image.mp hw
    have hn := ((mem_language token ps ss n p s gs).mp hm).2.2.2
    exact Finset.mem_filter.mpr ⟨(mem_candidates n _).mpr (by simpa [join] using hn.le),hn⟩
  have heq : ∑ w ∈ T.image (join token), eval f w = ∑ w ∈ W, eval f w := by
    apply Finset.sum_subset hsub
    intro w hw hn
    by_contra hz
    obtain ⟨p,hp0,s,hs0,gs,hgs⟩ := hcover w (Finset.mem_filter.mp hw).2 hz
    apply hn
    apply Finset.mem_image.mpr
    refine ⟨(p,s,gs),?_,hgs.symm⟩
    apply (mem_language token ps ss n p s gs).mpr
    refine ⟨hp0,hs0,?_,by simpa only [←hgs] using (Finset.mem_filter.mp hw).2⟩
    have hpos : ∀ c, 1 ≤ (token c).length := by
      intro c; obtain ⟨a,t,he,_,_⟩ := ht c; simp [he]
    have hl := length_le_sum (fun c => (token c).length) hpos gs
    have hlen := length_flatMap token (fun c => (token c).length) 1 (by simp) gs
    rw [one_mul] at hlen
    have htot : w.length = p.length + (gs.flatMap token).length + s.length := by simp [hgs,Nat.add_assoc]
    have hw' := (Finset.mem_filter.mp hw).2
    omega
  rw [Finset.sum_image (join_injective cut token hinj ht ps ss hp hs n)] at heq
  exact heq.symm

omit [Fintype α] in

lemma slice_eq_chunk (f : α → R) (token : Γ → List α) (len : Γ → ℕ)
    (hl : ∀ c, 1 ≤ len c) (L : ℕ) (hL : 1 ≤ L)
    (hlen : ∀ c, (token c).length=L*len c) (p s : List α) (n : ℕ) :
    (∑ gs ∈ (candidates Γ n).filter
      (fun gs => (p++gs.flatMap token++s).length=n),
        eval (fun c => eval f (token c)) gs) = 0 ∨
      ∃ m, p.length+L*m+s.length=n ∧
        (∑ gs ∈ (candidates Γ n).filter
          (fun gs => (p++gs.flatMap token++s).length=n),
            eval (fun c => eval f (token c)) gs) = chunkSum len (fun c => eval f (token c)) m := by
  let T := (candidates Γ n).filter (fun gs => (p++gs.flatMap token++s).length=n)
  by_cases he : T.Nonempty
  · obtain ⟨gs,hgs⟩ := he
    let m := (gs.map len).sum
    have hn : p.length+L*m+s.length=n := by
      simpa only [List.length_append,length_flatMap token len L hlen] using
        (Finset.mem_filter.mp hgs).2
    have hmn : m ≤ n := by nlinarith
    have ht : T=(candidates Γ m).filter (fun gs => (gs.map len).sum=m) := by
      ext ts
      simp only [T,Finset.mem_filter,mem_candidates,List.length_append,
        length_flatMap token len L hlen]
      constructor
      · rintro ⟨_,he⟩
        have hm : (ts.map len).sum=m := by nlinarith
        exact ⟨by rw [←hm]; exact length_le_sum len hl ts,hm⟩
      · rintro ⟨ht,hm⟩
        exact ⟨by omega,by simpa only [hm] using hn⟩
    right
    exact ⟨m,hn,by change (∑ gs ∈ T, _) = _; rw [ht]; rfl⟩
  · left
    have ht : T=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change (∑ gs ∈ T, _) = 0
    rw [ht]; simp

theorem eventually_letterSum_zero (cut : α → Prop) (token : Γ → List α)
    (hinj : Function.Injective token) (ht : ∀ c, Cuts.Interval cut (token c))
    (ps ss : Finset (List α)) (hp : ∀ p∈ps, Cuts.NoCut cut p)
    (hs : ∀ s∈ss, Cuts.Interval cut s) (B : ℕ)
    (hpB : ∀ p∈ps, p.length ≤ B) (hsB : ∀ s∈ss, s.length ≤ B)
    (len : Γ → ℕ) (hl : ∀ c, 1 ≤ len c) (L : ℕ) (hL : 1 ≤ L)
    (hlen : ∀ c, (token c).length=L*len c) (f : α → R) (N₀ N₁ : ℕ)
    (hcover : ∀ w, N₀ ≤ w.length → eval f w ≠ 0 →
      ∃ p∈ps, ∃ s∈ss, ∃ gs : List Γ, w=p++gs.flatMap token++s)
    (hchunk : ∀ m, N₁ ≤ m → chunkSum len (fun c => eval f (token c)) m=0)
    (n : ℕ) (hn : max N₀ (2*B+L*N₁) ≤ n) : letterSum f n=0 := by
  rw [letterSum_eq_language cut token hinj ht ps ss hp hs f n
    (fun w hw h => hcover w (by omega) h)]
  rw [language,Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_eq_zero
  intro p hp0
  apply Finset.sum_eq_zero
  intro s hs0
  change (∑ gs ∈ candidates Γ n,
    if (p++gs.flatMap token++s).length=n then eval f (p++gs.flatMap token++s) else 0)=0
  have hslice : (∑ gs ∈ (candidates Γ n).filter
      (fun gs => (p++gs.flatMap token++s).length=n),
        eval (fun c => eval f (token c)) gs) = 0 := by
    rcases slice_eq_chunk f token len hl L hL hlen p s n with h | ⟨m,hm,he⟩
    · exact h
    · rw [he,hchunk m]
      have hp' := hpB p hp0
      have hs' := hsB s hs0
      have hn' : 2*B+L*N₁ ≤ n := by omega
      nlinarith
  have he : (∑ gs ∈ candidates Γ n,
      if (p++gs.flatMap token++s).length=n then eval f (p++gs.flatMap token++s) else 0) =
      eval f p * (∑ gs ∈ (candidates Γ n).filter
        (fun gs => (p++gs.flatMap token++s).length=n),
          eval (fun c => eval f (token c)) gs) * eval f s := by
    rw [Finset.sum_filter,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro gs _
    split_ifs <;> simp [eval_append,eval_flatMap,mul_assoc]
  rw [he,hslice,mul_zero,zero_mul]

end
end SourceBurnside.CutReduction
namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def tensor (X : Matrix ι ι K) (a : A) : Matrix ι ι A := fun i j => X i j • a
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma tensor_zero (X : Matrix ι ι K) : tensor X (0:A)=0 := by ext;simp [tensor]
omit [Fintype ι] in
@[simp] lemma tensor_one : tensor (1:Matrix ι ι K) (1:A)=1 := by
  ext i j
  by_cases h : i=j <;> simp [tensor,Matrix.one_apply,h]
omit [DecidableEq ι] in
lemma tensor_mul (X Y : Matrix ι ι K) (a b : A) :
    tensor X a * tensor Y b = tensor (X*Y) (a*b) := by
  ext i j
  simp only [Matrix.mul_apply,tensor,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  simp [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,mul_comm]
lemma eval_tensor {α : Type*} (W : α → Matrix ι ι K) (f : α → A) (w : List α) :
    (w.map (fun a=>tensor (W a) (f a))).prod =
      tensor ((w.map W).prod) (DirectCancellation.eval f w) := by
  induction w with
  | nil => exact tensor_one.symm
  | cons a w ih =>
    simp only [List.map_cons,List.prod_cons,DirectCancellation.eval,List.map_cons,List.prod_cons] at *
    rw [ih,tensor_mul]

def letterSum {α : Type*} [Fintype α] (W : α → Matrix ι ι K) (f : α → A) (n : ℕ) : Matrix ι ι A :=
  CutReduction.letterSum (fun a=>tensor (W a) (f a)) n

variable {α Γ : Type*} [Fintype α] [Fintype Γ]
def chunkSum (label : Γ → List α) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) : Matrix ι ι A :=
  CutReduction.chunkSum (fun c=>(label c).length) (fun c=>tensor (W c) (DirectCancellation.eval f (label c))) n
omit [Fintype α] [Fintype Γ] in
lemma eval_flatMap (f : α → A) (label : Γ → List α) (gs : List Γ) :
    DirectCancellation.eval (fun c=>DirectCancellation.eval f (label c)) gs =
      DirectCancellation.eval f (gs.flatMap label) := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    simp only [List.flatMap_cons,DirectCancellation.eval_append]
    exact congrArg (fun x=>DirectCancellation.eval f (label a)*x) ih
omit [Fintype α] in
lemma chunkSum_entry {d : ℕ} (label : Γ → List α) (W : Γ → Matrix (Fin d) (Fin d) K)
    (f : α → A) (n : ℕ) (i j : Fin d) :
    chunkSum label W f n i j = DirectCancellation.chunkSum label W f n i j := by
  unfold chunkSum CutReduction.chunkSum DirectCancellation.chunkSum
  have he : (CutReduction.candidates Γ n).filter (fun gs=>(gs.map (fun c=>(label c).length)).sum=n) =
      (DirectCancellation.candidates Γ n).filter (fun gs=>(DirectCancellation.spell label gs).length=n) := by
    apply Finset.filter_congr
    intro gs _
    simp [DirectCancellation.spell,List.length_flatMap]
  rw [he]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro gs hgs
  have hh := congrArg (fun M : Matrix (Fin d) (Fin d) A=>M i j) (eval_tensor W (fun c=>DirectCancellation.eval f (label c)) gs)
  simpa only [CutReduction.eval,eval_flatMap,tensor,Cancellation.chunkWeight,DirectCancellation.spell] using hh
omit [Fintype α] in
lemma direct_vanish {T : Type*} [CharP K 2] {d b q N : ℕ}
    (label : Γ → List α) (hne : ∀c,label c≠[]) (hb : ∀c,(label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀t,eligible t → ∀x y,erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀x,eligible (erase x) → f x*f x=0)
    (hlong : ∀w : List α,N ≤ w.length → DirectCancellation.eval f w≠0 →
      ∃a e,DirectCancellation.EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(d^2+3)<q) (W : Γ → Matrix (Fin d) (Fin d) K) :
    ∀n,N ≤ n → chunkSum label W f n=0 := by
  intro n hn
  ext i j
  rw [chunkSum_entry]
  exact DirectCancellation.direct_cancellation label hne hb erase eligible f hcomm hsquare hlong hbound W n hn i j
end
end SourceBurnside.MatrixTests
namespace SourceBurnside.CutReduction
noncomputable section
open Classical
open scoped BigOperators
variable {α R : Type*} [Fintype α] [Semiring R]
lemma letterSum_eq_ofFn (f : α → R) (n : ℕ) :
    letterSum f n=∑ w : Fin n → α,eval f (List.ofFn w) := by
  have he : (candidates α n).filter (fun w=>w.length=n)=Finset.univ.image (fun w : Fin n→α=>List.ofFn w) := by
    ext w
    simp only [Finset.mem_filter,mem_candidates,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,hw⟩
      subst n
      exact ⟨w.get,List.ofFn_get w⟩
    · rintro ⟨v,rfl⟩
      simp
  rw [letterSum,he,Finset.sum_image]
  exact fun _ _ _ _ h=>List.ofFn_injective h
end
end SourceBurnside.CutReduction
namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [decι : DecidableEq ι]
variable {α Γ : Type*} [Fintype α] [Fintype Γ]
omit [Fintype ι] decι in
lemma tensor_left_zero (a : A) : tensor (0:Matrix ι ι K) a=0 := by ext;simp [tensor]
omit [Fintype ι] decι in
lemma tensor_sum {J : Type*} (s : Finset J) (W : J → Matrix ι ι K) (a : A) :
    tensor (∑j∈s,W j) a=∑j∈s,tensor (W j) a := by
  ext i j
  simp [tensor,Matrix.sum_apply,Finset.sum_smul]
omit [Fintype Γ] in
lemma bounded_list_injective (n : ℕ) :
    Function.Injective (fun s : Automaton.BoundedSequences Γ n=>List.ofFn s.2) := by
  rintro ⟨⟨i,hi⟩,f⟩ ⟨⟨j,hj⟩,g⟩ he
  have hij : i=j := by simpa using congrArg List.length he
  subst j
  have hfg : f=g := List.ofFn_injective he
  subst g
  rfl
omit [Fintype α] in
lemma chunkSum_eq_sequences (label : Γ → List α) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) :
    chunkSum label W f n=∑s : Automaton.BoundedSequences Γ n,
      if (Automaton.spelled label s).length=n then
        tensor (Automaton.seqWeight W s) (DirectCancellation.eval f (Automaton.spelled label s)) else 0 := by
  unfold chunkSum CutReduction.chunkSum
  rw [Finset.sum_filter,CutReduction.candidates,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s _
    have hl : ((List.ofFn s.2).map (fun c=>(label c).length)).sum=(Automaton.spelled label s).length := by
      simp [Automaton.spelled,List.length_flatten,List.map_ofFn,Function.comp_def]
    rw [hl]
    split_ifs <;> try rfl
    change ((List.ofFn s.2).map (fun c=>tensor (W c) (DirectCancellation.eval f (label c)))).prod=_
    rw [eval_tensor,eval_flatMap]
    simp only [Automaton.seqWeight,Automaton.spelled,List.map_ofFn,List.flatMap]
  · exact fun _ _ _ _ he=>bounded_list_injective n he
lemma sum_wordCoefficient_tensor (label : Γ → List α) (W : Γ → Matrix ι ι K)
    (f : α → A) (n : ℕ) :
    (∑w : Fin n → α,tensor (Automaton.wordCoefficient label W (List.ofFn w))
      (DirectCancellation.eval f (List.ofFn w)))=chunkSum label W f n := by
  have hc (w : Fin n→α) : Automaton.wordCoefficient label W (List.ofFn w)=
      ∑s : Automaton.BoundedSequences Γ n,if Automaton.spelled label s=List.ofFn w then Automaton.seqWeight W s else 0 := by
    have aux (v : List α) (m : ℕ) (hm : v.length=m) : Automaton.wordCoefficient label W v=
        ∑s : Automaton.BoundedSequences Γ m,if Automaton.spelled label s=v then Automaton.seqWeight W s else 0 := by
      subst m
      rfl
    exact aux _ _ List.length_ofFn
  simp_rw [hc,tensor_sum]
  rw [Finset.sum_comm,chunkSum_eq_sequences]
  apply Finset.sum_congr rfl
  intro s _
  have he (w : Fin n→α) : tensor (if Automaton.spelled label s=List.ofFn w then Automaton.seqWeight W s else 0)
      (DirectCancellation.eval f (List.ofFn w)) =
      if List.ofFn w=Automaton.spelled label s then tensor (Automaton.seqWeight W s)
        (DirectCancellation.eval f (Automaton.spelled label s)) else 0 := by
    split_ifs <;> simp_all [tensor_left_zero]
  simp_rw [he]
  exact Automaton.sum_words_eq (Automaton.spelled label s) n _

lemma automaton_block {b : ℕ} (hb : 0<b) (label : Γ → List α) (hne : ∀c,label c≠[])
    (hl : ∀c,(label c).length ≤ b) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) (i j : ι) :
    letterSum (Automaton.blockTransition (b:=b) (Automaton.combinedWeight label W)) f n (Automaton.root hb,i) (Automaton.root hb,j)=
      chunkSum label W f n i j := by
  have he := congrArg (fun M : Matrix ι ι A=>M i j) (sum_wordCoefficient_tensor label W f n)
  rw [letterSum,CutReduction.letterSum_eq_ofFn]
  simp only [CutReduction.eval,eval_tensor,Matrix.sum_apply,tensor] at *
  apply Eq.trans ?_ he
  apply Finset.sum_congr rfl
  intro w _
  have hdec : decι = Classical.decEq ι := Subsingleton.elim _ _
  subst decι
  exact congrArg (fun c : K=>c • DirectCancellation.eval f (List.ofFn w)) (Automaton.root_block_eq_wordCoefficient hb label hne hl W (List.ofFn w) i j)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
omit decι [DecidableEq κ] in
lemma reindex_tensor (e : ι ≃ κ) (W : Matrix ι ι K) (a : A) :
    Matrix.reindexRingEquiv A e (tensor W a)=tensor (Matrix.reindexRingEquiv K e W) a := rfl
omit [Fintype α] in
lemma reindex_chunkSum (e : ι ≃ κ) (label : Γ → List α) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) :
    Matrix.reindexRingEquiv A e (chunkSum label W f n)=chunkSum label (fun c=>Matrix.reindexRingEquiv K e (W c)) f n := by
  simp only [chunkSum,CutReduction.chunkSum,CutReduction.eval,map_sum,map_list_prod,List.map_map,Function.comp_def,reindex_tensor]
omit [Fintype α] in
lemma direct_vanish_finite {T : Type*} [CharP K 2] {b q N : ℕ}
    (label : Γ → List α) (hne : ∀c,label c≠[]) (hb : ∀c,(label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀t,eligible t → ∀x y,erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀x,eligible (erase x) → f x*f x=0)
    (hlong : ∀w : List α,N ≤ w.length → DirectCancellation.eval f w≠0 →
      ∃a e,DirectCancellation.EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*((Fintype.card ι)^2+3)<q) (W : Γ → Matrix ι ι K) :
    ∀n,N ≤ n → chunkSum label W f n=0 := by
  intro n hn
  apply (Matrix.reindexRingEquiv A (Fintype.equivFin ι)).injective
  rw [map_zero,reindex_chunkSum]
  exact direct_vanish label hne hb erase eligible f hcomm hsquare hlong hbound _ n hn
end
end SourceBurnside.MatrixTests

end

end OAI
