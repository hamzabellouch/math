import OAI.Computability.StarHeight.UsableCopies

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uI uI2 uM uM2 uAlphabet2 uAlphabet3 uAlphabet4
universe uM3

namespace FiniteRecognition

variable {Alphabet : Type uAlphabet}

lemma regular_mul {L R : Language Alphabet} (hL : L.IsRegular) (hR : R.IsRegular) :
    (L*R).IsRegular := by
  let combine (q : Language Alphabet) (s : Set (Language Alphabet)) : Language Alphabet :=
    let U : Language Alphabet := {w | ∃ r ∈ s, w ∈ r}
    q*R + U
  apply Language.IsRegular.of_finite_range_leftQuotient
  apply (hL.finite_range_leftQuotient.image2 combine hR.finite_range_leftQuotient.powerset).subset
  rintro _ ⟨x,rfl⟩
  let s : Set (Language Alphabet) := {r | ∃ u v, x=u++v ∧ u∈L ∧ r=R.leftQuotient v}
  refine ⟨L.leftQuotient x, ⟨x,rfl⟩, s, ?_, ?_⟩
  · rintro r ⟨u,v,_,_,rfl⟩
    exact ⟨v,rfl⟩
  · ext y
    change (y∈(L.leftQuotient x)*R ∨ ∃ r∈s,y∈r) ↔ x++y∈L*R
    constructor
    · rintro (hy | ⟨r,⟨u,v,hx,hu,hr⟩,hy⟩)
      · obtain ⟨u,hu,v,hv,rfl⟩ := Language.mem_mul.mp hy
        exact Language.mem_mul.mpr ⟨x++u,hu,v,hv,by simp⟩
      · rw [hr] at hy
        exact Language.mem_mul.mpr ⟨u,hu,v++y,hy,by simp [hx]⟩
    · rintro ⟨u,hu,v,hv,he⟩
      rcases List.append_eq_append_iff.mp he.symm with ⟨a,ha,hy⟩ | ⟨a,ha,hv'⟩
      · left
        refine Language.mem_mul.mpr ⟨a,?_,v,hv,hy.symm⟩
        change x++a∈L
        rwa [←ha]
      · right
        refine ⟨R.leftQuotient a,⟨u,a,ha,hu,rfl⟩,?_⟩
        change a++y∈R
        rw [←hv']
        exact hv

lemma regular_finite {L : Language Alphabet} (hL : (L : Set (List Alphabet)).Finite) :
    L.IsRegular := by
  let S : Set (List Alphabet) := ⋃ w∈L, {v | v∈w.tails}
  have hS : S.Finite := hL.biUnion (fun w _ => w.tails.finite_toSet)
  apply Language.IsRegular.of_finite_range_leftQuotient
  apply hS.powerset.subset
  rintro _ ⟨x,rfl⟩ y hy
  exact Set.mem_iUnion_of_mem (x++y) (Set.mem_iUnion_of_mem hy
    ((List.mem_tails _ _).mpr ⟨x,rfl⟩))

lemma regular_singleton (w : List Alphabet) : ({w} : Language Alphabet).IsRegular :=
  regular_finite (Set.finite_singleton w)

lemma regular_finset_iSup {I : Type uI} (s : Finset I) (L : I → Language Alphabet)
    (h : ∀ i∈s, (L i).IsRegular) : (⨆ i∈s,L i).IsRegular := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty,iSup_false,iSup_bot]
    exact regular_finite Set.finite_empty
  | @insert i s hi ih =>
    have he : (⨆ j∈insert i s,L j)=L i+(⨆ j∈s,L j) := by
      ext w
      simp only [Language.mem_iSup,Finset.mem_insert,Language.mem_add]
      aesop
    rw [he]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma regular_iSup {I : Type uI2} [Finite I] (L : I → Language Alphabet)
    (h : ∀ i, (L i).IsRegular) : (⨆ i,L i).IsRegular := by
  classical
  let := Fintype.ofFinite I
  simpa only [Finset.mem_univ, iSup_pos] using
    regular_finset_iSup (Finset.univ : Finset I) L (fun i _ => h i)

lemma regular_recognized {M : Type uM} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (F : Set M) :
    Language.IsRegular ({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet) := by
  let A : DFA Alphabet M := ⟨fun q a => q*T (FreeMonoid.of a),1,F⟩
  have he : ∀ (w : List Alphabet) (q : M), A.evalFrom q w=q*T (FreeMonoid.ofList w) := by
    intro w
    induction w with
    | nil => intro q;simp [DFA.evalFrom]
    | cons a w ih =>
      intro q
      rw [DFA.evalFrom_cons,ih]
      change q*T (FreeMonoid.of a)*T (FreeMonoid.ofList w)=q*T (FreeMonoid.of a*FreeMonoid.ofList w)
      rw [map_mul,mul_assoc]
  apply Language.isRegular_iff.mpr
  refine ⟨M,inferInstance,A,?_⟩
  ext w
  simp only [DFA.mem_accepts,DFA.eval,he]
  change 1*T (FreeMonoid.ofList w)∈F ↔ T (FreeMonoid.ofList w)∈F
  rw [one_mul]

lemma regular_sandwich [Finite Alphabet] {M : Type uM2} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (N tail : ℕ) (L : Language Alphabet)
    (hc : ∀ (a b x y : List Alphabet), a.length=N → b.length=tail →
      T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y) →
      (a++x++b∈L ↔ a++y++b∈L)) : L.IsRegular := by
  classical
  let small : Language Alphabet := {w | w.length<N+tail ∧ w∈L}
  have hsmall : small.IsRegular := regular_finite
    ((List.finite_length_le Alphabet (N+tail)).subset (fun w hw => hw.1.le))
  let As := (List.finite_length_le Alphabet N).toFinset.filter (fun a => a.length=N)
  let Bs := (List.finite_length_le Alphabet tail).toFinset.filter (fun b => b.length=tail)
  let F (a b : List Alphabet) : Set M := {q | ∃ x, T (FreeMonoid.ofList x)=q ∧ a++x++b∈L}
  let R (a b : List Alphabet) : Language Alphabet :=
    let mid : Language Alphabet := {x | T (FreeMonoid.ofList x)∈F a b}
    ({a} : Language Alphabet)*mid*({b} : Language Alphabet)
  have hR : ∀ a b, (R a b).IsRegular := fun a b =>
    regular_mul (regular_mul (regular_singleton a) (regular_recognized T (F a b)))
      (regular_singleton b)
  have he : L=small+(⨆ a∈As,⨆ b∈Bs,R a b) := by
    ext w
    constructor
    · intro hw
      by_cases hl : w.length<N+tail
      · exact Or.inl ⟨hl,hw⟩
      · let a := w.take N
        let x := (w.drop N).take (w.length-N-tail)
        let b := w.drop (w.length-tail)
        have ha : a.length=N := by simp only [a,List.length_take];omega
        have hb : b.length=tail := by simp only [b,List.length_drop];omega
        have hw' : a++x++b=w := by
          have hcut : N+(w.length-N-tail)=w.length-tail := by omega
          dsimp [a,x,b]
          rw [←hcut,←List.drop_drop,List.append_assoc,List.take_append_drop,List.take_append_drop]
        right
        apply Language.mem_iSup.mpr
        refine ⟨a,Language.mem_iSup.mpr ⟨?_,Language.mem_iSup.mpr ⟨b,Language.mem_iSup.mpr ⟨?_,?_⟩⟩⟩⟩
        · simp only [As,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,ha,le_refl,and_self]
        · simp only [Bs,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,hb,le_refl,and_self]
        · rw [←hw']
          exact Language.append_mem_mul (Language.append_mem_mul (Set.mem_singleton _)
            ⟨x,rfl,by simpa only [hw'] using hw⟩) (Set.mem_singleton _)
    · rintro (⟨_,hw⟩ | hw)
      · exact hw
      · obtain ⟨a,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨ha,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨b,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨hb,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨u,hu,v,hv,rfl⟩ := Language.mem_mul.mp hw
        obtain ⟨a',ha',x,hx,rfl⟩ := Language.mem_mul.mp hu
        have ha'eq : a'=a := ha'
        subst a'
        have hveq : v=b := hv
        subst v
        obtain ⟨y,hy,hyL⟩ := hx
        exact (hc a b y x (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hy).mp hyL
  rw [he]
  exact hsmall.add (regular_finset_iSup As _ (fun a _ =>
    regular_finset_iSup Bs _ (fun b _ => hR a b)))

end FiniteRecognition
namespace PeriodicSummary

variable {Alphabet : Type uAlphabet2} {p : ℕ}

noncomputable def matcher (v : ZMod p → Alphabet) : DFA Alphabet (Option (ZMod p)) := by
  classical
  exact ⟨fun q a => q.bind (fun i => if a=v i then some (i+1) else none),some 0, {q | q.isSome}⟩

def Fits (v : ZMod p → Alphabet) : ZMod p → List Alphabet → Prop
  | _, [] => True
  | q, a::w => a=v q ∧ Fits v (q+1) w

lemma eval_none (v : ZMod p → Alphabet) (w : List Alphabet) :
    (matcher v).evalFrom none w=none := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [DFA.evalFrom_cons,matcher] using ih

lemma eval_isSome (v : ZMod p → Alphabet) (w : List Alphabet) (q : ZMod p) :
    ((matcher v).evalFrom (some q) w).isSome ↔ Fits v q w := by
  classical
  induction w generalizing q with
  | nil => simp [DFA.evalFrom_nil,Fits]
  | cons a w ih =>
    rw [DFA.evalFrom_cons]
    change ((matcher v).evalFrom (if a=v q then some (q+1) else none) w).isSome ↔ _
    by_cases h : a=v q
    · rw [ite_eq_left h,ih]
      simp only [Fits,h,true_and]
    · rw [ite_eq_right h,eval_none]
      simp only [Option.isSome_none,Bool.false_eq_true,Fits,h,false_and]

lemma fits_iff (v : ZMod p → Alphabet) (w : List Alphabet) (q : ZMod p) :
    Fits v q w ↔ ∀ i : Fin w.length, w[i.val]=v (q+i.val) := by
  induction w generalizing q with
  | nil => simp [Fits]
  | cons a w ih =>
    simp only [Fits,ih,List.length_cons,Fin.forall_fin_succ,List.getElem_cons_zero,
      List.getElem_cons_succ,Fin.val_zero,Nat.cast_zero,add_zero,Fin.val_succ,Nat.cast_add,
      Nat.cast_one]
    constructor
    · rintro ⟨ha,hw⟩
      exact ⟨ha,fun i => by simpa [add_assoc,add_comm,add_left_comm] using hw i⟩
    · rintro ⟨ha,hw⟩
      exact ⟨ha,fun i => by simpa [add_assoc,add_comm,add_left_comm] using hw i⟩

noncomputable def transition : FreeMonoid Alphabet →*
    ((ZMod p → Alphabet) → (Function.End (Option (ZMod p)))ᵐᵒᵖ) :=
  MonoidHom.pi (fun v => FiniteRecognition.transition (matcher v))

lemma fits_congr {x y : List Alphabet}
    (h : transition (p := p) (FreeMonoid.ofList x)=transition (FreeMonoid.ofList y))
    (v : ZMod p → Alphabet) (q : ZMod p) : Fits v q x ↔ Fits v q y := by
  have he := congrArg (fun t => (t v).unop (some q)) h
  change (matcher v).evalFrom (some q) x=(matcher v).evalFrom (some q) y at he
  rw [←eval_isSome,←eval_isSome,he]

end PeriodicSummary

namespace PeriodicSummary

variable {Alphabet : Type uAlphabet3}

def lengthMod (n : ℕ) : FreeMonoid Alphabet →* Multiplicative (ZMod n) where
  toFun w := Multiplicative.ofAdd (w.toList.length:ZMod n)
  map_one' := by simp only [FreeMonoid.toList_one,List.length_nil,Nat.cast_zero]; rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((x.toList++y.toList).length:ZMod n)=_
    simp only [List.length_append,Nat.cast_add]
    rfl

lemma lengthMod_dvd {n : ℕ} {x y : List Alphabet}
    (h : lengthMod n (FreeMonoid.ofList x)=lengthMod n (FreeMonoid.ofList y)) :
    (n:ℤ) ∣ (y.length:ℤ)-x.length := by
  have he : (x.length:ZMod n)=(y.length:ZMod n) := congrArg Multiplicative.toAdd h
  have hz : ((x.length:ℤ):ZMod n)=((y.length:ℤ):ZMod n) := by simpa only [Int.cast_natCast] using he
  exact ((ZMod.intCast_eq_intCast_iff _ _ _).mp hz).dvd

end PeriodicSummary
namespace StreamSplice

open WordIntervals LocalMarkers

variable {Alphabet : Type uAlphabet4}

noncomputable def splice (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) (z : ℤ) : Alphabet :=
  if h : z<N then f z else if h' : z<N+y.length then
    y[(z-N).toNat]'(by omega) else f (z-((y.length:ℤ)-x.length))

lemma splice_left (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) {z : ℤ} (hz : z<N) :
    splice f N x y z=f z := by simp only [splice,dite_eq_left hz]

lemma splice_right (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) {z : ℤ}
    (hz : N+y.length≤z) : splice f N x y z=f (z-((y.length:ℤ)-x.length)) := by
  have hy : (0:ℤ)≤y.length := Int.natCast_nonneg _
  simp only [splice,dite_eq_right (show ¬z<N by omega),dite_eq_right (show ¬z<N+y.length by omega)]

lemma splice_middle (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) :
    Realizes y N (splice f N x y) := by
  intro i
  rw [splice,dite_eq_right (show ¬N+(i.val:ℤ)<N by omega),
    dite_eq_left (show N+(i.val:ℤ)<N+y.length by omega)]
  simp only [add_sub_cancel_left,Int.toNat_natCast]

lemma splice_realizes {f : ℤ → Alphabet} {a b x : List Alphabet}
    (hf : Realizes (a++x++b) 0 f) (y : List Alphabet) :
    Realizes (a++y++b) 0 (splice f a.length x y) := by
  have ha := hf.append_left.append_left
  have hb := hf.append_right
  apply Realizes.append
  · apply Realizes.append
    · intro i
      rw [splice_left f a.length x y (by omega)]
      exact ha i
    · simpa only [zero_add] using splice_middle f a.length x y
  · intro i
    rw [splice_right f a.length x y (by simp only [List.length_append,Nat.cast_add];omega)]
    have hh := hb i
    simp only [List.length_append,Nat.cast_add,zero_add] at hh ⊢
    convert hh using 2
    omega

structure Frame (f f' : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) : Prop where
  left : ∀ z, z<N → f' z=f z
  oldMiddle : Realizes x N f
  newMiddle : Realizes y N f'
  right : ∀ z, N+y.length≤z → f' z=f (z-((y.length:ℤ)-x.length))

lemma splice_frame {f : ℤ → Alphabet} {a b x : List Alphabet}
    (hf : Realizes (a++x++b) 0 f) (y : List Alphabet) :
    Frame f (splice f a.length x y) a.length x y := by
  refine ⟨fun z hz => splice_left f a.length x y hz,?_,splice_middle f a.length x y,
    fun z hz => splice_right f a.length x y hz⟩
  simpa only [zero_add] using hf.append_left.append_right

namespace Frame

variable {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet} (H : Frame f f' N x y)

include H

lemma agrees_left {s t : ℤ} (ht : t≤N) : AgreesOn f f' s t := by
  intro z _ hz
  exact (H.left z (hz.trans_le ht)).symm

lemma piece_left {s t : ℤ} (hst : s ≤ t) (ht : t≤N) : piece f s t=piece f' s t :=
  piece_congr hst (H.agrees_left ht)

lemma piece_right {s t : ℤ} (hs : N+x.length ≤ s) :
    piece f' (s+((y.length:ℤ)-x.length)) (t+((y.length:ℤ)-x.length))=piece f s t := by
  dsimp [piece]
  have hl : (t+((y.length:ℤ)-x.length)-(s+((y.length:ℤ)-x.length))).toNat=(t-s).toNat := by
    congr 1;ring
  rw [hl]
  apply List.ofFn_inj.mpr
  funext i
  rw [H.right _ (by omega)]
  congr 1
  ring

lemma product {M : Type uM3} [Monoid M] (T : FreeMonoid Alphabet →* M)
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y)) {s b : ℤ}
    (hs : s≤N) (hb : N+x.length≤b) :
    WordIntervals.product T f' s (b+((y.length:ℤ)-x.length))=WordIntervals.product T f s b := by
  have hx : N≤N+(x.length:ℤ) := by omega
  have hy : N≤N+(y.length:ℤ) := by omega
  have hb' : N+(y.length:ℤ)≤b+((y.length:ℤ)-x.length) := by omega
  unfold WordIntervals.product
  rw [piece_append f' hs (hy.trans hb'),piece_append f hs (hx.trans hb)]
  rw [piece_append f' hy hb',piece_append f hx hb]
  rw [H.piece_left hs (le_refl _),WordIntervals.realizes_piece H.oldMiddle,
    WordIntervals.realizes_piece H.newMiddle]
  have ht : piece f' (N+y.length) (b+((y.length:ℤ)-x.length))=piece f (N+x.length) b := by
    have hh := H.piece_right (s := N+x.length) (t := b) (le_refl _)
    simpa only [show N+(x.length:ℤ)+((y.length:ℤ)-x.length)=N+y.length by ring] using hh
  rw [ht]
  change T (FreeMonoid.ofList (piece f' s N)*(FreeMonoid.ofList y*
      FreeMonoid.ofList (piece f (N+x.length) b)))=
    T (FreeMonoid.ofList (piece f' s N)*(FreeMonoid.ofList x*
      FreeMonoid.ofList (piece f (N+x.length) b)))
  simp only [map_mul,hT]

end Frame
end StreamSplice

end GeneralizedStarHeight

end OAI
