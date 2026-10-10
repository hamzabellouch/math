import OAI.Computability.WeisfeilerLeman.Pebbles

namespace OAI

universe uA uB uA' uB' uP uE

namespace WLTime.Pebble
namespace Position
variable {K : ℕ} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}

def map (f : A ≃ A') (g : B ≃ B') (P : Position K A B) : Position K A' B' :=
  fun i => (P i).map (fun xy => (f xy.1,g xy.2))

@[simp] theorem map_none (f : A ≃ A') (g : B ≃ B') :
    map f g (fun _ : Fin K => none) = fun _ => none := rfl

@[simp] theorem map_update (f : A ≃ A') (g : B ≃ B') (P : Position K A B)
    (i : Fin K) (x : A) (y : B) :
    map f g (Function.update P i (some (x,y))) =
      Function.update (map f g P) i (some (f x,g y)) := by
  funext j
  by_cases h : j=i
  · subst j; simp [map]
  · simp [map,h]

@[simp] theorem map_inverse (f : A ≃ A') (g : B ≃ B') (P : Position K A B) :
    map f.symm g.symm (map f g P) = P := by
  funext i
  cases h : P i <;> simp [map,h]

@[simp] theorem map_apply_eq_some (f : A ≃ A') (g : B ≃ B') (P : Position K A B)
    (i : Fin K) (x : A') (y : B') :
    map f g P i = some (x,y) ↔ P i = some (f.symm x,g.symm y) := by
  cases h : P i with
  | none => simp [map,h]
  | some xy =>
    rcases xy with ⟨a,b⟩
    simp [map,h,f.eq_symm_apply,g.eq_symm_apply]

@[simp] theorem map_apply_eq_none (f : A ≃ A') (g : B ≃ B') (P : Position K A B)
    (i : Fin K) : map f g P i = none ↔ P i = none := by simp [map]

end Position

theorem Wins.transport {K : ℕ} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    {G : SimpleGraph A} {H : SimpleGraph B} {G' : SimpleGraph A'} {H' : SimpleGraph B'}
    (f : A ≃ A') (g : B ≃ B')
    (hf : ∀ x y, G.Adj x y ↔ G'.Adj (f x) (f y))
    (hg : ∀ x y, H.Adj x y ↔ H'.Adj (g x) (g y))
    {P : Position K A B} (h : Wins G H (fun _ _ => True) P) :
    Wins G' H' (fun _ _ => True) (Position.map f g P) := by
  classical
  let J : Invariant G' H' (fun _ _ => True) K := {
    safe Q := Wins G H (fun _ _ => True) (Position.map f.symm g.symm Q)
    forget := by
      intro Q R hR hQR
      apply hR.forget
      intro i
      rcases hQR i with hi | hi
      · exact Or.inl (by simp [Position.map,hi])
      · exact Or.inr (by simp [Position.map,hi])
    atomic := by
      intro Q hQ
      refine ⟨fun _ _ _ _ => True.intro,?_⟩
      intro i j x y u v hi hj
      have ha := hQ.atomic.2 i j (f.symm x) (g.symm y) (f.symm u) (g.symm v)
        (by simp [hi]) (by simp [hj])
      simpa only [Equiv.apply_eq_iff_eq, hf, hg, Equiv.apply_symm_apply] using ha
    extend := by
      intro Q hQ i hi
      obtain ⟨e,he⟩ := hQ.extend i (by simp [hi])
      refine ⟨f.symm.trans (e.trans g),fun x => ?_⟩
      simpa only [Position.map_update,Equiv.trans_apply,Equiv.symm_apply_apply] using he (f.symm x) }
  exact ⟨J,by simpa only [J,Position.map_inverse] using h⟩

end WLTime.Pebble

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev Block (K : ℕ) := {b : RawBlock (r := r) (m := m) (P := P) (E := E) K // I.ValidBlock K b}
abbrev Vertex (K : ℕ) (ε : F₂) := (b : I.Block K) × I.Legal K ε b.val

noncomputable instance [Fintype P] [Fintype E] (K : ℕ) : Fintype (I.Block K) := by
  classical
  dsimp [Block]
  infer_instance
noncomputable instance [Fintype P] [Fintype E] (K : ℕ) (ε : F₂) (b : I.Block K) :
    Fintype (I.Legal K ε b.val) := by
  classical
  dsimp [Legal]
  infer_instance

namespace Vertex
variable {I} {K : ℕ} {ε : F₂}
abbrev read (x : I.Vertex K ε) : I.Readouts K := x.2.val.val

theorem ext {x y : I.Vertex K ε} (hb : x.1 = y.1) (hr : x.read = y.read) : x = y := by
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  dsimp at hb
  subst c
  apply congrArg (Sigma.mk b)
  apply Subtype.ext
  exact Subtype.ext hr
end Vertex

open scoped Classical in

noncomputable def valuationGraph (K : ℕ) (ε : F₂) : SimpleGraph (I.Vertex K ε) where
  Adj x y := x.1 ≠ y.1 ∧ (I.footprint K x.1.val ∩ I.footprint K y.1.val).Nonempty ∧
    ∀ n ∈ I.footprint K x.1.val, n ∈ I.footprint K y.1.val → x.read n = y.read n
  symm := ⟨by
    intro x y h
    exact ⟨Ne.symm h.1,by simpa only [Finset.inter_comm] using h.2.1,
      fun n hn hm => (h.2.2 n hm hn).symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def Maps (K : ℕ) (R : I.Readouts K) (x : I.Vertex K 0) (y : I.Vertex K 1) : Prop :=
  x.1 = y.1 ∧ y.read = x.read + (I.atBlock K x.1.val R).val

theorem atBlock_congr (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R S : I.Readouts K)
    (h : ∀ n ∈ I.footprint K b, R n = S n) : I.atBlock K b R = I.atBlock K b S := by
  classical
  apply Subtype.ext
  funext n
  by_cases hn : n ∈ I.footprint K b
  · simpa only [I.atBlock_apply K b R n hn,I.atBlock_apply K b S n hn] using h n hn
  · simp only [atBlock,ite_eq_right hn]

theorem maps_read (K : ℕ) {R : I.Readouts K} {x : I.Vertex K 0} {y : I.Vertex K 1}
    (h : I.Maps K R x y) (n : RawName (r := r) (m := m) (P := P) (E := E) K)
    (hn : n ∈ I.footprint K x.1.val) : y.read n = x.read n + R n := by
  rw [h.2]
  simp only [Pi.add_apply,I.atBlock_apply K _ R n hn]

theorem maps_atomic (K : ℕ) {R : I.Readouts K}
    {x u : I.Vertex K 0} {y v : I.Vertex K 1} (hx : I.Maps K R x y) (hu : I.Maps K R u v) :
    (x = u ↔ y = v) ∧ ((I.valuationGraph K 0).Adj x u ↔ (I.valuationGraph K 1).Adj y v) := by
  classical
  have hb : x.1 = u.1 ↔ y.1 = v.1 := by rw [hx.1,hu.1]
  constructor
  · constructor
    · intro h
      have hyv := hb.mp (congrArg Sigma.fst h)
      apply Vertex.ext hyv
      rw [hx.2,hu.2,h]
    · intro h
      have hxu := hb.mpr (congrArg Sigma.fst h)
      apply Vertex.ext hxu
      have he : x.read + (I.atBlock K x.1.val R).val = u.read + (I.atBlock K u.1.val R).val := by
        rw [← hx.2,← hu.2,h]
      rw [hxu] at he
      exact add_right_cancel he
  · change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    have hs : (I.footprint K x.1.val ∩ I.footprint K u.1.val).Nonempty ↔
        (I.footprint K y.1.val ∩ I.footprint K v.1.val).Nonempty := by rw [hx.1,hu.1]
    refine and_congr (not_congr hb) (and_congr hs ?_)
    constructor
    · intro h n hn hm
      rw [← hx.1] at hn
      rw [← hu.1] at hm
      rw [I.maps_read K hx n hn,I.maps_read K hu n hm,h n hn hm]
    · intro h n hn hm
      have he := h n (hx.1 ▸ hn) (hu.1 ▸ hm)
      rw [I.maps_read K hx n hn,I.maps_read K hu n hm] at he
      exact add_right_cancel he

open scoped Classical in
noncomputable def rawSet (K : ℕ) (U : Finset (I.Block K)) := U.image Subtype.val

@[simp] theorem rawSet_card (K : ℕ) (U : Finset (I.Block K)) : (I.rawSet K U).card = U.card := by
  classical
  exact Finset.card_image_of_injective U Subtype.val_injective

theorem rawSet_mono (K : ℕ) {U V : Finset (I.Block K)} (h : V ⊆ U) : I.rawSet K V ⊆ I.rawSet K U := by
  classical
  exact Finset.image_subset_image h

@[simp] theorem mem_rawSet (K : ℕ) (U : Finset (I.Block K)) (b : I.Block K) :
    b.val ∈ I.rawSet K U ↔ b ∈ U := by
  classical
  constructor
  · intro h
    obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp h
    have he : c = b := Subtype.ext hcb
    exact he ▸ hc
  · intro h
    exact Finset.mem_image.mpr ⟨b,h,rfl⟩

theorem rawSet_valid (K : ℕ) (U : Finset (I.Block K)) :
    ∀ b ∈ I.rawSet K U, I.ValidBlock K b := by
  classical
  intro b hb
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hb
  exact c.property

noncomputable def localOffset [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (b : I.Block K) (R : I.Readouts K)
    (hR : I.OffsetFamily Q K (I.rawSet K {b}) R) : I.Legal K 1 b.val := by
  classical
  refine ⟨I.atBlock K b.val R, ?_⟩
  rw [I.blockForm_atBlock, one_mul]
  exact I.offset_legal Q K hK _ (by simp; omega) R hR b.val (by simp)

noncomputable def assembleTranslations [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (a : I.Block K → I.Readouts K)
    (ha : ∀ b, I.OffsetFamily Q K (I.rawSet K {b}) (a b)) : I.Vertex K 0 ≃ I.Vertex K 1 :=
  Equiv.sigmaCongrRight (fun b => I.translate K b.val (I.localOffset Q K hK b (a b) (ha b)))

theorem assembleTranslations_maps [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (a : I.Block K → I.Readouts K)
    (ha : ∀ b, I.OffsetFamily Q K (I.rawSet K {b}) (a b)) (x : I.Vertex K 0) :
    I.Maps K (a x.1) x (I.assembleTranslations Q K hK a ha x) := by
  exact ⟨rfl,rfl⟩

noncomputable def valuationSystem [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r) (hKr : K ≤ r+2) :
    Pebble.ExactLocalSystem (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun x => some x.1) K where
  State := I.Readouts K
  family U R := I.OffsetFamily Q K (I.rawSet K U) R
  agree U R S := I.AgreeOn K (I.rawSet K U) R S
  maps := I.Maps K
  empty := by
    have h := I.offset_nonempty Q K hr (I.rawSet K ∅) (by simp)
    exact h
  restrict := by
    intro U V hVU hU R hR
    exact I.offset_restrict Q K hK hr (I.rawSet_mono K hVU)
      (by simpa using hU) (by simpa using hU.trans hKr) (I.rawSet_valid K U) R hR
  extend := by
    intro U V hVU hU R hR
    exact I.offset_extend Q K hK hr (I.rawSet_mono K hVU)
      (by simpa using hU) (by simpa using hU.trans hKr) (I.rawSet_valid K U) R hR
  transfer := by
    intro U R S x y hag hxy hxU
    have hx := hxU x.1 rfl
    have hab := I.atBlock_congr K x.1.val R S (hag x.1.val ((I.mem_rawSet K U x.1).mpr hx))
    exact ⟨hxy.1,by rw [← hab]; exact hxy.2⟩
  color := fun h => h.1
  atomic := I.maps_atomic K
  assemble := I.assembleTranslations Q K hK
  assemble_some := by
    intro a ha x b hb
    have he : x.1 = b := Option.some.inj hb
    rw [← he]
    exact I.assembleTranslations_maps Q K hK a ha x
  assemble_none := by intro a ha x h; cases h

theorem ac_colored_wins [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r) (hKr : K ≤ r+2) :
    Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin K => none) :=
  (I.valuationSystem Q K hK hr hKr).wins_empty

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

noncomputable def zeroVertex (K : ℕ) (b : I.Block K) : I.Vertex K 0 := ⟨b,I.zeroValuation K b.val⟩

@[simp] theorem zeroVertex_read (K : ℕ) (b : I.Block K) : (I.zeroVertex K b).read = 0 := rfl

noncomputable def queryPosition (K : ℕ) {s : ℕ} (f : Fin s → I.Block K) (y : Fin s → I.Vertex K 1) :
    Pebble.Position (s+1) (I.Vertex K 0) (I.Vertex K 1) :=
  Fin.lastCases none (fun i => some (I.zeroVertex K (f i),y i))

def Queried (K : ℕ) {s : ℕ} (f : Fin s → I.Block K) (y : Fin s → I.Vertex K 1) : Prop :=
  Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
    (fun x y => x.1 = y.1) (I.queryPosition K f y)

theorem queried_color (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {y : Fin s → I.Vertex K 1}
    (h : I.Queried K f y) (i : Fin s) : f i = (y i).1 := by
  exact h.atomic.1 i.castSucc (I.zeroVertex K (f i)) (y i) (by simp [queryPosition])

theorem queried_exists (K : ℕ) {s : ℕ}
    (h : Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (s+1) => none)) (f : Fin s → I.Block K) :
    ∃ y, I.Queried K f y := by
  classical
  let X : Fin (s+1) → Option (I.Vertex K 0) := Fin.lastCases none (fun i => some (I.zeroVertex K (f i)))
  obtain ⟨Q,hQ,hsrc⟩ := h.realize X
  have hget (i : Fin s) : ∃ y, Q i.castSucc = some (I.zeroVertex K (f i),y) := by
    have he := hsrc i.castSucc
    simp only [X,Fin.lastCases_castSucc] at he
    cases hqi : Q i.castSucc with
    | none => simp [hqi] at he
    | some xy =>
      rcases xy with ⟨x,y⟩
      simp only [hqi,Option.map_some,Option.some.injEq] at he
      subst x
      exact ⟨y,rfl⟩
  choose y hy using hget
  have hlast : Q (Fin.last s) = none := by
    have he := hsrc (Fin.last s)
    simpa only [X,Fin.lastCases_last,Option.map_eq_none_iff] using he
  have heq : Q = I.queryPosition K f y := by
    funext j
    induction j using Fin.lastCases with
    | last => simpa only [queryPosition,Fin.lastCases_last] using hlast
    | cast i => simpa only [queryPosition,Fin.lastCases_castSucc] using hy i
  refine ⟨y,?_⟩
  change Pebble.Wins _ _ _ _
  rw [← heq]
  exact hQ

theorem queried_change_one (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {ys : Fin s → I.Vertex K 1}
    (h : I.Queried K f ys) (i : Fin s) (b : I.Block K) :
    ∃ y, I.Queried K (Function.update f i b) (Function.update ys i y) ∧
      ∀ n ∈ I.footprint K (f i).val, n ∈ I.footprint K b.val → (ys i).read n = y.read n := by
  classical
  obtain ⟨y,hy,hcolor,hcomp⟩ := h.replace i.castSucc (Fin.last s) (Fin.castSucc_ne_last i)
    (by simp [queryPosition]) (I.zeroVertex K b)
  have hpos : Function.update (I.queryPosition K f ys) i.castSucc (some (I.zeroVertex K b,y)) =
      I.queryPosition K (Function.update f i b) (Function.update ys i y) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [queryPosition,(Fin.castSucc_ne_last i).symm]
    | cast j =>
      by_cases he : j = i
      · subst j; simp [queryPosition]
      · have hcast : j.castSucc ≠ i.castSucc := fun hh => he (Fin.castSucc_inj.mp hh)
        simp only [Function.update_of_ne hcast,queryPosition,Fin.lastCases_castSucc,Function.update_of_ne he]
  refine ⟨y,?_,?_⟩
  · change Pebble.Wins _ _ _ _
    rw [← hpos]
    exact hy
  · intro n hn hm
    have hc := hcomp (I.zeroVertex K (f i)) (ys i) (by simp [queryPosition])
    by_cases hb : f i = b
    · have he : I.zeroVertex K (f i) = I.zeroVertex K b := congrArg (I.zeroVertex K) hb
      exact congrArg (fun z : I.Vertex K 1 => z.read n) (hc.1.mp he)
    · have ha : (I.valuationGraph K 0).Adj (I.zeroVertex K (f i)) (I.zeroVertex K b) := by
        refine ⟨hb,⟨n,Finset.mem_inter.mpr ⟨hn,hm⟩⟩,?_⟩
        intro k _ _
        rfl
      have ha' := hc.2.mp ha
      exact ha'.2.2 n (by rwa [← I.queried_color K h i]) (by rwa [← hcolor])

theorem queried_transform (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {ys : Fin s → I.Vertex K 1}
    (h : I.Queried K f ys) (g : Fin s → I.Block K) :
    ∃ zs, I.Queried K g zs ∧ ∀ i n, n ∈ I.footprint K (f i).val → n ∈ I.footprint K (g i).val →
      (ys i).read n = (zs i).read n := by
  classical
  let blend (S : Finset (Fin s)) : Fin s → I.Block K := fun i => if i ∈ S then g i else f i
  have aux (S : Finset (Fin s)) : ∃ zs, I.Queried K (blend S) zs ∧
      (∀ i ∉ S, zs i = ys i) ∧
      (∀ i ∈ S, ∀ n, n ∈ I.footprint K (f i).val → n ∈ I.footprint K (g i).val →
        (ys i).read n = (zs i).read n) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨ys,by simpa only [blend,Finset.notMem_empty,ite_false] using h,by simp,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨zs,hzs,hout,hin⟩ := ih
      obtain ⟨z,hz,hkeep⟩ := I.queried_change_one K hzs i (g i)
      have heq : Function.update (blend S) i (g i) = blend (insert i S) := by
        funext j
        by_cases he : j = i
        · subst j; simp [blend]
        · simp [blend,he]
      refine ⟨Function.update zs i z,heq ▸ hz,?_,?_⟩
      · intro j hj
        have hji : j ≠ i := by intro hh; subst j; exact hj (Finset.mem_insert_self i S)
        rw [Function.update_of_ne hji]
        exact hout j (fun hh => hj (Finset.mem_insert_of_mem hh))
      · intro j hj n hn hm
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [Function.update_self]
          rw [← hout j hi]
          apply hkeep n
          · simpa only [blend,ite_eq_right hi] using hn
          · exact hm
        · have hji : j ≠ i := by intro hh; subst j; exact hi hj
          rw [Function.update_of_ne hji]
          exact hin j hj n hn hm
  obtain ⟨zs,hzs,_,hkeep⟩ := aux Finset.univ
  exact ⟨zs,by simpa only [blend,Finset.mem_univ,ite_true] using hzs,
    fun i n hn hm => hkeep i (Finset.mem_univ i) n hn hm⟩

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

theorem queried_legal (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {y : Fin s → I.Vertex K 1}
    (h : I.Queried K f y) (i : Fin s) :
    I.blockForm K (f i).val (y i).read = I.blockBias K (f i).val := by
  rw [I.queried_color K h i]
  simpa only [one_mul] using (y i).2.property

theorem queried_shared (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {y : Fin s → I.Vertex K 1}
    (h : I.Queried K f y) (i j : Fin s) (hne : f i ≠ f j)
    (n : RawName (r := r) (m := m) (P := P) (E := E) K)
    (hi : n ∈ I.footprint K (f i).val) (hj : n ∈ I.footprint K (f j).val) :
    (y i).read n = (y j).read n := by
  classical
  have ha : (I.valuationGraph K 0).Adj (I.zeroVertex K (f i)) (I.zeroVertex K (f j)) :=
    ⟨hne,⟨n,Finset.mem_inter.mpr ⟨hi,hj⟩⟩,fun _ _ _ => rfl⟩
  have hpair := h.atomic.2 i.castSucc j.castSucc (I.zeroVertex K (f i)) (y i)
    (I.zeroVertex K (f j)) (y j) (by simp [queryPosition]) (by simp [queryPosition])
  exact (hpair.2.mp ha).2.2 n (by rwa [← I.queried_color K h i]) (by rwa [← I.queried_color K h j])

def AddressAllowed (K : ℕ) (t : TypeNode K P E) (a : I.Address) : Prop :=
  ∀ i, I.LabelAllowed K t i (a i)

abbrev horizontalName (K : ℕ) (t : TypeNode K P E) (a : I.Address) (i : Fin (r+1)) :
    RawName (r := r) (m := m) (P := P) (E := E) K :=
  .horizontal i t (a i) (a (finRotate (r+1) i))

abbrev verticalName (K : ℕ) (l : TypeLink K E) (a : I.Address) (i : Fin (r+1)) :
    RawName (r := r) (m := m) (P := P) (E := E) K := .vertical i l (a i)

noncomputable def matchedAddress (K : ℕ) (l : TypeLink K E) (a : I.Address) : I.Address :=
  fun i => linkMatch K (fun e => I.coordinatePerm e i) l (a i)

noncomputable def siteRing (K : ℕ) (t : TypeNode K P E) (a : I.Address) (ha : I.AddressAllowed K t a) :
    Fin (r+1) → I.Block K := fun i =>
  ⟨.site i t (a i) (a (finRotate (r+1) i)),ha i,ha (finRotate (r+1) i)⟩

noncomputable def squareRing (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    Fin (r+1) → I.Block K := fun i =>
  ⟨.square i l (a i) (a (finRotate (r+1) i)),ha i,ha (finRotate (r+1) i)⟩

theorem leftAddress_allowed (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    I.AddressAllowed K (linkLeft K I.src l) a :=
  fun i => I.linkLeft_allowed K l i (a i) (ha i)

theorem rightAddress_allowed (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    I.AddressAllowed K (linkRight K I.dst l) (I.matchedAddress K l a) :=
  fun i => I.linkRight_allowed K l i (a i) (ha i)

noncomputable def horizontalSum (K : ℕ) (t : TypeNode K P E) (a : I.Address)
    (ys : Fin (r+1) → I.Vertex K 1) : I.Value K t := ∑ i, (ys i).read (I.horizontalName K t a i)

theorem squareRing_injective (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    Function.Injective (I.squareRing K l a ha) := by
  intro i j h
  exact congrArg (fun b : I.Block K => BlockName.row b.val) h

theorem squareRing_vertical (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.squareRing K l a ha) ys) (i : Fin (r+1)) :
    (ys i).read (I.verticalName K l a (finRotate (r+1) i)) =
      (ys (finRotate (r+1) i)).read (I.verticalName K l a (finRotate (r+1) i)) := by
  apply I.queried_shared K h i (finRotate (r+1) i)
  · intro he
    exact rotate_ne_self hr i ((I.squareRing_injective K l a ha he).symm)
  · simp [squareRing,footprint,verticalName]
  · simp [squareRing,footprint,verticalName]

theorem squareRing_equation (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.squareRing K l a ha) ys) :
    I.leftForm K l (I.horizontalSum K (linkLeft K I.src l) a ys) +
      I.rightForm K l (I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) ys) =
        I.linkBias K l := by
  have heq (i : Fin (r+1)) :
      I.leftForm K l ((ys i).read (I.horizontalName K (linkLeft K I.src l) a i)) +
      I.rightForm K l ((ys i).read (I.horizontalName K (linkRight K I.dst l) (I.matchedAddress K l a) i)) +
      ((ys i).read (I.verticalName K l a i) : F₂) +
      ((ys i).read (I.verticalName K l a (finRotate (r+1) i)) : F₂) = seam i * I.linkBias K l :=
    I.queried_legal K h i
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => heq i)
  simp only [Finset.sum_add_distrib] at hsum
  have hver : (∑ i, (ys i).read (I.verticalName K l a (finRotate (r+1) i)) : F₂) =
      (∑ i, (ys i).read (I.verticalName K l a i) : F₂) := by
    calc
      _ = (∑ i, (ys (finRotate (r+1) i)).read (I.verticalName K l a (finRotate (r+1) i)) : F₂) :=
        Finset.sum_congr rfl (fun i _ => I.squareRing_vertical K hr l a ha h i)
      _ = _ := Equiv.sum_comp (M := F₂) (finRotate (r+1)) (fun i => (ys i).read (I.verticalName K l a i))
  have hseam : (∑ i : Fin (r+1), seam i * I.linkBias K l) = I.linkBias K l := by simp [seam]
  rw [hver,hseam] at hsum
  simpa only [horizontalSum,map_sum,add_assoc,CharTwo.add_self_eq_zero,add_zero] using hsum

theorem ring_transfer_left (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.siteRing K (linkLeft K I.src l) a (I.leftAddress_allowed K l a ha)) ys) :
    ∃ zs, I.Queried K (I.siteRing K (linkRight K I.dst l) (I.matchedAddress K l a)
      (I.rightAddress_allowed K l a ha)) zs ∧
      I.leftForm K l (I.horizontalSum K (linkLeft K I.src l) a ys) +
      I.rightForm K l (I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) zs) = I.linkBias K l := by
  obtain ⟨qs,hqs,hleft⟩ := I.queried_transform K h (I.squareRing K l a ha)
  obtain ⟨zs,hzs,hright⟩ := I.queried_transform K hqs
    (I.siteRing K (linkRight K I.dst l) (I.matchedAddress K l a) (I.rightAddress_allowed K l a ha))
  have hl : I.horizontalSum K (linkLeft K I.src l) a ys = I.horizontalSum K (linkLeft K I.src l) a qs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hleft i
    · simp [siteRing,footprint,horizontalName]
    · simp [squareRing,footprint,horizontalName]
  have hr' : I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) qs =
      I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) zs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hright i
    · simp [squareRing,footprint,horizontalName,matchedAddress]
    · simp [siteRing,footprint,horizontalName]
  exact ⟨zs,hzs,by rw [hl,← hr']; exact I.squareRing_equation K hr l a ha hqs⟩

theorem ring_transfer_right (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.siteRing K (linkRight K I.dst l) (I.matchedAddress K l a)
      (I.rightAddress_allowed K l a ha)) ys) :
    ∃ zs, I.Queried K (I.siteRing K (linkLeft K I.src l) a (I.leftAddress_allowed K l a ha)) zs ∧
      I.leftForm K l (I.horizontalSum K (linkLeft K I.src l) a zs) +
      I.rightForm K l (I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) ys) = I.linkBias K l := by
  obtain ⟨qs,hqs,hright⟩ := I.queried_transform K h (I.squareRing K l a ha)
  obtain ⟨zs,hzs,hleft⟩ := I.queried_transform K hqs
    (I.siteRing K (linkLeft K I.src l) a (I.leftAddress_allowed K l a ha))
  have hl : I.horizontalSum K (linkLeft K I.src l) a qs = I.horizontalSum K (linkLeft K I.src l) a zs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hleft i
    · simp [squareRing,footprint,horizontalName]
    · simp [siteRing,footprint,horizontalName]
  have hr' : I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) ys =
      I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) qs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hright i
    · simp [siteRing,footprint,horizontalName]
    · simp [squareRing,footprint,horizontalName,matchedAddress]
  exact ⟨zs,hzs,by rw [← hl,hr']; exact I.squareRing_equation K hr l a ha hqs⟩

end ConsistencyData
end WLTime.Compression

end OAI
