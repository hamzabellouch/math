import OAI.GroupTheory.ArtinCAT0.Detour

namespace OAI

open scoped Classical
namespace ArtinCAT0.AmalgamTools
open Monoid Monoid.CoprodI Monoid.PushoutI Monoid.PushoutI.NormalWord
variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
variable {φ : ∀ i, H →* G i}

lemma reduced_append {i j k l : ι} (a : NeWord G i j) (h : j≠k) (b : NeWord G k l) :
    Reduced φ (a.append h b).toWord ↔ Reduced φ a.toWord ∧ Reduced φ b.toWord := by
  simp only [Reduced,NeWord.toWord,NeWord.toList,List.mem_append]
  aesop

lemma reduced_singleton {i : ι} (g : G i) (hg : g≠1) :
    Reduced φ (NeWord.singleton g hg).toWord ↔ g∉(φ i).range := by
  simp [Reduced,NeWord.toWord]

lemma reduced_inv {i j : ι} (a : NeWord G i j) (ha : Reduced φ a.toWord) :
    Reduced φ a.inv.toWord := by
  induction a with
  | singleton g hg =>
    simpa only [NeWord.inv,reduced_singleton,inv_mem_iff] using (reduced_singleton g hg).mp ha
  | append a h b iha ihb =>
    rw [reduced_append] at ha
    exact (reduced_append _ _ _).mpr ⟨ihb ha.2,iha ha.1⟩

lemma reduced_not_factor (hφ : ∀ i, Function.Injective (φ i))
    {w : Word G} (hw : Reduced φ w) {k : ι}
    (hk : ∃ g∈w.toList, g.1≠k) : ofCoprodI (φ:=φ) w.prod ∉ (PushoutI.of k).range := by
  rintro ⟨b,hb⟩
  by_cases hr : b∈(φ k).range
  · obtain ⟨c,hc⟩ := hr
    have he := hw.eq_empty_of_mem_range hφ ⟨c,by rw [← hc,of_apply_eq_base] at hb; exact hb⟩
    subst w
    simp [Word.empty] at hk
  · obtain ⟨d⟩ := transversal_nonempty φ hφ
    obtain ⟨w',hw',htypes⟩ := hw.exists_normalWord_prod_eq d
    let b' : NormalWord d := NormalWord.cons b NormalWord.empty (by change (none : Option ι) ≠ some k; intro h; cases h) hr
    have hb' : b'.prod=PushoutI.of k b := by
      dsimp only [b']
      rw [NormalWord.prod_cons,NormalWord.prod_empty,mul_one]
    have he : w'=b' := NormalWord.prod_injective (hw'.trans (hb.symm.trans hb'.symm))
    rw [he] at htypes
    obtain ⟨g,hg,hgk⟩ := hk
    have hh : g.1 ∈ w.toList.map Sigma.fst := List.mem_map.mpr ⟨g,hg,rfl⟩
    rw [← htypes] at hh
    have hh' : g.1=k := by
      simpa [b',NormalWord.cons,Word.cons,NormalWord.empty,Word.empty] using hh
    exact hgk hh'

/-- A reduced word is either a single-factor element, or conjugating an element
whose factor-conjugacy class avoids the base produces a reduced word still
containing a letter from another factor. -/
lemma conjugate_certificate {k i j : ι} (w : NeWord G i j) (hw : Reduced φ w.toWord) :
    (∃ b : G k, ofCoprodI (φ:=φ) w.prod=PushoutI.of k b ∧ i=k ∧ j=k) ∨
    (∀ q : G k, (∀ b : G k, b*q*b⁻¹∉(φ k).range) →
      ∃ v : NeWord G i i, Reduced φ v.toWord ∧
        ofCoprodI (φ:=φ) v.prod = ofCoprodI (φ:=φ) w.prod * PushoutI.of k q *
          (ofCoprodI (φ:=φ) w.prod)⁻¹ ∧ ∃ g∈v.toList, g.1≠k) := by
  induction w with
  | @singleton i g hg =>
    by_cases hi : i=k
    · subst i
      exact Or.inl ⟨g,by simp,rfl,rfl⟩
    · right
      intro q hq
      have hqr : q∉(φ k).range := by simpa using hq 1
      have hq1 : q≠1 := fun he => hqr (he ▸ (φ k).range.one_mem)
      let a : NeWord G i i := .singleton g hg
      let b : NeWord G k k := .singleton q hq1
      let v := (a.append hi b).append (Ne.symm hi) a.inv
      refine ⟨v,(reduced_append _ _ _).mpr ⟨(reduced_append _ _ _).mpr
        ⟨hw,(reduced_singleton q hq1).mpr hqr⟩,reduced_inv a hw⟩,?_,?_⟩
      · simp [v,a,b]
      · exact ⟨⟨i,g⟩,by simp [v,a],hi⟩
  | @append i j l m a h b iha ihb =>
    obtain ⟨ha,hb⟩ := (reduced_append a h b).mp hw
    rcases ihb hb with ⟨c,hc,hl,hm⟩ | hcb
    · subst l; subst m
      rcases iha ha with ⟨e,he,hi,hj⟩ | hca
      · exact False.elim (h hj)
      · right
        intro q hq
        obtain ⟨v,hv,hvp,hvm⟩ := hca (c*q*c⁻¹) (by
          intro e
          convert hq (e*c) using 1; group)
        refine ⟨v,hv,?_,hvm⟩
        simp only [hvp,NeWord.append_prod,map_mul,map_inv,hc]
        group
    · right
      intro q hq
      obtain ⟨v,hv,hvp,hvm⟩ := hcb q hq
      let u := (a.append h v).append h.symm a.inv
      refine ⟨u,(reduced_append _ _ _).mpr ⟨(reduced_append _ _ _).mpr ⟨ha,hv⟩,
        reduced_inv a ha⟩,?_,?_⟩
      · simp only [u,NeWord.append_prod,NeWord.inv_prod,map_mul,map_inv,hvp]
        group
      · obtain ⟨g,hg,hgk⟩ := hvm
        exact ⟨g,by simp only [u,NeWord.toList,List.mem_append]; exact Or.inl (Or.inr hg),hgk⟩

lemma normal_reduced (d : Transversal φ) (w : NormalWord d) : Reduced φ w.toWord := by
  rintro ⟨i,g⟩ hg hr
  have hself := (Subgroup.IsComplement.equiv_snd_eq_self_iff_mem (d.compl i) (φ i).range.one_mem).mpr
    (w.normalized i g hg)
  have hone := (Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem (d.compl i) (d.one_mem i)).mpr hr
  exact w.ne_one ⟨i,g⟩ hg (hself.symm.trans hone)

/-- Centralizers cannot escape the factor when the factor-conjugacy class
of the element misses the amalgamating subgroup. -/
theorem centralizer_in_factor (hφ : ∀ i, Function.Injective (φ i)) (k : ι) (q : G k)
    (hq : ∀ b : G k, b*q*b⁻¹∉(φ k).range)
    (g : PushoutI φ) (hg : Commute g (PushoutI.of k q)) : g∈(PushoutI.of k).range := by
  classical
  obtain ⟨d⟩ := transversal_nonempty φ hφ
  let w : NormalWord d := NormalWord.equiv g
  have hwp : w.prod=g := (NormalWord.equiv (d:=d)).symm_apply_apply g
  have hp : PushoutI.base φ w.head * ofCoprodI (φ:=φ) w.toWord.prod=g := hwp
  have hh : PushoutI.base φ w.head ∈ (PushoutI.of k).range :=
    ⟨φ k w.head,of_apply_eq_base φ k w.head⟩
  by_cases he : w.toWord=Word.empty
  · have hgg : g=PushoutI.base φ w.head := by simpa [he] using hp.symm
    exact hgg ▸ hh
  · obtain ⟨i,j,v,hv⟩ := NeWord.of_word w.toWord he
    have hvr : Reduced φ v.toWord := hv.symm ▸ normal_reduced d w
    rcases conjugate_certificate (k:=k) v hvr with ⟨b,hb,_,_⟩ | hc
    · rw [← hv] at hp
      change PushoutI.base φ w.head * ofCoprodI (φ:=φ) v.prod=g at hp
      have hbmem : ofCoprodI (φ:=φ) v.prod∈(PushoutI.of (φ:=φ) k).range := ⟨b,hb.symm⟩
      exact hp ▸ (PushoutI.of (φ:=φ) k).range.mul_mem hh hbmem
    · obtain ⟨u,hur,hup,hum⟩ := hc q hq
      have hnot := reduced_not_factor hφ hur hum
      apply False.elim
      apply hnot
      change ofCoprodI (φ:=φ) u.prod∈(PushoutI.of (φ:=φ) k).range
      rw [hup]
      have hp' : ofCoprodI (φ:=φ) v.prod=(PushoutI.base φ w.head)⁻¹*g := by
        rw [← hp,← hv]
        simp [NeWord.prod]
      rw [hp']
      have hg' : g * PushoutI.of k q * g⁻¹=PushoutI.of k q := hg.mul_inv_cancel
      have hh' : (PushoutI.base φ w.head)⁻¹*g*PushoutI.of k q*
          ((PushoutI.base φ w.head)⁻¹*g)⁻¹ =
          (PushoutI.base φ w.head)⁻¹*PushoutI.of k q*PushoutI.base φ w.head := by
        calc
          _ = (PushoutI.base φ w.head)⁻¹*(g*PushoutI.of k q*g⁻¹)*PushoutI.base φ w.head := by group
          _ = _ := by rw [hg']
      rw [hh']
      exact (PushoutI.of (φ:=φ) k).range.mul_mem ((PushoutI.of (φ:=φ) k).range.mul_mem
        ((PushoutI.of (φ:=φ) k).range.inv_mem hh) ⟨q,rfl⟩) hh

end ArtinCAT0.AmalgamTools

namespace ArtinCAT0.BinaryAmalgam
open Monoid
universe u
variable {A B H K : Type u} [Group A] [Group B] [Group H] [Group K]
def Family (A B : Type u) : Bool → Type u
  | false => A
  | true => B
instance familyGroup : ∀ i, Group (Family A B i)
  | false => inferInstanceAs (Group A)
  | true => inferInstanceAs (Group B)
def diagram (f : H →* A) (g : H →* B) : ∀ i, H →* Family A B i
  | false => f
  | true => g
abbrev GroupOf (f : H →* A) (g : H →* B) := PushoutI (diagram f g)
def left (f : H →* A) (g : H →* B) : A →* GroupOf f g := PushoutI.of (φ:=diagram f g) false
def right (f : H →* A) (g : H →* B) : B →* GroupOf f g := PushoutI.of (φ:=diagram f g) true
lemma agree (f : H →* A) (g : H →* B) : (left f g).comp f=(right f g).comp g := by
  exact (PushoutI.of_comp_eq_base (φ:=diagram f g) false).trans (PushoutI.of_comp_eq_base (φ:=diagram f g) true).symm
lemma diagram_injective {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∀ i, Function.Injective (diagram f g i) := by
  intro i; cases i; exact hf; exact hg
lemma left_injective {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (left f g) :=
  PushoutI.of_injective (diagram_injective hf hg) false
lemma right_injective {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (right f g) :=
  PushoutI.of_injective (diagram_injective hf hg) true

def targets (l : A →* K) (r : B →* K) : ∀ i, Family A B i →* K
  | false => l
  | true => r

def lift {f : H →* A} {g : H →* B} (l : A →* K) (r : B →* K)
    (h : l.comp f=r.comp g) : GroupOf f g →* K :=
  PushoutI.lift (targets l r) (l.comp f) (by intro i; cases i; rfl; exact h.symm)
@[simp] lemma lift_left {f : H →* A} {g : H →* B} (l : A →* K) (r : B →* K)
    (h : l.comp f=r.comp g) (a : A) : lift l r h (left f g a)=l a :=
  PushoutI.lift_of _ _ _ _
@[simp] lemma lift_right {f : H →* A} {g : H →* B} (l : A →* K) (r : B →* K)
    (h : l.comp f=r.comp g) (b : B) : lift l r h (right f g b)=r b :=
  PushoutI.lift_of _ _ _ _

lemma centralizer_right {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) (q : B)
    (hq : ∀ b : B, b*q*b⁻¹∉g.range) (x : GroupOf f g)
    (hx : Commute x (right f g q)) : x∈(right f g).range :=
  AmalgamTools.centralizer_in_factor (diagram_injective hf hg) true q hq x hx
end ArtinCAT0.BinaryAmalgam

namespace ArtinCAT0.FreeTwo
open Monoid
abbrev Cyclic := Multiplicative ℤ
def maps (_ : Bool) : PUnit →* Cyclic := 1
abbrev GroupOf := PushoutI maps
def gen (i : Bool) : GroupOf := PushoutI.of i (Multiplicative.ofAdd (1 : ℤ))
lemma maps_injective (i : Bool) : Function.Injective (maps i) := fun _ _ _ => Subsingleton.elim _ _
lemma gen_ne_one (i : Bool) : gen i≠1 := by
  intro h
  have he := PushoutI.of_injective maps_injective i (h.trans (map_one _).symm)
  change Multiplicative.ofAdd (1 : ℤ)=Multiplicative.ofAdd 0 at he
  exact Int.one_ne_zero (Multiplicative.ofAdd.injective he)

def lift {K : Type*} [Group K] (q : Bool→K) : GroupOf →* K :=
  PushoutI.lift (fun i => zpowersHom K (q i)) 1 (by
    intro i
    ext x
    simp [maps])
@[simp] lemma lift_gen {K : Type*} [Group K] (q : Bool→K) (i : Bool) :
    lift q (gen i)=q i := by simp [lift,gen,zpowersHom_apply]

lemma common_centralizer (x : GroupOf) (hx : ∀ i, Commute x (gen i)) : x=1 := by
  have hmem (i : Bool) : x∈(PushoutI.of (φ:=maps) i).range := by
    apply AmalgamTools.centralizer_in_factor maps_injective i _ _ x (hx i)
    intro b
    rintro ⟨y,hy⟩
    have he : (1:ℤ)=0 := by
      have hh : Multiplicative.ofAdd (1:ℤ)=(1:Cyclic) := by
        simpa [maps,mul_comm,mul_left_comm] using hy.symm
      exact Multiplicative.ofAdd.injective hh
    exact Int.one_ne_zero he
  have hboth : x∈(PushoutI.of (φ:=maps) false).range ⊓ (PushoutI.of (φ:=maps) true).range :=
    ⟨hmem false,hmem true⟩
  rw [PushoutI.inf_of_range_eq_base_range maps_injective Bool.false_ne_true] at hboth
  obtain ⟨y,rfl⟩ := hboth
  have hy : y=1 := Subsingleton.elim _ _
  rw [hy,map_one]
end ArtinCAT0.FreeTwo
open scoped Classical
namespace ArtinCAT0

lemma blockLetter_injective (b : Fin 3) : Function.Injective (blockLetter b) := by
  intro i j he
  unfold blockLetter at he
  split_ifs at he <;> simp only [Fin.mk.injEq] at he <;> apply Fin.ext <;> omega

lemma blockLetter_private {b c : Fin 3} {i j : Fin 39} (hi : 2 ≤ i.val)
    (he : blockLetter b i=blockLetter c j) : b=c ∧ i=j := by
  unfold blockLetter at he
  split_ifs at he <;> simp only [Fin.mk.injEq] at he
  all_goals try omega

lemma blockLetter_nonsentinel (b : Fin 3) (i : Fin 39) :
    (blockLetter b i).val≠3 ∧ (blockLetter b i).val≠4 := by
  unfold blockLetter
  split_ifs <;> dsimp <;> omega

lemma adjacent_symm {s t : Letters} (h : Adjacent s t) : Adjacent t s := by
  obtain ⟨b,i,j,rfl,rfl,h⟩ := h
  exact ⟨b,j,i,rfl,rfl,h.symm⟩
lemma distant_symm {s t : Letters} (h : Distant s t) : Distant t s := by
  obtain ⟨b,i,j,rfl,rfl,h⟩ := h
  exact ⟨b,j,i,rfl,rfl,h.symm⟩
lemma sentinel_symm {s t : Letters} (h : Sentinel s t) : Sentinel t s := h.symm

lemma adjacent_not_distant {s t : Letters} (ha : Adjacent s t) : ¬Distant s t := by
  obtain ⟨b,i,j,rfl,rfl,hij⟩ := ha
  rintro ⟨c,k,l,hik,hjl,hkl⟩
  have hc : b=c := by
    rcases hkl with hkl|hlk
    · have hh := blockLetter_private (j:=j) (by omega : 2 ≤ l.val) hjl.symm
      exact hh.1.symm
    · have hh := blockLetter_private (j:=i) (by omega : 2 ≤ k.val) hik.symm
      exact hh.1.symm
  subst c
  have hik' := blockLetter_injective b hik
  have hjl' := blockLetter_injective b hjl
  subst k; subst l
  omega

lemma sentinel_not_adjacent {s t : Letters} (hs : Sentinel s t) : ¬Adjacent s t := by
  rintro ⟨b,i,j,rfl,rfl,_⟩
  have hi := blockLetter_nonsentinel b i
  have hj := blockLetter_nonsentinel b j
  rcases hs with ⟨h,_⟩|⟨h,_⟩ <;> omega

lemma explicitMatrix_symmetric (s t : Letters) : explicitMatrix s t=explicitMatrix t s := by
  have ha : Adjacent s t ↔ Adjacent t s := ⟨adjacent_symm,adjacent_symm⟩
  have hd : Distant s t ↔ Distant t s := ⟨distant_symm,distant_symm⟩
  have hs : Sentinel s t ↔ Sentinel t s := ⟨sentinel_symm,sentinel_symm⟩
  simp only [explicitMatrix,eq_comm,ha,hd,hs]

@[simp] lemma explicitMatrix_diagonal (s : Letters) : explicitMatrix s s=1 := by
  simp [explicitMatrix]

lemma explicitMatrix_values (s t : Letters) (h : s≠t) :
    explicitMatrix s t=2 ∨ explicitMatrix s t=3 ∨ explicitMatrix s t=⊤ := by
  unfold explicitMatrix
  simp only [ite_eq_right h]
  split_ifs <;> simp

lemma matrix_block_adjacent (b : Fin 3) (i j : Fin 39)
    (hij : i.val+1=j.val ∨ j.val+1=i.val) :
    explicitMatrix (blockLetter b i) (blockLetter b j)=3 := by
  have he : blockLetter b i≠blockLetter b j := fun he => by
    have := blockLetter_injective b he
    subst j
    omega
  have ha : Adjacent (blockLetter b i) (blockLetter b j) := ⟨b,i,j,rfl,rfl,hij⟩
  simp [explicitMatrix,he,ha]

lemma matrix_block_distant (b : Fin 3) (i j : Fin 39)
    (hij : i.val+2 ≤ j.val ∨ j.val+2 ≤ i.val) :
    explicitMatrix (blockLetter b i) (blockLetter b j)=2 := by
  have he : blockLetter b i≠blockLetter b j := fun he => by
    have := blockLetter_injective b he
    subst j
    omega
  have hd : Distant (blockLetter b i) (blockLetter b j) := ⟨b,i,j,rfl,rfl,hij⟩
  have hn : ¬Adjacent (blockLetter b i) (blockLetter b j) := fun ha => adjacent_not_distant ha hd
  simp [explicitMatrix,he,hn,hd]

lemma matrix_sentinel (s t : Letters) (hs : Sentinel s t) : explicitMatrix s t=2 := by
  have he : s≠t := by rintro rfl; rcases hs with ⟨h,ht⟩|⟨h,ht⟩ <;> omega
  simp [explicitMatrix,he,sentinel_not_adjacent hs,hs]

abbrev MainGroup := ArtinGroup explicitMatrix
abbrev mainGen (s : Letters) : MainGroup := PresentedGroup.of s

lemma artin_braid {S : Type*} (M : S→S→Label) (s t : S) (h : M s t=3) :
    PresentedGroup.of (rels:=artinRelators M) s * PresentedGroup.of t * PresentedGroup.of s =
      PresentedGroup.of t * PresentedGroup.of s * PresentedGroup.of t := by
  have hh := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels:=artinRelators M) ⟨s,t,3,h,rfl⟩
  simpa [alternating,PresentedGroup.of,map_mul,mul_assoc] using hh

lemma artin_commute {S : Type*} (M : S→S→Label) (s t : S) (h : M s t=2) :
    Commute (PresentedGroup.of (rels:=artinRelators M) s) (PresentedGroup.of t) := by
  have hh := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels:=artinRelators M) ⟨s,t,2,h,rfl⟩
  simpa [alternating,PresentedGroup.of,map_mul,Commute,SemiconjBy] using hh

section Lift
variable {H : Type*} [Group H]

def mainLift (v : Letters → H)
    (hb : ∀ s t, Adjacent s t → v s*v t*v s=v t*v s*v t)
    (hc : ∀ s t, Distant s t ∨ Sentinel s t → Commute (v s) (v t)) : MainGroup →* H :=
  PresentedGroup.toGroup (f:=v) (by
    rintro r ⟨s,t,n,hn,rfl⟩
    simp only [map_mul,map_inv,mul_inv_eq_one]
    unfold explicitMatrix at hn
    split_ifs at hn with he ha hd
    · have hn' : n=1 := by exact_mod_cast hn.symm
      subst n; subst t
      rfl
    · have hn' : n=3 := by exact_mod_cast hn.symm
      subst n
      simpa [alternating,map_mul,mul_assoc] using hb s t ha
    · have hn' : n=2 := by exact_mod_cast hn.symm
      subst n
      simpa [alternating,map_mul] using (hc s t hd).eq
    · exact False.elim (WithTop.top_ne_coe hn))

@[simp] lemma mainLift_gen (v : Letters → H) (hb hc) (s : Letters) :
    mainLift v hb hc (mainGen s)=v s := PresentedGroup.toGroup.of _

end Lift
end ArtinCAT0
open scoped Classical
namespace ArtinCAT0.Assembly
open BinaryAmalgam

abbrev inc := initialBraidInclusion 39 (by norm_num)
abbrev A₁ := GroupOf (trianglePair 0) inc
def t₁ : TriangleGroup →* A₁ := left (trianglePair 0) inc
abbrev A₂ := GroupOf (t₁.comp (trianglePair 1)) inc
def t₂ : TriangleGroup →* A₂ := (left (t₁.comp (trianglePair 1)) inc).comp t₁
abbrev A₃ := GroupOf (t₂.comp (trianglePair 2)) inc
def t₃ : TriangleGroup →* A₃ := (left (t₂.comp (trianglePair 2)) inc).comp t₂

lemma inc_injective : Function.Injective inc := initialBraidInclusion_injective 39 (by norm_num)
lemma t₁_injective : Function.Injective t₁ := left_injective (trianglePair_injective 0) inc_injective
lemma t₂_injective : Function.Injective t₂ := by
  intro a b h
  apply t₁_injective
  exact left_injective (f:=t₁.comp (trianglePair 1)) (g:=inc)
    (t₁_injective.comp (trianglePair_injective 1)) inc_injective h
lemma t₃_injective : Function.Injective t₃ := by
  intro a b h
  apply t₂_injective
  exact left_injective (f:=t₂.comp (trianglePair 2)) (g:=inc)
    (t₂_injective.comp (trianglePair_injective 2)) inc_injective h

def block₀ : BraidGroup 39 →* A₃ :=
  (left (t₂.comp (trianglePair 2)) inc).comp
    ((left (t₁.comp (trianglePair 1)) inc).comp (right (trianglePair 0) inc))
def block₁ : BraidGroup 39 →* A₃ :=
  (left (t₂.comp (trianglePair 2)) inc).comp (right (t₁.comp (trianglePair 1)) inc)
def block₂ : BraidGroup 39 →* A₃ := right (t₂.comp (trianglePair 2)) inc

def block (b : Fin 3) : BraidGroup 39 →* A₃ := ![block₀,block₁,block₂] b
lemma block_agree (b : Fin 3) : (block b).comp inc=t₃.comp (trianglePair b) := by
  apply MonoidHom.ext
  intro x
  fin_cases b
  · exact congrArg (fun y : A₁ => left (t₂.comp (trianglePair 2)) inc
      (left (t₁.comp (trianglePair 1)) inc y))
      (DFunLike.congr_fun (agree (trianglePair 0) inc) x).symm
  · exact congrArg (left (t₂.comp (trianglePair 2)) inc)
      (DFunLike.congr_fun (agree (t₁.comp (trianglePair 1)) inc) x).symm
  · exact (DFunLike.congr_fun (agree (t₂.comp (trianglePair 2)) inc) x).symm

abbrev Product := TriangleGroup × FreeTwo.GroupOf
def productT : TriangleGroup →* Product := (MonoidHom.id _).prod 1
lemma productT_injective : Function.Injective productT := by
  intro a b h
  exact congrArg Prod.fst h
abbrev Model := GroupOf t₃ productT
def triangle : TriangleGroup →* Model := (left t₃ productT).comp t₃
def braidBlock (b : Fin 3) : BraidGroup 39 →* Model := (left t₃ productT).comp (block b)
def sentinel (i : Bool) : Model := right t₃ productT (1,FreeTwo.gen i)
lemma triangle_injective : Function.Injective triangle :=
  (left_injective t₃_injective productT_injective).comp t₃_injective
lemma triangle_eq_right : triangle=(right t₃ productT).comp productT := agree _ _
lemma braidBlock_agree (b : Fin 3) : (braidBlock b).comp inc=triangle.comp (trianglePair b) := by
  simp only [braidBlock,triangle,MonoidHom.comp_assoc,block_agree]

lemma product_conjugate_not_base (i : Bool) (b : Product) :
    b*(1,FreeTwo.gen i)*b⁻¹∉productT.range := by
  rintro ⟨a,ha⟩
  have he : b.2*FreeTwo.gen i*b.2⁻¹=1 := (congrArg Prod.snd ha).symm
  have hh : FreeTwo.gen i=1 := by
    have := congrArg (fun x => b.2⁻¹*x*b.2) he
    simpa [mul_assoc] using this
  exact FreeTwo.gen_ne_one i hh

lemma common_centralizer (g : Model) (hg : ∀ i, Commute g (sentinel i)) : g∈triangle.range := by
  obtain ⟨b,rfl⟩ := centralizer_right t₃_injective productT_injective (1,FreeTwo.gen false)
    (product_conjugate_not_base false) g (hg false)
  have hb (i : Bool) : Commute b (1,FreeTwo.gen i) := by
    apply (right_injective t₃_injective productT_injective)
    simpa only [map_mul,sentinel] using (hg i).eq
  have hf : b.2=1 := FreeTwo.common_centralizer b.2 (fun i => (hb i).map (MonoidHom.snd _ _))
  refine ⟨b.1,?_⟩
  rw [triangle_eq_right]
  change right t₃ productT (b.1,1)=right t₃ productT b
  rw [← hf]

def corner (i : Fin 3) : Letters := ⟨i.val,by omega⟩
@[simp] lemma blockLetter_zero (b : Fin 3) : blockLetter b 0=corner b := by
  simp [blockLetter,corner]
@[simp] lemma blockLetter_one (b : Fin 3) : blockLetter b 1=corner (b+1) := by
  apply Fin.ext
  simp [blockLetter,corner,Fin.add_def]

lemma braidBlock_zero (b : Fin 3) : braidBlock b (braidGen 39 0)=triangle (triangleGen b) := by
  have h := DFunLike.congr_fun (braidBlock_agree b) (braidGen 2 0)
  simpa [inc,initialBraidInclusion,trianglePair,braidGen] using h
lemma braidBlock_one (b : Fin 3) : braidBlock b (braidGen 39 1)=triangle (triangleGen (b+1)) := by
  have h := DFunLike.congr_fun (braidBlock_agree b) (braidGen 2 1)
  simpa [inc,initialBraidInclusion,trianglePair,braidGen] using h

def letter (s : Letters) : Model :=
  if hs : s.val<3 then triangle (triangleGen ⟨s.val,hs⟩)
  else if s.val=3 then sentinel false
  else if s.val=4 then sentinel true
  else braidBlock ⟨(s.val-5)/37,by omega⟩ (braidGen 39 ((s.val-5)%37+2))
@[simp] lemma letter_corner (i : Fin 3) : letter (corner i)=triangle (triangleGen i) := by
  simp [letter,corner,i.isLt]
@[simp] lemma letter_three : letter 3=sentinel false := by simp [letter]
@[simp] lemma letter_four : letter 4=sentinel true := by simp [letter]
lemma letter_block (b : Fin 3) (i : Fin 39) : letter (blockLetter b i)=braidBlock b (braidGen 39 i.val) := by
  rcases lt_or_ge i.val 2 with hi|hi
  · have he : i=0 ∨ i=1 := by omega
    rcases he with rfl|rfl
    · simpa only [Fin.val_zero,blockLetter_zero,letter_corner] using (braidBlock_zero b).symm
    · simpa only [Fin.val_one,blockLetter_one,letter_corner] using (braidBlock_one b).symm
  · have h₀ : i.val≠0 := by omega
    have h₁ : i.val≠1 := by omega
    have hs : (blockLetter b i).val=5+37*b.val+(i.val-2) := by simp [blockLetter,h₀,h₁]
    have hsmall : ¬(blockLetter b i).val<3 := by omega
    have h3 : (blockLetter b i).val≠3 := by omega
    have h4 : (blockLetter b i).val≠4 := by omega
    have hb : ((blockLetter b i).val-5)/37=b.val := by omega
    have hj : ((blockLetter b i).val-5)%37+2=i.val := by omega
    simp only [letter,dite_eq_right hsmall,ite_eq_right h3,ite_eq_right h4,hj]
    congr 2
    exact Fin.ext hb

lemma letter_braid (s t : Letters) (h : Adjacent s t) :
    letter s*letter t*letter s=letter t*letter s*letter t := by
  obtain ⟨b,i,j,rfl,rfl,h⟩ := h
  rw [letter_block,letter_block]
  rcases h with h|h
  · have he := congrArg (braidBlock b) (braidGroup_relation 39 i.val (by omega))
    simpa only [map_mul,h] using he
  · have he := congrArg (braidBlock b) (braidGroup_relation 39 j.val (by omega))
    simpa only [map_mul,h] using he.symm

lemma triangle_sentinel_commute (t : TriangleGroup) (i : Bool) : Commute (triangle t) (sentinel i) := by
  rw [triangle_eq_right]
  apply Commute.map (f:=right t₃ productT)
  change Commute (t,1) (1,FreeTwo.gen i)
  change (t,1)*(1,FreeTwo.gen i)=(1,FreeTwo.gen i)*(t,1)
  simp

lemma letter_commute (s t : Letters) (h : Distant s t ∨ Sentinel s t) : Commute (letter s) (letter t) := by
  rcases h with h|h
  · obtain ⟨b,i,j,rfl,rfl,h⟩ := h
    rw [letter_block,letter_block]
    rcases h with h|h
    · exact (braidGroup_commute 39 i.val j.val h j.isLt).map (braidBlock b)
    · exact ((braidGroup_commute 39 j.val i.val h i.isLt).map (braidBlock b)).symm
  · have hh (s t : Letters) (hs : s.val=3 ∨ s.val=4) (ht : t.val<3) :
        Commute (letter s) (letter t) := by
      have ht' : t=corner ⟨t.val,ht⟩ := rfl
      rw [ht',letter_corner]
      rcases hs with hs|hs
      · have hs' : s=3 := Fin.ext hs
        rw [hs',letter_three]
        exact (triangle_sentinel_commute _ _).symm
      · have hs' : s=4 := Fin.ext hs
        rw [hs',letter_four]
        exact (triangle_sentinel_commute _ _).symm
    rcases h with ⟨hs,ht⟩|⟨ht,hs⟩
    · exact hh s t hs ht
    · exact (hh t s ht hs).symm

def toModel : MainGroup →* Model := mainLift letter letter_braid letter_commute
@[simp] lemma toModel_gen (s : Letters) : toModel (mainGen s)=letter s := mainLift_gen _ _ _ _

def triangleMain : TriangleGroup →* MainGroup := triangleLift (fun i => mainGen (corner i)) (by
  intro i
  have h := matrix_block_adjacent i 0 1 (by decide)
  rw [blockLetter_zero,blockLetter_one] at h
  exact artin_braid _ _ _ h)
@[simp] lemma triangleMain_gen (i : Fin 3) : triangleMain (triangleGen i)=mainGen (corner i) :=
  triangleLift_gen _ _ _

def blockMain (b : Fin 3) : BraidGroup 39 →* MainGroup := braidLift (fun i => mainGen (blockLetter b i))
  (fun i hi => artin_braid _ _ _ (matrix_block_adjacent b ⟨i,by omega⟩ ⟨i+1,hi⟩ (Or.inl rfl)))
  (fun i j hij => artin_commute _ _ _ (matrix_block_distant b i j (Or.inl hij)))
@[simp] lemma blockMain_gen (b : Fin 3) (i : ℕ) (hi : i<39) :
    blockMain b (braidGen 39 i)=mainGen (blockLetter b ⟨i,hi⟩) := braidLift_gen _ _ _ _ hi
lemma blockMain_agree (b : Fin 3) : (blockMain b).comp inc=triangleMain.comp (trianglePair b) := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp [inc,initialBraidInclusion,trianglePair,braidGen,blockMain]

def sentinelMain (i : Bool) : MainGroup := if i then mainGen 4 else mainGen 3
lemma triangleMain_commute (t : TriangleGroup) : ∀ i, Commute (triangleMain t) (sentinelMain i) := by
  let C := (tupleCentralizer sentinelMain).comap triangleMain
  have hgen (k : Fin 3) : PresentedGroup.of (rels:=triangleRelators) k∈C := by
    change ∀ i, Commute (triangleMain (triangleGen k)) (sentinelMain i)
    intro i
    rw [triangleMain_gen]
    cases i
    · exact artin_commute _ _ _ (matrix_sentinel _ _ (Or.inr ⟨Or.inl rfl,k.isLt⟩))
    · exact artin_commute _ _ _ (matrix_sentinel _ _ (Or.inr ⟨Or.inr rfl,k.isLt⟩))
  exact PresentedGroup.generated_by triangleRelators C hgen t

def freeMain : FreeTwo.GroupOf →* MainGroup := FreeTwo.lift sentinelMain
@[simp] lemma freeMain_gen (i : Bool) : freeMain (FreeTwo.gen i)=sentinelMain i := FreeTwo.lift_gen _ _
lemma factors_commute (t : TriangleGroup) (f : FreeTwo.GroupOf) : Commute (triangleMain t) (freeMain f) := by
  apply Monoid.PushoutI.induction_on f
  · intro i g
    simpa [freeMain,FreeTwo.lift,zpowersHom_apply] using (triangleMain_commute t i).zpow_right g.toAdd
  · intro g
    simp [freeMain,FreeTwo.lift]
  · intro a b ha hb
    simpa only [map_mul] using ha.mul_right hb

def productMain : Product →* MainGroup := triangleMain.noncommCoprod freeMain factors_commute
@[simp] lemma productMain_apply (t : TriangleGroup) (f : FreeTwo.GroupOf) :
    productMain (t,f)=triangleMain t*freeMain f := rfl
lemma productMain_triangle : productMain.comp productT=triangleMain := by
  apply MonoidHom.ext
  intro x
  simp [productT]

def back₁ : A₁ →* MainGroup := lift triangleMain (blockMain 0) (blockMain_agree 0).symm
lemma back₁_triangle : back₁.comp t₁=triangleMain := by
  apply MonoidHom.ext
  intro x
  simp [back₁,t₁]
def back₂ : A₂ →* MainGroup := lift back₁ (blockMain 1) (by
  rw [← MonoidHom.comp_assoc,back₁_triangle]
  exact (blockMain_agree 1).symm)
lemma back₂_triangle : back₂.comp t₂=triangleMain := by
  apply MonoidHom.ext
  intro x
  change back₂ (left (t₁.comp (trianglePair 1)) inc (t₁ x))=triangleMain x
  rw [back₂,lift_left]
  exact DFunLike.congr_fun back₁_triangle x
def back₃ : A₃ →* MainGroup := lift back₂ (blockMain 2) (by
  rw [← MonoidHom.comp_assoc,back₂_triangle]
  exact (blockMain_agree 2).symm)
lemma back₃_triangle : back₃.comp t₃=triangleMain := by
  apply MonoidHom.ext
  intro x
  change back₃ (left (t₂.comp (trianglePair 2)) inc (t₂ x))=triangleMain x
  rw [back₃,lift_left]
  exact DFunLike.congr_fun back₂_triangle x
lemma back₃_block (b : Fin 3) : back₃.comp (block b)=blockMain b := by
  apply MonoidHom.ext
  intro x
  fin_cases b <;> simp [block,block₀,block₁,block₂,back₃,back₂,back₁]

def fromModel : Model →* MainGroup := lift back₃ productMain (by
  rw [back₃_triangle,productMain_triangle])
lemma fromModel_triangle : fromModel.comp triangle=triangleMain := by
  apply MonoidHom.ext
  intro x
  simp only [triangle,MonoidHom.comp_apply,fromModel,lift_left]
  exact DFunLike.congr_fun back₃_triangle x
lemma fromModel_block (b : Fin 3) : fromModel.comp (braidBlock b)=blockMain b := by
  apply MonoidHom.ext
  intro x
  simp only [braidBlock,MonoidHom.comp_apply,fromModel,lift_left]
  exact DFunLike.congr_fun (back₃_block b) x
@[simp] lemma fromModel_sentinel (i : Bool) : fromModel (sentinel i)=sentinelMain i := by
  simp [fromModel,sentinel]

lemma letter_cover (s : Letters) : s=3 ∨ s=4 ∨ ∃ b i, s=blockLetter b i := by
  by_cases h3 : s=3
  · exact Or.inl h3
  by_cases h4 : s=4
  · exact Or.inr (Or.inl h4)
  right; right
  by_cases hs : s.val<3
  · exact ⟨⟨s.val,hs⟩,0,by rw [blockLetter_zero]; rfl⟩
  have hval : 5 ≤ s.val := by
    have hh3 : s.val≠3 := fun h => h3 (Fin.ext h)
    have hh4 : s.val≠4 := fun h => h4 (Fin.ext h)
    omega
  refine ⟨⟨(s.val-5)/37,by omega⟩,⟨(s.val-5)%37+2,by omega⟩,?_⟩
  apply Fin.ext
  simp only [blockLetter]
  split_ifs <;> dsimp at * <;> omega

lemma fromModel_letter (s : Letters) : fromModel (letter s)=mainGen s := by
  rcases letter_cover s with rfl|rfl|⟨b,i,rfl⟩
  · simp [sentinelMain]
  · simp [sentinelMain]
  · rw [letter_block]
    change (fromModel.comp (braidBlock b)) (braidGen 39 i.val)=_
    rw [fromModel_block,blockMain_gen b i.val i.isLt]
lemma fromModel_toModel : fromModel.comp toModel=MonoidHom.id MainGroup := by
  apply PresentedGroup.ext
  intro s
  change fromModel (toModel (mainGen s))=mainGen s
  rw [toModel_gen,fromModel_letter]
lemma toModel_injective : Function.Injective toModel := by
  apply Function.Injective.of_comp (f:=fromModel)
  rw [← MonoidHom.coe_comp,fromModel_toModel]
  exact Function.injective_id
lemma toModel_triangleMain : toModel.comp triangleMain=triangle := by
  apply PresentedGroup.ext
  intro i
  change toModel (triangleMain (triangleGen i))=triangle (triangleGen i)
  rw [triangleMain_gen,toModel_gen,letter_corner]
lemma triangleMain_injective : Function.Injective triangleMain := by
  apply Function.Injective.of_comp (f:=toModel)
  rw [← MonoidHom.coe_comp,toModel_triangleMain]
  exact triangle_injective
@[simp] lemma toModel_sentinelMain (i : Bool) : toModel (sentinelMain i)=sentinel i := by
  cases i <;> simp [sentinelMain]
lemma main_common_centralizer (g : MainGroup) (hg : ∀ i, Commute g (sentinelMain i)) : g∈triangleMain.range := by
  have hh (i : Bool) : Commute (toModel g) (sentinel i) := by
    simpa only [toModel_sentinelMain] using (hg i).map toModel
  obtain ⟨t,ht⟩ := common_centralizer (toModel g) hh
  refine ⟨t,?_⟩
  apply toModel_injective
  change (toModel.comp triangleMain) t=toModel g
  rw [toModel_triangleMain]
  exact ht

def triangleCentralizer : TriangleGroup →* tupleCentralizer sentinelMain :=
  triangleMain.codRestrict _ triangleMain_commute
lemma triangleCentralizer_bijective : Function.Bijective triangleCentralizer := by
  constructor
  · intro a b h
    apply triangleMain_injective
    exact congrArg Subtype.val h
  · intro g
    obtain ⟨t,ht⟩ := main_common_centralizer g.val g.property
    exact ⟨t,Subtype.ext ht⟩
end ArtinCAT0.Assembly
namespace ArtinCAT0
variable {G H X : Type*} [Group G] [Group H] [MetricSpace X] [MulAction G X]

lemma geometric_compHom (f : H →* G) (hf : Function.Bijective f) (hG : GeometricAction G X) :
    let := MulAction.compHom X f
    GeometricAction H X := by
  let := MulAction.compHom X f
  refine ⟨hG.1,fun h => hG.2.1 (f h),?_,?_⟩
  · intro K hK
    change (f ⁻¹' {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}).Finite
    exact (hG.2.2.1 K hK).preimage (fun _ _ _ _ h => hf.1 h)
  · obtain ⟨K,hK,hcov⟩ := hG.2.2.2
    refine ⟨K,hK,?_⟩
    intro x
    obtain ⟨g,k,hk,hgk⟩ := hcov x
    obtain ⟨h,rfl⟩ := hf.2 g
    exact ⟨h,k,hk,hgk⟩

lemma stableLength_compHom (f : H →* G) (x : X) (h : H) :
    let := MulAction.compHom X f
    stableLengthAt x h=stableLengthAt x (f h) := by
  let := MulAction.compHom X f
  simp only [stableLengthAt,MulAction.compHom_smul_def,map_pow]

lemma generator_square_positive [ProperSpace X] [Nonempty X]
    {S : Type*} (M : S→S→Label) [MulAction (ArtinGroup M) X]
    (hG : GeometricAction (ArtinGroup M) X) (x : X) (s : S) :
    0<stableLengthAt x ((PresentedGroup.of (rels:=artinRelators M) s)^2) := by
  have hp : 0<stableLengthAt x (PresentedGroup.of (rels:=artinRelators M) s) := by
    apply lt_of_le_of_ne (stableLength_nonneg hG.2.1 x _)
    intro h
    exact artin_generator_infinite_order M s ((stableLength_eq_zero_iff_finiteOrder hG x _).mp h.symm)
  rw [stableLength_pow hG.2.1]
  positivity
end ArtinCAT0

end OAI
