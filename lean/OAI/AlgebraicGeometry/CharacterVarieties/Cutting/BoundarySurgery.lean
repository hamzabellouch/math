import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.StripFacets

namespace OAI

/-!
# Boundary circuits and their noncommutative words under finite splicing.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortWiring
open scoped Classical
open VertexTable
variable {V : Type} {kind : V → Kind} (W : PortWiring kind)
    (C : Equiv.Perm W.Seam) (hC : ∀ s,W.seamArity (C s)=W.seamArity s)

def parentSurgery : Equiv.Perm (Side W.Seam W.seamArity) :=
  W.entryAction C.symm (Equiv.refl _) (fun _=>rfl)
def childSurgery : Equiv.Perm (Side W.Seam W.seamArity) :=
  W.entryAction (Equiv.refl _) C hC

lemma positiveRelabel_child (a : Side W.Seam W.seamArity) :
    W.positiveRelabel C hC (W.childSurgery C hC a)=a := by
  rcases a with ⟨s,c⟩
  cases c with
  | none => rfl
  | some i =>
    apply sideNumber_injective
    change (C.symm (C s),some i.val)=(s,some i.val)
    rw [Equiv.symm_apply_apply]
lemma positiveRelabel_cut (a : Side W.Seam W.seamArity) :
    W.positiveRelabel C hC (W.cutAction C hC a)=W.parentSurgery C a := by
  rcases a with ⟨s,c⟩
  cases c with
  | none => rfl
  | some i =>
    apply sideNumber_injective
    change (C.symm (C s),some i.val)=(s,some i.val)
    rw [Equiv.symm_apply_apply]

/-- Actual successor in UNCHANGED positive-port side coordinates. Parents
are postcomposed and children are precomposed. Omitting this distinction
incorrectly assigns the old child monodromy to a new identity short side. -/
lemma rewire_boundary_unchanged (a : Side W.Seam W.seamArity) :
    ((W.rewire C hC).assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext a=
      W.parentSurgery C (((W.assemble (fun _ => ()) (fun _=>rfl)).vertexAssembly.corners.boundaryNext)
        (W.childSurgery C hC a)) := by
  have h := W.rewire_boundary C hC (W.childSurgery C hC a)
  rw [W.positiveRelabel_child,W.positiveRelabel_cut] at h
  exact h

lemma parentSurgery_number (a : Side W.Seam W.seamArity) :
    sideNumber (W.parentSurgery C a)=
      (if a.2.isNone then C.symm a.1 else a.1,a.2.map Fin.val) := by
  rcases a with ⟨s,c⟩
  cases c <;> rfl
lemma childSurgery_number (a : Side W.Seam W.seamArity) :
    sideNumber (W.childSurgery C hC a)=
      (if a.2.isNone then a.1 else C a.1,a.2.map Fin.val) := by
  rcases a with ⟨s,c⟩
  cases c <;> rfl

lemma parentSurgery_fixed (a : Side W.Seam W.seamArity)
    (ha : a.2=none → C a.1=a.1) : W.parentSurgery C a=a := by
  rcases a with ⟨s,c⟩
  cases c with
  | none =>
    have he : C.symm s=s := C.injective (by rw [Equiv.apply_symm_apply,ha rfl])
    change (⟨C.symm s,none⟩ : Side W.Seam W.seamArity)=⟨s,none⟩
    rw [he]
  | some i => rfl
end IntegralCharacterVarieties.OccurrenceIncidence.PortWiring

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α ι : Type}
noncomputable def pairSwap (e : (ι × Bool) ↪ α) (i : ι) : Equiv.Perm α :=
  Equiv.swap (e (i,false)) (e (i,true))

lemma pairSwap_same (e : (ι × Bool) ↪ α) (i : ι) (b : Bool) :
    pairSwap e i (e (i,b))=e (i,!b) := by
  cases b <;> simp [pairSwap]

lemma pairSwap_other (e : (ι × Bool) ↪ α) (i j : ι) (h : j≠i) (b : Bool) :
    pairSwap e i (e (j,b))=e (j,b) := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun he => h (congrArg Prod.fst (e.injective he))
  · exact fun he => h (congrArg Prod.fst (e.injective he))

lemma pairSwap_product (e : (ι × Bool) ↪ α) (is : List ι) (hi : is.Nodup)
    (j : ι) (b : Bool) :
    (is.map (pairSwap e)).prod (e (j,b))=e (j,if j∈is then !b else b) := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hn := List.nodup_cons.mp hi
    rw [List.map_cons,List.prod_cons,mul_apply,ih hn.2]
    by_cases h : j=i
    · subst j
      simp only [hn.1,ite_false,List.mem_cons_self,ite_true]
      exact pairSwap_same e i b
    · rw [pairSwap_other e i j h]
      have he : j∈i::is ↔ j∈is := by simp [h]
      simp only [he]

lemma pairSwap_product_away (e : (ι × Bool) ↪ α) (is : List ι)
    (a : α) (ha : ∀ i∈is,∀ b,a≠e (i,b)) :
    (is.map (pairSwap e)).prod a=a := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [List.map_cons,List.prod_cons,mul_apply,ih (fun j hj => ha j (List.mem_cons_of_mem i hj))]
    exact Equiv.swap_apply_of_ne_of_ne (ha i List.mem_cons_self false) (ha i List.mem_cons_self true)
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.PortWiring
open scoped Classical
open VertexTable IntegralCharacterVarieties.BoundarySurgery
variable {V : Type} {k : V → Kind} (W : PortWiring k)

def childPair (s t : W.Seam) (hst : s≠t) (ht : W.seamArity t=W.seamArity s) :
    (Fin (W.seamArity s) × Bool) ↪ Side W.Seam W.seamArity where
  toFun z := match z.2 with
    | false => ⟨s,some z.1⟩
    | true => ⟨t,some (finCongr ht.symm z.1)⟩
  inj' := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    cases b <;> cases c
    · have z := congrArg sideNumber h
      exact Prod.ext (Fin.ext (Option.some.inj (congrArg Prod.snd z))) rfl
    · exact False.elim (hst (congrArg Sigma.fst h))
    · exact False.elim (hst (congrArg Sigma.fst h).symm)
    · have z := congrArg sideNumber h
      exact Prod.ext (Fin.ext (Option.some.inj (congrArg Prod.snd z))) rfl

lemma swap_arity (s t : W.Seam) (ht : W.seamArity t=W.seamArity s) :
    ∀ r,W.seamArity (Equiv.swap s t r)=W.seamArity r := by
  intro r
  by_cases hs : r=s
  · subst r
    simpa using ht
  by_cases hr : r=t
  · subst r
    simpa using ht.symm
  rw [Equiv.swap_apply_of_ne_of_ne hs hr]

lemma childPair_number (s t : W.Seam) (hst : s≠t) (ht : W.seamArity t=W.seamArity s)
    (i : Fin (W.seamArity s)) (b : Bool) :
    sideNumber (W.childPair s t hst ht (i,b))=(if b then t else s,some i.val) := by
  cases b <;> rfl

lemma childSurgery_swap (s t : W.Seam) (hst : s≠t) (ht : W.seamArity t=W.seamArity s) :
    W.childSurgery (Equiv.swap s t) (W.swap_arity s t ht)=
      ((List.finRange (W.seamArity s)).map (pairSwap (W.childPair s t hst ht))).prod := by
  apply Equiv.ext
  rintro ⟨r,c⟩
  cases c with
  | none =>
    change (⟨r,none⟩ : Side W.Seam W.seamArity)=_
    symm
    apply pairSwap_product_away
    intro i hi b he
    have hz := congrArg sideNumber he
    rw [W.childPair_number] at hz
    have hz' : (none : Option ℕ)=some i.val := congrArg (fun z : W.Seam × Option ℕ => z.2) hz
    cases hz'
  | some j =>
    by_cases hs : r=s
    · subst r
      have h := pairSwap_product (W.childPair s t hst ht) (List.finRange (W.seamArity s))
        (List.nodup_finRange _) j false
      have hj : j∈List.finRange (W.seamArity s) := List.mem_finRange j
      rw [ite_eq_left hj] at h
      change _=(_ : Equiv.Perm (Side W.Seam W.seamArity)) (W.childPair s t hst ht (j,false))
      rw [h]
      apply sideNumber_injective
      rw [W.childSurgery_number,W.childPair_number]
      simp
    by_cases hr : r=t
    · subst r
      let i := finCongr ht j
      have h := pairSwap_product (W.childPair s t hst ht) (List.finRange (W.seamArity s))
        (List.nodup_finRange _) i true
      have hi : i∈List.finRange (W.seamArity s) := List.mem_finRange i
      rw [ite_eq_left hi] at h
      have he : W.childPair s t hst ht (i,true)=⟨t,some j⟩ := by
        apply sideNumber_injective
        rw [W.childPair_number]
        rfl
      rw [←he,h]
      apply sideNumber_injective
      change (Equiv.swap s t t,some j.val)=(s,some i.val)
      rw [Equiv.swap_apply_right]
      rfl
    · have ha : ((List.finRange (W.seamArity s)).map (pairSwap (W.childPair s t hst ht))).prod
          ⟨r,some j⟩=⟨r,some j⟩ := by
        apply pairSwap_product_away
        intro i hi b he
        have hz := congrArg sideNumber he
        rw [W.childPair_number] at hz
        cases b
        · exact hs (congrArg Prod.fst hz)
        · exact hr (congrArg Prod.fst hz)
      rw [ha]
      apply sideNumber_injective
      rw [W.childSurgery_number]
      simp [Equiv.swap_apply_of_ne_of_ne hs hr,sideNumber]

lemma childSurgery_mul (C D : Equiv.Perm W.Seam)
    (hC : ∀ s,W.seamArity (C s)=W.seamArity s)
    (hD : ∀ s,W.seamArity (D s)=W.seamArity s) :
    W.childSurgery (C*D) (fun s => (hC (D s)).trans (hD s))=
      W.childSurgery C hC * W.childSurgery D hD := by
  apply Equiv.ext
  rintro ⟨s,c⟩
  cases c with
  | none => rfl
  | some i =>
    apply sideNumber_injective
    rfl
end IntegralCharacterVarieties.OccurrenceIncidence.PortWiring

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α : Type} {G : Type*} [Group G]

def cycleWord (N : Equiv.Perm α) (u : α → G) (x : α) (n : ℕ) : G :=
  (((List.range n).map (fun k => u ((N^k) x))).reverse).prod

lemma cycleWord_add (N : Equiv.Perm α) (u : α → G) (x : α) (n m : ℕ) :
    cycleWord N u x (n+m)=cycleWord N u ((N^n) x) m*cycleWord N u x n := by
  unfold cycleWord
  rw [List.range_add,List.map_append,List.reverse_append,List.prod_append]
  congr 1
  rw [List.map_map]
  congr 2
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp_apply, Nat.add_comm n k,pow_add,mul_apply]

variable (N : Equiv.Perm α) (s t : Finset α) (x y : α)
    (hs : N.IsCycleOn (s : Set α)) (ht : N.IsCycleOn (t : Set α))
    (hx : x∈s) (hy : y∈t) (hdis : Disjoint s t)

include hs hx hy hdis in
lemma splice_word_prefix (u : α → G) :
    cycleWord (Equiv.swap x y*N) u x s.card=cycleWord N u x s.card := by
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro k hk
  rw [splice_pow_lt N s t x y hs hx hy hdis k (List.mem_range.mp hk)]

include hs ht hx hy hdis in
/-- Ordered boundary word under literal oriented-end splicing. The proof
retains the entire cyclic order, not only the number of boundary components. -/
lemma splice_cycleWord (u : α → G) :
    cycleWord (Equiv.swap x y*N) u x (s.card+t.card)=
      cycleWord N u y t.card*cycleWord N u x s.card := by
  rw [cycleWord_add,splice_pow_card N s t x y hs hx hy hdis,
    splice_word_prefix N s t x y hs hx hy hdis]
  have hyword := splice_word_prefix N t s y x ht hy hx hdis.symm u
  rw [Equiv.swap_comm y x] at hyword
  rw [hyword]

include hs hx in
lemma cycleWord_one_on (u : α → G) (h : ∀ z∈s,u z=1) :
    cycleWord N u x s.card=1 := by
  unfold cycleWord
  apply List.prod_eq_one
  intro v hv
  rw [List.mem_reverse] at hv
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hv
  exact h _ (hs.1.mapsTo.iterate k hx)

include hs ht hx hy hdis in
/-- A full identity-transport strip disk inserted into an old circuit leaves
its based monodromy unchanged. This is the exact full-ring word step required
by the lower-strip cut; noncommutative old coefficients remain arbitrary. -/
lemma splice_cycleWord_identity (u : α → G) (hu : ∀ z∈t,u z=1) :
    cycleWord (Equiv.swap x y*N) u x (s.card+t.card)=cycleWord N u x s.card := by
  rw [splice_cycleWord N s t x y hs ht hx hy hdis u,
    cycleWord_one_on N t y ht hy u hu,one_mul]
end IntegralCharacterVarieties.BoundarySurgery

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α : Type} {G : Type*} [Group G]

lemma cycleWord_zero (N : Equiv.Perm α) (u : α → G) (x : α) :
    cycleWord N u x 0=1 := rfl
lemma cycleWord_one (N : Equiv.Perm α) (u : α → G) (x : α) :
    cycleWord N u x 1=u x := by simp [cycleWord]

lemma preSplice_pow_shift (N : Equiv.Perm α) (x y z : α) (k : ℕ) :
    ((N*Equiv.swap x y)^k) (N z)=N (((Equiv.swap x y*N)^k) z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ',mul_apply,ih]

variable (N : Equiv.Perm α) (s t : Finset α) (x y : α)
    (hs : N.IsCycleOn (s : Set α)) (ht : N.IsCycleOn (t : Set α))
    (hx : x∈s) (hy : y∈t) (hdis : Disjoint s t)

include hs ht hx hy hdis in
lemma preSplice_isCycle : (N*Equiv.swap x y).IsCycleOn ((s∪t : Finset α) : Set α) := by
  rw [Equiv.mul_swap_eq_swap_mul]
  exact splice_isCycle N s t (N x) (N y) hs ht (hs.1.mapsTo hx) (ht.1.mapsTo hy) hdis

include hs hx hy hdis in
lemma preSplice_pow_lt (k : ℕ) (hk : k<s.card) :
    ((N*Equiv.swap x y)^k) (N x)=(N^k) (N x) := by
  rw [preSplice_pow_shift,splice_pow_lt N s t x y hs hx hy hdis k hk]
  exact congrArg (fun f : Equiv.Perm α => f x) (Commute.self_pow N k).eq

include hs hx hy hdis in
lemma preSplice_word_prefix (u : α → G) (k : ℕ) (hk : k ≤ s.card) :
    cycleWord (N*Equiv.swap x y) u (N x) k=cycleWord N u (N x) k := by
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro j hj
  rw [preSplice_pow_lt N s t x y hs hx hy hdis j (lt_of_lt_of_le (List.mem_range.mp hj) hk)]

include ht hx hy hdis in
lemma preSplice_return : ((N*Equiv.swap x y)^(t.card+1)) x=N x := by
  have hfirst : (N*Equiv.swap x y) x=N y := by simp
  rw [pow_succ,mul_apply,hfirst,preSplice_pow_shift]
  have h := splice_pow_card N t s y x ht hy hx hdis.symm
  rw [Equiv.swap_comm y x] at h
  rw [h]

include hs ht hx hy hdis in
/-- In CHILD-side coordinates the cut precomposes the old successor; the
identity strip is inserted AFTER the old weighted side. This retains the exact
based monodromy, and does not move its weight onto the new short occurrence. -/
lemma preSplice_cycleWord_identity (u : α → G) (hu : ∀ z∈t,u z=1) :
    cycleWord (N*Equiv.swap x y) u x (s.card+t.card)=cycleWord N u x s.card := by
  have hp : 0<s.card := Finset.card_pos.mpr ⟨x,hx⟩
  have hfirst : (N*Equiv.swap x y) x=N y := by simp
  have hprefix : cycleWord (N*Equiv.swap x y) u x (t.card+1)=u x := by
    rw [Nat.add_comm t.card 1,cycleWord_add,cycleWord_one]
    simp only [pow_one,hfirst]
    have hv := preSplice_word_prefix N t s y x ht hy hx hdis.symm u t.card (le_refl _)
    rw [Equiv.swap_comm y x] at hv
    rw [hv,cycleWord_one_on N t (N y) ht (ht.1.mapsTo hy) u hu,one_mul]
  have hn : s.card+t.card=(t.card+1)+(s.card-1) := by omega
  rw [hn,cycleWord_add,preSplice_return N s t x y ht hx hy hdis,hprefix,
    preSplice_word_prefix N s t x y hs hx hy hdis u (s.card-1) (by omega)]
  have hs' : s.card=1+(s.card-1) := by omega
  conv_rhs => rw [hs',cycleWord_add,cycleWord_one]
  rfl
end IntegralCharacterVarieties.BoundarySurgery

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α : Type} {G : Type*} [Group G]

lemma pow_eq_on {N M : Equiv.Perm α} {s : Set α} (hs : Set.MapsTo N s s)
    (he : Set.EqOn M N s) {x : α} (hx : x∈s) (k : ℕ) : (M^k) x=(N^k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',pow_succ',mul_apply,mul_apply,ih]
    exact he (hs.iterate k hx)

lemma isCycleOn_eqOn {N M : Equiv.Perm α} {s : Finset α}
    (hs : N.IsCycleOn (s : Set α)) (he : Set.EqOn M N (s : Set α)) :
    M.IsCycleOn (s : Set α) := by
  refine ⟨⟨?_,M.injective.injOn,?_⟩,?_⟩
  · intro z hz
    rw [he hz]
    exact hs.1.mapsTo hz
  · intro z hz
    obtain ⟨w,hw,hwz⟩ := hs.1.surjOn hz
    exact ⟨w,hw,(he hw).trans hwz⟩
  · intro x hx y hy
    obtain ⟨k,hk,heq⟩ := hs.exists_pow_eq hx hy
    exact ⟨(k : ℤ),by simpa only [zpow_natCast,pow_eq_on hs.1.mapsTo he hx k] using heq⟩

lemma preSplice_away {N : Equiv.Perm α} {t : Finset α} (ht : N.IsCycleOn (t : Set α))
    (x y : α) (hx : x∉t) (hy : y∉t) : (N*Equiv.swap x y).IsCycleOn (t : Set α) := by
  apply isCycleOn_eqOn ht
  intro z hz
  rw [mul_apply,Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => hx (h ▸ hz)
  · exact fun h => hy (h ▸ hz)

lemma cycleWord_eqOn {N M : Equiv.Perm α} {s : Set α}
    (hs : Set.MapsTo N s s) (he : Set.EqOn M N s) (u : α → G) {x : α} (hx : x∈s) (k : ℕ) :
    cycleWord M u x k=cycleWord N u x k := by
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro j hj
  rw [pow_eq_on hs he hx j]

variable (N : Equiv.Perm α) (s t v : Finset α) (x y z : α)
    (hs : N.IsCycleOn (s : Set α)) (ht : N.IsCycleOn (t : Set α))
    (hv : N.IsCycleOn (v : Set α)) (hx : x∈s) (hy : y∈t) (hz : z∈v)
    (hst : Disjoint s t) (hsv : Disjoint s v) (htv : Disjoint t v)

include hs ht hv hx hy hz hst hsv htv in
lemma tripleSplice_isCycle : (N*(Equiv.swap x z*Equiv.swap x y)).IsCycleOn
    ((s∪v∪t : Finset α) : Set α) := by
  have hxnot : x∉t := fun h => Finset.disjoint_left.mp hst hx h
  have hznot : z∉t := fun h => Finset.disjoint_left.mp htv h hz
  have hdis : Disjoint (s∪v) t := Finset.disjoint_union_left.mpr ⟨hst,htv.symm⟩
  rw [←mul_assoc]
  exact preSplice_isCycle (N*Equiv.swap x z) (s∪v) t x y
    (preSplice_isCycle N s v x z hs hv hx hz hsv)
    (preSplice_away ht x z hxnot hznot) (Finset.mem_union_left _ hx) hy hdis

include hs ht hv hx hy hz hst hsv htv in
/-- The whole three-port cut inserts BOTH distinct contacted strips. This is
not inferred from ranks, equal facet labels, or a one-strip approximation. -/
lemma tripleSplice_cycleWord_identity (u : α → G)
    (hut : ∀ a∈t,u a=1) (huv : ∀ a∈v,u a=1) :
    cycleWord (N*(Equiv.swap x z*Equiv.swap x y)) u x (s.card+v.card+t.card)=
      cycleWord N u x s.card := by
  have hxnot : x∉t := fun h => Finset.disjoint_left.mp hst hx h
  have hznot : z∉t := fun h => Finset.disjoint_left.mp htv h hz
  have hdis : Disjoint (s∪v) t := Finset.disjoint_union_left.mpr ⟨hst,htv.symm⟩
  have hcard : (s∪v).card=s.card+v.card := Finset.card_union_of_disjoint hsv
  rw [←hcard,←mul_assoc,preSplice_cycleWord_identity (N*Equiv.swap x z) (s∪v) t x y
    (preSplice_isCycle N s v x z hs hv hx hz hsv)
    (preSplice_away ht x z hxnot hznot) (Finset.mem_union_left _ hx) hy hdis u hut,hcard]
  exact preSplice_cycleWord_identity N s v x z hs hv hx hz hsv u huv
end IntegralCharacterVarieties.BoundarySurgery

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α : Type} {G : Type*} [Group G]

lemma cycleWord_rotate (N : Equiv.Perm α) (u : α → G) (x : α) (n k : ℕ)
    (h : (N^n) x=x) :
    cycleWord N u ((N^k) x) n=
      cycleWord N u x k * cycleWord N u x n * (cycleWord N u x k)⁻¹ := by
  have he := cycleWord_add N u x n k
  have he' := cycleWord_add N u x k n
  rw [h,Nat.add_comm n k,he'] at he
  exact (eq_mul_inv_iff_mul_eq.mpr he)

variable (N : Equiv.Perm α) (s t : Finset α) (x y : α)
    (hs : N.IsCycleOn (s : Set α)) (ht : N.IsCycleOn (t : Set α))
    (hx : x∈s) (hy : y∈t) (hdis : Disjoint s t)

include hs ht hx hy hdis in
/-- Identity-strip insertion preserves the based word at EVERY old occurrence,
not only at the short-side contact chosen to describe the surgery. -/
lemma preSplice_cycleWord_allBases (u : α → G) (hu : ∀ z∈t,u z=1)
    (a : α) (ha : a∈s) :
    cycleWord (N*Equiv.swap x y) u a (s.card+t.card)=cycleWord N u a s.card := by
  have hnx : N x∈s := hs.1.mapsTo hx
  have hny : N y∈t := ht.1.mapsTo hy
  have hword : cycleWord (N*Equiv.swap x y) u (N x) (s.card+t.card)=
      cycleWord N u (N x) s.card := by
    rw [Equiv.mul_swap_eq_swap_mul]
    exact splice_cycleWord_identity N s t (N x) (N y) hs ht hnx hny hdis u hu
  have hreturn : ((N*Equiv.swap x y)^(s.card+t.card)) (N x)=N x := by
    have h := (preSplice_isCycle N s t x y hs ht hx hy hdis).pow_card_apply
      (Finset.mem_union_left t hnx)
    rw [Finset.card_union_of_disjoint hdis] at h
    exact h
  obtain ⟨k,hk,hka⟩ := hs.exists_pow_eq hnx ha
  have hmka : ((N*Equiv.swap x y)^k) (N x)=a :=
    (preSplice_pow_lt N s t x y hs hx hy hdis k hk).trans hka
  rw [←hmka,cycleWord_rotate _ _ _ _ _ hreturn,
    preSplice_word_prefix N s t x y hs hx hy hdis u k (le_of_lt hk),hword,
    ←cycleWord_rotate N u (N x) s.card k (hs.pow_card_apply hnx),hka]
  rw [hmka]

include hs ht hx hy hdis in
lemma preSplice_word_allBases_card (u : α → G) (hu : ∀ z∈t,u z=1)
    (a : α) (ha : a∈s) :
    cycleWord (N*Equiv.swap x y) u a (s∪t).card=cycleWord N u a s.card := by
  rw [Finset.card_union_of_disjoint hdis]
  exact preSplice_cycleWord_allBases N s t x y hs ht hx hy hdis u hu a ha
end IntegralCharacterVarieties.BoundarySurgery

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α ι : Type} {G : Type*} [Group G]

/-- Insert a finite family of separate doubled strips AFTER their old child
occurrences. Several old contacts may lie on the same old boundary circle. -/
noncomputable def preSpliceFamily (N : Equiv.Perm α) (x y : ι → α) : List ι → Equiv.Perm α
  | [] => N
  | i::is => preSpliceFamily (N*Equiv.swap (x i) (y i)) x y is

def attachedCircle (s : Finset α) [DecidableEq α] (t : ι → Finset α) : List ι → Finset α
  | [] => s
  | i::is => attachedCircle (s∪t i) t is

/-- The full old circle, with every contacted identity strip, remains ONE
actual cycle, and its word is preserved at EVERY old based occurrence. -/
lemma preSpliceFamily_cycle (N : Equiv.Perm α) (s : Finset α) (x y : ι → α)
    (t : ι → Finset α) (is : List ι)
    (hs : N.IsCycleOn (s : Set α))
    (ht : ∀ i∈is,N.IsCycleOn (t i : Set α))
    (hx : ∀ i∈is,x i∈s) (hy : ∀ i∈is,y i∈t i)
    (hst : ∀ i∈is,Disjoint s (t i))
    (htt : is.Pairwise (fun i j => Disjoint (t i) (t j)))
    (u : α → G) (hu : ∀ i∈is,∀ z∈t i,u z=1) :
    (preSpliceFamily N x y is).IsCycleOn (attachedCircle s t is : Set α) ∧
    ∀ a∈s,cycleWord (preSpliceFamily N x y is) u a (attachedCircle s t is).card=
      cycleWord N u a s.card := by
  induction is generalizing N s with
  | nil => exact ⟨hs,fun _ _ => rfl⟩
  | cons i is ih =>
    have hpair := List.pairwise_cons.mp htt
    have hi : i∈i::is := List.mem_cons_self
    have ht' : ∀ j∈is,(N*Equiv.swap (x i) (y i)).IsCycleOn (t j : Set α) := by
      intro j hj
      apply preSplice_away (ht j (List.mem_cons_of_mem i hj))
      · exact fun h => Finset.disjoint_left.mp (hst j (List.mem_cons_of_mem i hj)) (hx i hi) h
      · exact fun h => Finset.disjoint_left.mp (hpair.1 j hj) (hy i hi) h
    have z := ih (N*Equiv.swap (x i) (y i)) (s∪t i)
      (preSplice_isCycle N s (t i) (x i) (y i) hs (ht i hi) (hx i hi) (hy i hi) (hst i hi)) ht'
      (fun j hj => Finset.mem_union_left _ (hx j (List.mem_cons_of_mem i hj)))
      (fun j hj => hy j (List.mem_cons_of_mem i hj))
      (fun j hj => Finset.disjoint_union_left.mpr ⟨hst j (List.mem_cons_of_mem i hj),hpair.1 j hj⟩)
      hpair.2 (fun j hj => hu j (List.mem_cons_of_mem i hj))
    refine ⟨z.1,?_⟩
    intro a ha
    change cycleWord (preSpliceFamily (N*Equiv.swap (x i) (y i)) x y is) u a
      (attachedCircle (s∪t i) t is).card=cycleWord N u a s.card
    rw [z.2 a (Finset.mem_union_left _ ha)]
    exact preSplice_word_allBases_card N s (t i) (x i) (y i) hs (ht i hi)
      (hx i hi) (hy i hi) (hst i hi) u (hu i hi) a ha

noncomputable def attachedCircleOn (s : Finset α) (x : ι → α) (t : ι → Finset α) :
    List ι → Finset α
  | [] => s
  | i::is => attachedCircleOn (if x i∈s then s∪t i else s) x t is

/-- This is the version for the whole actual seam. Contacts on other old
circles are retained in the surgery, rather than being assumed absent. -/
lemma preSpliceFamily_cycleOn (N : Equiv.Perm α) (s : Finset α) (x y : ι → α)
    (t : ι → Finset α) (is : List ι)
    (hs : N.IsCycleOn (s : Set α))
    (ht : ∀ i∈is,N.IsCycleOn (t i : Set α))
    (hy : ∀ i∈is,y i∈t i)
    (hst : ∀ i∈is,Disjoint s (t i))
    (hxt : ∀ i∈is,∀ j∈is,x i∉t j)
    (htt : is.Pairwise (fun i j => Disjoint (t i) (t j)))
    (u : α → G) (hu : ∀ i∈is,∀ z∈t i,u z=1) :
    (preSpliceFamily N x y is).IsCycleOn (attachedCircleOn s x t is : Set α) ∧
    ∀ a∈s,cycleWord (preSpliceFamily N x y is) u a (attachedCircleOn s x t is).card=
      cycleWord N u a s.card := by
  induction is generalizing N s with
  | nil => exact ⟨hs,fun _ _ => rfl⟩
  | cons i is ih =>
    have hpair := List.pairwise_cons.mp htt
    have hi : i∈i::is := List.mem_cons_self
    have ht' : ∀ j∈is,(N*Equiv.swap (x i) (y i)).IsCycleOn (t j : Set α) := by
      intro j hj
      apply preSplice_away (ht j (List.mem_cons_of_mem i hj))
      · exact hxt i hi j (List.mem_cons_of_mem i hj)
      · exact fun h => Finset.disjoint_left.mp (hpair.1 j hj) (hy i hi) h
    have hxt' : ∀ j∈is,∀ k∈is,x j∉t k :=
      fun j hj k hk => hxt j (List.mem_cons_of_mem i hj) k (List.mem_cons_of_mem i hk)
    have hu' : ∀ j∈is,∀ a∈t j,u a=1 := fun j hj => hu j (List.mem_cons_of_mem i hj)
    by_cases hxi : x i∈s
    · have z := ih (N*Equiv.swap (x i) (y i)) (s∪t i)
        (preSplice_isCycle N s (t i) (x i) (y i) hs (ht i hi) hxi (hy i hi) (hst i hi)) ht'
        (fun j hj => hy j (List.mem_cons_of_mem i hj))
        (fun j hj => Finset.disjoint_union_left.mpr ⟨hst j (List.mem_cons_of_mem i hj),hpair.1 j hj⟩)
        hxt' hpair.2 hu'
      simp only [preSpliceFamily,attachedCircleOn,ite_eq_left hxi]
      refine ⟨z.1,?_⟩
      intro a ha
      rw [z.2 a (Finset.mem_union_left _ ha)]
      exact preSplice_word_allBases_card N s (t i) (x i) (y i) hs (ht i hi)
        hxi (hy i hi) (hst i hi) u (hu i hi) a ha
    · have hyi : y i∉s := fun h => Finset.disjoint_left.mp (hst i hi) h (hy i hi)
      have z := ih (N*Equiv.swap (x i) (y i)) s (preSplice_away hs _ _ hxi hyi) ht'
        (fun j hj => hy j (List.mem_cons_of_mem i hj))
        (fun j hj => hst j (List.mem_cons_of_mem i hj)) hxt' hpair.2 hu'
      simp only [preSpliceFamily,attachedCircleOn,ite_eq_right hxi]
      refine ⟨z.1,?_⟩
      intro a ha
      rw [z.2 a ha]
      refine cycleWord_eqOn hs.1.mapsTo ?_ u ha _
      intro b hb
      rw [mul_apply,Equiv.swap_apply_of_ne_of_ne]
      · exact fun he => hxi (he ▸ hb)
      · exact fun he => hyi (he ▸ hb)
end IntegralCharacterVarieties.BoundarySurgery

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α ι : Type}
lemma swap_irrel (d₁ d₂ : DecidableEq α) (a b : α) :
    @Equiv.swap α d₁ a b = @Equiv.swap α d₂ a b := by
  have h : d₁=d₂ := Subsingleton.elim _ _
  cases h
  rfl
lemma preSpliceFamily_product (N : Equiv.Perm α) (x y : ι → α) (is : List ι) :
    preSpliceFamily N x y is=N*(is.map (fun i=>Equiv.swap (x i) (y i))).prod := by
  induction is generalizing N with
  | nil => simp [preSpliceFamily]
  | cons i is ih =>
    rw [preSpliceFamily,ih,List.map_cons,List.prod_cons,mul_assoc]

lemma preSpliceFamily_append (N : Equiv.Perm α) (x y : ι → α) (is js : List ι) :
    preSpliceFamily N x y (is++js)=preSpliceFamily (preSpliceFamily N x y is) x y js := by
  simp only [preSpliceFamily_product,List.map_append,List.prod_append,mul_assoc]
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.PortWiring
open scoped Classical
open VertexTable IntegralCharacterVarieties.BoundarySurgery
variable {V : Type} {k : V → Kind} (W : PortWiring k)
    (s t u : W.Seam) (hst : s≠t) (hsu : s≠u)
    (ht : W.seamArity t=W.seamArity s) (hu : W.seamArity u=W.seamArity s)

def tripleContacts : List (Fin (W.seamArity s) × Bool) :=
  (List.finRange (W.seamArity s)).map (fun i=>(i,false)) ++
  (List.finRange (W.seamArity s)).map (fun i=>(i,true))

def tripleOld (z : Fin (W.seamArity s) × Bool) : Side W.Seam W.seamArity := ⟨s,some z.1⟩
def tripleNew (z : Fin (W.seamArity s) × Bool) : Side W.Seam W.seamArity :=
  match z.2 with
  | false => ⟨t,some (finCongr ht.symm z.1)⟩
  | true => ⟨u,some (finCongr hu.symm z.1)⟩

lemma tripleContacts_nodup : (W.tripleContacts s).Nodup := by
  rw [tripleContacts,List.nodup_append]
  refine ⟨(List.nodup_finRange _).map ?_,(List.nodup_finRange _).map ?_,?_⟩
  · intro i j h; exact congrArg Prod.fst h
  · intro i j h; exact congrArg Prod.fst h
  · intro z hz w hw heq
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hz
    obtain ⟨j,hj,hf⟩ := List.mem_map.mp hw
    have hh := congrArg Prod.snd (he.trans (heq.trans hf.symm))
    cases hh

include hst hsu in
lemma childSurgery_triple (h : ∀ r,W.seamArity ((Equiv.swap s t*Equiv.swap s u) r)=W.seamArity r) :
    W.childSurgery (Equiv.swap s t*Equiv.swap s u) h=
      ((W.tripleContacts s).map (fun z=>Equiv.swap (W.tripleOld s z) (W.tripleNew s t u ht hu z))).prod := by
  have hm := W.childSurgery_mul (Equiv.swap s t) (Equiv.swap s u)
    (W.swap_arity s t ht) (W.swap_arity s u hu)
  rw [W.childSurgery_swap s t hst ht,W.childSurgery_swap s u hsu hu] at hm
  apply hm.trans
  simp only [tripleContacts,List.map_append,List.prod_append,List.map_map]
  congr 2 <;> apply List.map_congr_left <;> intro i hi
  · exact swap_irrel _ _ _ _
  · exact swap_irrel _ _ _ _

include hst hsu in
lemma triple_preSplice (N : Equiv.Perm (Side W.Seam W.seamArity))
    (h : ∀ r,W.seamArity ((Equiv.swap s t*Equiv.swap s u) r)=W.seamArity r) :
    N*W.childSurgery (Equiv.swap s t*Equiv.swap s u) h=
      preSpliceFamily N (W.tripleOld s) (W.tripleNew s t u ht hu) (W.tripleContacts s) := by
  rw [W.childSurgery_triple s t u hst hsu ht hu h,preSpliceFamily_product]
  congr 2
  apply List.map_congr_left
  intro z hz
  exact swap_irrel _ _ _ _
end IntegralCharacterVarieties.OccurrenceIncidence.PortWiring
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {F S V U I : Type} {arity : S → ℕ}
    (A : PortAssembly F S V arity) {kind : U → Kind}
    (P : PortPatch kind I Bool Bool) (q : S)
lemma graftPerm_swaps : graftPerm A P q=
    Equiv.swap (graftPlus A P (.inl q)) (graftPlus A P (.inr (.inr false))) *
    Equiv.swap (graftPlus A P (.inl q)) (graftPlus A P (.inr (.inr true))) := by
  apply Equiv.ext
  intro p
  obtain ⟨z,rfl⟩ := (graftPlus A P).surjective p
  rw [graftPerm_apply]
  unfold graftCycle
  rw [Equiv.Perm.mul_apply,Equiv.Perm.mul_apply]
  rw [←(graftPlus A P).injective.map_swap,←(graftPlus A P).injective.map_swap]
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α β : Type} {G : Type*} [Group G]
lemma embedding_pow (N : Equiv.Perm α) (M : Equiv.Perm β) (e : α → β)
    (h : ∀ a,M (e a)=e (N a)) (a : α) (n : ℕ) :
    (M^n) (e a)=e ((N^n) a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',pow_succ',mul_apply,mul_apply,ih,h]

lemma embedding_isCycle (N : Equiv.Perm α) (M : Equiv.Perm β) (e : α ↪ β)
    (h : ∀ a,M (e a)=e (N a)) (s : Finset α) (hs : N.IsCycleOn (s : Set α)) :
    M.IsCycleOn ((s.map e : Finset β) : Set β) := by
  refine ⟨⟨?_,M.injective.injOn,?_⟩,?_⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
    rw [h]
    exact Finset.mem_map.mpr ⟨N a,hs.1.mapsTo ha,rfl⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨c,hc,he⟩ := hs.1.surjOn ha
    exact ⟨e c,Finset.mem_map.mpr ⟨c,hc,rfl⟩,(h c).trans (congrArg e he)⟩
  · intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨n,hn,he⟩ := hs.exists_pow_eq hx hy
    exact ⟨(n : ℤ),by simp only [zpow_natCast,embedding_pow N M e h,he]⟩

lemma embedding_cycleWord (N : Equiv.Perm α) (M : Equiv.Perm β) (e : α → β)
    (h : ∀ a,M (e a)=e (N a)) (u : β → G) (a : α) (n : ℕ) :
    cycleWord M u (e a) n=cycleWord N (u ∘ e) a n := by
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [embedding_pow N M e h]
  rfl
end IntegralCharacterVarieties.BoundarySurgery

end OAI
