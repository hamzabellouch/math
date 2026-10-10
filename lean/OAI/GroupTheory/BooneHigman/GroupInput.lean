import OAI.GroupTheory.BooneHigman.WordProblem

namespace OAI


/-!
Wreath-product reduction to countably infinite finitely generated decidable input groups.
-/


namespace FiniteAlgebraicEnvelopes
universe u
namespace GroupInput
variable (G : Type u) [Group G]

def shift (z : Multiplicative ℤ) : MulAut (ℤ → G) where
  toFun f i := f (i - z.toAdd)
  invFun f i := f (i + z.toAdd)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_mul' _ _ := rfl

def shifts : Multiplicative ℤ →* MulAut (ℤ → G) where
  toFun := shift G
  map_one' := by ext f i; simp [shift]
  map_mul' z w := by ext f i; simp [shift, sub_sub]

abbrev Ambient := SemidirectProduct (ℤ → G) (Multiplicative ℤ) (shifts G)

def base : G × G →* (ℤ → G) where
  toFun ab i := if i < 0 then 1 else if i = 0 then ab.1 else ab.2
  map_one' := by ext i; split <;> simp_all
  map_mul' a b := by ext i; split <;> simp_all

def embed : G × G →* Ambient G := SemidirectProduct.inl.comp (base G)
def stable : Ambient G := SemidirectProduct.inr (Multiplicative.ofAdd 1)

theorem embed_injective : Function.Injective (embed G) := by
  intro a b h
  have hh := congrArg SemidirectProduct.left h
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  exact Prod.ext (by simpa [embed, base] using h0) (by simpa [embed, base] using h1)

theorem stable_conj (g : G) :
    stable G * embed G (g,g) * (stable G)⁻¹ = embed G (1,g) := by
  simp only [stable, embed, MonoidHom.comp_apply, ← map_inv, ← SemidirectProduct.inl_aut]
  apply congrArg SemidirectProduct.inl
  ext i
  change (if i - 1 < 0 then 1 else if i - 1 = 0 then g else g) =
    (if i < 0 then 1 else if i = 0 then 1 else g)
  split_ifs <;> first | rfl | omega

theorem commutator (g : G) :
    embed G (g,g) * stable G * (embed G (g,g))⁻¹ * (stable G)⁻¹ = embed G (g,1) := by
  rw [mul_assoc (embed G (g,g)), mul_assoc (embed G (g,g)),
    ← map_inv, Prod.inv_mk, stable_conj G g⁻¹, ← map_mul]
  simp

abbrev Letters (n : ℕ) := Option (Fin n × Bool)
abbrev InputWord (n : ℕ) := List (Letters n × Bool)

def generators {n} (s : Fin n → G) : Letters n → Ambient G
  | none => stable G
  | some (i, false) => embed G (s i,1)
  | some (i, true) => embed G (1,s i)

def heightLetter {n} : Letters n × Bool → ℤ
  | (none, true) => 1
  | (none, false) => -1
  | (some _, _) => 0

def atLetter {n} (a : Letters n × Bool) (i : ℤ) : Word n :=
  match a.1 with
  | none => []
  | some (j, b) => if (b = false ∧ i = 0) ∨ (b = true ∧ 0 < i) then [(j,a.2)] else []

def height {n} (w : InputWord n) : ℤ := (w.map heightLetter).sum

def sectionWord {n} (i : ℤ) : InputWord n → Word n
  | [] => []
  | a :: w => atLetter a i ++ sectionWord (i - heightLetter a) w

def value {n} (s : Fin n → G) (w : InputWord n) : Ambient G :=
  (w.map fun a => if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).prod

@[simp] theorem height_nil {n} : height ([] : InputWord n) = 0 := rfl
@[simp] theorem height_cons {n} (a) (w : InputWord n) :
    height (a::w) = heightLetter a + height w := rfl

@[simp] theorem heightLetter_bounds {n} (a : Letters n × Bool) :
    -1 ≤ heightLetter a ∧ heightLetter a ≤ 1 := by
  rcases a with ⟨_ | ⟨j,b⟩, t⟩ <;> cases t <;> simp [heightLetter]

@[simp] theorem value_nil {n} (s : Fin n → G) : value G s [] = 1 := rfl
@[simp] theorem value_cons {n} (s : Fin n → G) (a : Letters n × Bool) (w) :
    value G s (a::w) = (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹) *
      value G s w := rfl

theorem value_right {n} (s : Fin n → G) (w : InputWord n) :
    (value G s w).right.toAdd = height w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [value_cons, SemidirectProduct.mul_right]
    change (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).right.toAdd +
      (value G s w).right.toAdd = heightLetter a + height w
    rw [ih]
    congr 1
    rcases a with ⟨_ | ⟨i,b⟩,t⟩ <;> cases t
    all_goals try cases b
    all_goals simp [generators, stable, embed, heightLetter]

theorem signed_right {n} (s : Fin n → G) (a : Letters n × Bool) :
    (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).right =
      Multiplicative.ofAdd (heightLetter a) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> cases t
  all_goals try cases b
  all_goals rfl

theorem signed_left {n} (s : Fin n → G) (a : Letters n × Bool) (i : ℤ) :
    (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).left i =
      evalWord s (atLetter a i) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> cases t
  · change (1 : G)⁻¹ = 1
    exact inv_one
  · rfl
  all_goals cases b
  all_goals simp only [generators, Bool.false_eq_true, ↓reduceIte, embed,
    MonoidHom.comp_apply, ← map_inv, SemidirectProduct.left_inl, base,
    MonoidHom.coe_mk, OneHom.coe_mk,
    atLetter, evalWord]
  all_goals split_ifs <;> simp_all [List.map_cons, List.prod_cons] <;> try omega
  all_goals split_ifs <;> first | rfl | omega

theorem value_cons_left {n} (s : Fin n → G) (a : Letters n × Bool)
    (w : InputWord n) (i : ℤ) :
    (value G s (a::w)).left i = evalWord s (atLetter a i) *
      (value G s w).left (i - heightLetter a) := by
  rw [value_cons, SemidirectProduct.mul_left]
  change (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).left i *
    (value G s w).left (i - (if a.2 then generators G s a.1 else
      (generators G s a.1)⁻¹).right.toAdd) = _
  rw [signed_left, signed_right]
  rfl

theorem value_left {n} (s : Fin n → G) (w : InputWord n) (i : ℤ) :
    (value G s w).left i = evalWord s (sectionWord i w) := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    rw [value_cons_left, ih]
    simp [sectionWord, evalWord, List.map_append, List.prod_append]

theorem at_low {n} (w : InputWord n) (i : ℤ) (hi : i < -(w.length : ℤ)) :
    sectionWord i w = [] := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih =>
    have hb := heightLetter_bounds a
    have hil : i < 0 := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega
    have hii : i - heightLetter a < -(w.length : ℤ) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega
    rw [sectionWord, ih _ hii]
    simp only [List.append_nil]
    rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> simp [atLetter, ne_of_lt hil, not_lt_of_ge (le_of_lt hil)]

theorem at_high {n} (w : InputWord n) (i j : ℤ)
    (hi : (w.length : ℤ) < i) (hj : (w.length : ℤ) < j) : sectionWord i w = sectionWord j w := by
  induction w generalizing i j with
  | nil => rfl
  | cons a w ih =>
    have hb := heightLetter_bounds a
    have his : 0 < i ∧ (w.length : ℤ) < i - heightLetter a := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega
    have hjs : 0 < j ∧ (w.length : ℤ) < j - heightLetter a := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hj; omega
    rw [sectionWord, sectionWord, ih _ _ his.2 hjs.2]
    congr 1
    rcases a with ⟨_ | ⟨k,b⟩,t⟩ <;>
      simp [atLetter, ne_of_gt his.1, ne_of_gt hjs.1, his.1, hjs.1]

theorem value_eq_one_iff {n} (s : Fin n → G) (w : InputWord n) :
    value G s w = 1 ↔ height w = 0 ∧
      ∀ k ∈ List.range (2 * w.length + 3),
        evalWord s (sectionWord ((k : ℤ) - (w.length : ℤ) - 1) w) = 1 := by
  constructor
  · intro h
    constructor
    · rw [← value_right G s, h]; rfl
    · intro k _; rw [← value_left G s, h]; rfl
  · rintro ⟨hh, hv⟩
    apply SemidirectProduct.ext
    · funext i
      change (value G s w).left i = 1
      rw [value_left]
      by_cases hi : i < -(w.length : ℤ)
      · rw [at_low w i hi]; rfl
      by_cases hj : (w.length : ℤ) + 1 < i
      · have hk := hv (2*w.length+2) (List.mem_range.mpr (by omega))
        have he : ((2*w.length+2 : ℕ) : ℤ) - (w.length : ℤ) - 1 =
            (w.length : ℤ) + 1 := by push_cast; omega
        rw [he] at hk
        rw [at_high w i ((w.length : ℤ)+1) (by omega) (by omega)]
        exact hk
      · let k := (i + (w.length : ℤ) + 1).toNat
        have hk : (k : ℤ) = i + (w.length : ℤ) + 1 := Int.toNat_of_nonneg (by omega)
        have hkr : k < 2*w.length+3 := by omega
        have hki : (k : ℤ) - (w.length : ℤ) - 1 = i := by omega
        simpa only [hki] using hv k (List.mem_range.mpr hkr)
    · apply Multiplicative.toAdd.injective
      exact (value_right G s w).trans hh

/-- Unsimplified positive/negative counters avoid assuming a computation model on `G`. -/
def countsLetter {n} : Letters n × Bool → ℕ × ℕ
  | (none, true) => (1,0)
  | (none, false) => (0,1)
  | (some _, _) => (0,0)

def counts {n} (w : InputWord n) : ℕ × ℕ :=
  w.foldl (fun c a => (c.1 + (countsLetter a).1, c.2 + (countsLetter a).2)) (0,0)

def natAtLetter {n} (a : Letters n × Bool) (pq : ℕ × ℕ) : Word n :=
  match a.1 with
  | none => []
  | some (j,b) => if (b = false ∧ pq.1 = pq.2) ∨ (b = true ∧ pq.2 < pq.1)
      then [(j,a.2)] else []

def natStep {n} (v : (ℕ × ℕ) × Word n) (a : Letters n × Bool) : (ℕ × ℕ) × Word n :=
  ((v.1.1 + (countsLetter a).2, v.1.2 + (countsLetter a).1),
    v.2 ++ natAtLetter a v.1)

def natAt {n} (w : InputWord n) (pq : ℕ × ℕ) : Word n :=
  (w.foldl natStep (pq,[])).2

theorem heightLetter_eq {n} (a : Letters n × Bool) :
    heightLetter a = ((countsLetter a).1 : ℤ) - ((countsLetter a).2 : ℤ) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩ <;> cases t <;> rfl

theorem counts_fold {n} (w : InputWord n) (p q : ℕ) :
    let c := w.foldl (fun c a => (c.1 + (countsLetter a).1, c.2 + (countsLetter a).2)) (p,q)
    (c.1 : ℤ) - (c.2 : ℤ) = (p : ℤ) - (q : ℤ) + height w := by
  induction w generalizing p q with
  | nil => simp
  | cons a w ih =>
    simp only [List.foldl_cons, height_cons]
    rw [ih, heightLetter_eq]
    push_cast
    ring

theorem counts_eq_height {n} (w : InputWord n) :
    ((counts w).1 : ℤ) - ((counts w).2 : ℤ) = height w := by
  simpa [counts] using counts_fold w 0 0

theorem natAtLetter_eq {n} (a : Letters n × Bool) (p q : ℕ) :
    natAtLetter a (p,q) = atLetter a ((p : ℤ) - (q : ℤ)) := by
  rcases a with ⟨_ | ⟨j,b⟩,t⟩
  · rfl
  · simp [natAtLetter, atLetter, sub_eq_zero]

theorem natStep_fold {n} (w : InputWord n) (p q : ℕ) (v : Word n) :
    (w.foldl natStep ((p,q),v)).2 = v ++ sectionWord ((p : ℤ) - (q : ℤ)) w := by
  induction w generalizing p q v with
  | nil => simp [sectionWord]
  | cons a w ih =>
    simp only [List.foldl_cons, natStep]
    rw [ih, natAtLetter_eq, List.append_assoc]
    simp only [sectionWord]
    congr 2
    rw [heightLetter_eq]
    push_cast
    congr 1
    ring

theorem natAt_eq {n} (w : InputWord n) (p q : ℕ) :
    natAt w (p,q) = sectionWord ((p : ℤ) - (q : ℤ)) w := by
  simpa [natAt] using natStep_fold w p q []

open Primrec

theorem countsLetter_primrec (n) : Primrec (@countsLetter n) := Primrec.dom_finite _

theorem counts_primrec (n) : Primrec (@counts n) := by
  unfold counts
  apply Primrec.list_foldl (h := fun _ ca =>
    (ca.1.1 + (countsLetter ca.2).1, ca.1.2 + (countsLetter ca.2).2))
    Primrec.id (Primrec.const (0,0))
  unfold Primrec₂
  apply Primrec.pair
  · exact Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp ((countsLetter_primrec n).comp (Primrec.snd.comp Primrec.snd)))
  · exact Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp ((countsLetter_primrec n).comp (Primrec.snd.comp Primrec.snd)))

theorem natAtLetter_primrec (n) : Primrec₂ (@natAtLetter n) := by
  unfold natAtLetter Primrec₂
  refine (Primrec.option_casesOn (g := fun a jb =>
    if (jb.2 = false ∧ a.2.1 = a.2.2) ∨ (jb.2 = true ∧ a.2.2 < a.2.1)
    then [(jb.1,a.1.2)] else [])
    (Primrec.fst.comp Primrec.fst) (Primrec.const []) ?_).of_eq (fun a => by
      rcases a with ⟨⟨_ | ⟨j,b⟩,t⟩,pq⟩ <;> rfl)
  unfold Primrec₂
  apply Primrec.ite
  · exact ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const false)).and
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).or
      ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true)).and
      (Primrec.nat_lt.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  · exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const [])
  · exact Primrec.const []

theorem natStep_primrec (n) : Primrec₂ (@natStep n) := by
  unfold natStep Primrec₂
  apply Primrec.pair
  · exact Primrec.pair
      (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp ((countsLetter_primrec n).comp Primrec.snd)))
      (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp ((countsLetter_primrec n).comp Primrec.snd)))
  · exact Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      ((natAtLetter_primrec n).comp Primrec.snd (Primrec.fst.comp Primrec.fst))

theorem natAt_primrec (n) : Primrec₂ (@natAt n) := by
  unfold natAt Primrec₂
  apply Primrec.snd.comp
  exact Primrec.list_foldl Primrec.fst (Primrec.pair Primrec.snd (Primrec.const []))
    (((natStep_primrec n).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)

/-- Closure of genuine computability under a variable finite universal test. -/
theorem computable_forall_lt {α : Type*} [Primcodable α] {p : α × ℕ → Prop}
    (hp : ComputablePred p) : ComputablePred (fun a : α × ℕ => ∀ k < a.2, p (a.1,k)) := by
  classical
  let test (a : α) : ℕ → Bool := Nat.rec true (fun k b => b && decide (p (a,k)))
  have hc : Computable₂ test := by
    unfold test Computable₂
    apply Computable.nat_rec (h := fun a kb => kb.2 && decide (p (a.1,kb.1)))
      Computable.snd (Computable.const true)
    exact ((Primrec.and.to_comp).comp (Computable.snd.comp Computable.snd)
      (hp.decide.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)))).to₂
  have ht (a : α) (n : ℕ) : test a n = true ↔ ∀ k < n, p (a,k) := by
    induction n with
    | zero => simp [test]
    | succ n ih =>
      change (test a n && decide (p (a,n))) = true ↔ _
      simp only [Bool.and_eq_true, decide_eq_true_eq, ih]
      exact ⟨fun h k hk => (Nat.lt_succ_iff_lt_or_eq.mp hk).elim (h.1 k) (fun he => he ▸ h.2),
        fun h => ⟨fun k hk => h k (by omega),h n (by omega)⟩⟩
  have hh : ComputablePred (fun a : α × ℕ => test a.1 a.2 = true) :=
    ⟨fun a => Classical.propDecidable (test a.1 a.2 = true),
      (show Computable (fun a : α × ℕ => test a.1 a.2) from hc).of_eq
        (fun a => by simp only [Bool.decide_eq_true])⟩
  exact hh.of_eq fun a => ht a.1 a.2

/-- The decision procedure for this finitely generated wreath subgroup. -/
theorem value_wordProblem {n} (s : Fin n → G)
    (hs : ComputablePred (fun w : Word n => evalWord s w = 1)) :
    ComputablePred (fun w : InputWord n => value G s w = 1) := by
  classical
  have hc : ComputablePred (fun w : InputWord n => (counts w).1 = (counts w).2) :=
    (Primrec.eq.comp (Primrec.fst.comp (counts_primrec n))
      (Primrec.snd.comp (counts_primrec n))).computablePred
  have hp : ComputablePred (fun a : InputWord n × ℕ =>
      evalWord s (natAt a.1 (a.2, a.1.length+1)) = 1) :=
    ⟨inferInstance, hs.decide.comp ((natAt_primrec n).comp Primrec.fst
      (Primrec.pair Primrec.snd (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))).to_comp⟩
  have hq : ComputablePred (fun w : InputWord n =>
      ∀ k < 2*w.length+3, evalWord s (natAt w (k,w.length+1)) = 1) :=
    ⟨inferInstance, (computable_forall_lt hp).decide.comp
      (Primrec.pair Primrec.id (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length) (Primrec.const 3))).to_comp⟩
  have ht : ComputablePred (fun w : InputWord n =>
      (counts w).1 = (counts w).2 ∧
      ∀ k < 2*w.length+3, evalWord s (natAt w (k,w.length+1)) = 1) :=
    ⟨inferInstance, by simpa only [Bool.decide_and] using
      ((Primrec.and.to_comp).comp hc.decide hq.decide)⟩
  exact ht.of_eq fun w => by
    rw [value_eq_one_iff]
    constructor
    · rintro ⟨h, hv⟩
      constructor
      · have hh := counts_eq_height w
        rw [h, sub_self] at hh
        exact hh.symm
      · intro k hk
        have hvk := hv k (List.mem_range.mp hk)
        simpa [natAt_eq, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hvk
    · rintro ⟨h, hv⟩
      constructor
      · have hh := counts_eq_height w
        rw [h, sub_eq_zero] at hh
        exact Int.ofNat_inj.mp hh
      · intro k hk
        simpa [natAt_eq, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hv k (List.mem_range.mpr hk)

/-- The finitely generated subgroup, rather than the whole unrestricted wreath product. -/
def generated {n} (s : Fin n → G) : Subgroup (Ambient G) :=
  Subgroup.closure (Set.range (generators G s))

theorem embed_mem_generated {n} (s : Fin n → G)
    (hs : Subgroup.closure (Set.range s) = ⊤) (a b : G) :
    embed G (a,b) ∈ generated G s := by
  have hl : ∀ x : G, embed G (x,1) ∈ generated G s := by
    have hle : Subgroup.closure (Set.range s) ≤ (generated G s).comap
        ((embed G).comp (MonoidHom.inl G G)) := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i,rfl⟩
      exact Subgroup.subset_closure ⟨some (i,false),rfl⟩
    rw [hs] at hle
    exact fun x => hle (Subgroup.mem_top x)
  have hr : ∀ x : G, embed G (1,x) ∈ generated G s := by
    have hle : Subgroup.closure (Set.range s) ≤ (generated G s).comap
        ((embed G).comp (MonoidHom.inr G G)) := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i,rfl⟩
      exact Subgroup.subset_closure ⟨some (i,true),rfl⟩
    rw [hs] at hle
    exact fun x => hle (Subgroup.mem_top x)
  have hh := (generated G s).mul_mem (hl a) (hr b)
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] at hh

def subgroupGenerators {n} (s : Fin n → G) : Letters n → generated G s :=
  fun a => ⟨generators G s a, Subgroup.subset_closure ⟨a,rfl⟩⟩

theorem subgroupGenerators_generate {n} (s : Fin n → G) :
    Subgroup.closure (Set.range (subgroupGenerators G s)) = ⊤ := by
  apply Subgroup.map_injective (generated G s).subtype_injective
  rw [MonoidHom.map_closure]
  have him : (generated G s).subtype '' Set.range (subgroupGenerators G s) =
      Set.range (generators G s) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩; exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩; exact ⟨subgroupGenerators G s a,⟨a,rfl⟩,rfl⟩
  rw [him]
  change generated G s = Subgroup.map (generated G s).subtype ⊤
  ext x
  constructor
  · intro hx; exact ⟨⟨x,hx⟩,Subgroup.mem_top _,rfl⟩
  · rintro ⟨y,_,rfl⟩; exact y.property

theorem generated_fg {n} (s : Fin n → G) : Group.FG (generated G s) :=
  Group.fg_iff.mpr ⟨Set.range (subgroupGenerators G s), subgroupGenerators_generate G s,
    Set.finite_range _⟩

theorem generated_wordProblem {n} (s : Fin n → G)
    (hs : ComputablePred (fun w : Word n => evalWord s w = 1)) :
    HasDecidableWordProblem (generated G s) := by
  classical
  let m := Fintype.card (Letters n)
  let e : Letters n ≃ Fin m := Fintype.equivFin (Letters n)
  let t : Fin m → generated G s := fun i => subgroupGenerators G s (e.symm i)
  have hgen : Set.range t = Set.range (subgroupGenerators G s) := by
    ext x
    exact ⟨fun ⟨i,hi⟩ => ⟨e.symm i,hi⟩, fun ⟨a,ha⟩ => ⟨e a,by simpa [t] using ha⟩⟩
  refine ⟨m,t,hgen ▸ subgroupGenerators_generate G s,?_⟩
  let tr (w : Word m) : InputWord n := w.map fun a => (e.symm a.1,a.2)
  have ht : Primrec tr :=
    Primrec.list_map Primrec.id ((Primrec.dom_finite (fun a : Fin m × Bool =>
      (e.symm a.1,a.2))).comp Primrec.snd)
  have hc : ComputablePred (fun w : Word m => value G s (tr w) = 1) :=
    ⟨inferInstance, (value_wordProblem G s hs).decide.comp ht.to_comp⟩
  exact hc.of_eq fun w => by
    have he : ((evalWord t w : generated G s) : Ambient G) = value G s (tr w) := by
      change (generated G s).subtype (evalWord t w) = _
      simp only [evalWord, tr, value, map_list_prod, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro a _
      cases a.2 <;> rfl
    rw [← he]
    change (generated G s).subtype (evalWord t w) = (generated G s).subtype 1 ↔ _
    exact (generated G s).subtype_injective.eq_iff

end GroupInput

/-- Wreath-product reduction using an explicit step-function witness.
The construction includes finite and trivial input groups. -/
theorem group_input (G : Type u) [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Group.FG H ∧ HasDecidableWordProblem H ∧
      ∃ (f : G × G →* H) (s : H), Function.Injective f ∧
        ∀ g : G, f (g,g) * s * (f (g,g))⁻¹ * s⁻¹ = f (g,1) := by
  obtain ⟨n,t,hgen,hwp⟩ := hG
  let H := GroupInput.generated G t
  let f : G × G →* H := (GroupInput.embed G).codRestrict H fun ab =>
    GroupInput.embed_mem_generated G t hgen ab.1 ab.2
  let s : H := ⟨GroupInput.stable G,Subgroup.subset_closure ⟨none,rfl⟩⟩
  refine ⟨H,inferInstance,GroupInput.generated_fg G t,
    GroupInput.generated_wordProblem G t hwp,f,s,?_,?_⟩
  · intro a b h
    exact GroupInput.embed_injective G (congrArg Subtype.val h)
  · intro g
    apply Subtype.val_injective
    exact GroupInput.commutator G g


end FiniteAlgebraicEnvelopes

end OAI
