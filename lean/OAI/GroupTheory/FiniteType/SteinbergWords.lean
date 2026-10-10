import Mathlib

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace SteinbergWords
variable {H : Type*} [Group H]

lemma interchange (a b c : H) (hac : Commute a c)
    (huv : Commute ⁅a,b⁆ ⁅b,c⁆) (hvc : Commute ⁅b,c⁆ c) :
    ⁅⁅a,b⁆,c⁆=⁅a,⁅b,c⁆⁆ := by
  have h1 : a*b*c=⁅a,b⁆*⁅b,c⁆*c*b*a := by
    calc
      a*b*c = ⁅a,b⁆*b*a*c := by simp [commutatorElement_def,mul_assoc]
      _ = ⁅a,b⁆*b*c*a := by rw [mul_assoc (⁅a,b⁆*b) a c,hac.eq]; group
      _ = ⁅a,b⁆*⁅b,c⁆*c*b*a := by simp [commutatorElement_def,mul_assoc]
  have h2 : a*b*c=⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*⁅a,b⁆*b*a := by
    calc
      a*b*c = a*⁅b,c⁆*c*b := by simp [commutatorElement_def,mul_assoc]
      _ = ⁅a,⁅b,c⁆⁆*⁅b,c⁆*a*c*b := by simp [commutatorElement_def,mul_assoc]
      _ = ⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*a*b := by rw [mul_assoc (⁅a,⁅b,c⁆⁆*⁅b,c⁆) a c,hac.eq]; group
      _ = ⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*⁅a,b⁆*b*a := by simp [commutatorElement_def,mul_assoc]
  have he : ⁅a,b⁆*⁅b,c⁆*c=⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*⁅a,b⁆ :=
    mul_right_cancel (mul_right_cancel (h1.symm.trans h2))
  have hv : Commute ⁅b,c⁆ ⁅⁅a,b⁆,c⁆ :=
    ((huv.symm.mul_right hvc).mul_right huv.symm.inv_right).mul_right hvc.inv_right
  apply mul_right_cancel (b:=⁅b,c⁆*c*⁅a,b⁆)
  calc
    ⁅⁅a,b⁆,c⁆*(⁅b,c⁆*c*⁅a,b⁆) = ⁅b,c⁆*(⁅⁅a,b⁆,c⁆*c*⁅a,b⁆) := by
      simp only [← mul_assoc]
      rw [hv.symm.eq]
    _ = ⁅b,c⁆*(⁅a,b⁆*c) := by simp [commutatorElement_def,mul_assoc]
    _ = ⁅a,b⁆*⁅b,c⁆*c := by rw [← mul_assoc,huv.symm.eq]
    _ = ⁅a,⁅b,c⁆⁆*(⁅b,c⁆*c*⁅a,b⁆) := by simpa only [mul_assoc] using he

variable {n α : Type*}

structure Initial where
  gen : ∀ i j : n, i≠j → Option α → H
  away : ∀ i j k l hij hkl, i≠l → j≠k → ∀ a b,
    Commute (gen i j hij a) (gen k l hkl b)
  chain_left : ∀ i j k hij hjk hik a,
    ⁅gen i j hij none,gen j k hjk a⁆=gen i k hik a
  chain_right : ∀ i j k hij hjk hik a,
    ⁅gen i j hij a,gen j k hjk none⁆=gen i k hik a

variable (outside : ∀ i j k l : n, ∃ p, p≠i ∧ p≠j ∧ p≠k ∧ p≠l)

private def middle (i j : n) : n := (outside i j i j).choose
private lemma middle_left (i j : n) : i≠middle outside i j :=
  (outside i j i j).choose_spec.1.symm
private lemma middle_right (i j : n) : middle outside i j≠j :=
  (outside i j i j).choose_spec.2.1

variable (D : Initial (n:=n) (α:=α) (H:=H))

def word (i j : n) (hij : i≠j) (w : List α) : H :=
  match w with
  | [] => D.gen i j hij none
  | [a] => D.gen i j hij (some a)
  | a::b::t => ⁅D.gen i (middle outside i j) (middle_left outside i j) (some a),
      word (middle outside i j) j (middle_right outside i j) (b::t)⁆

@[simp] lemma word_nil (i j : n) (hij) : word outside D i j hij []=D.gen i j hij none := by
  rw [word]
@[simp] lemma word_singleton (i j : n) (hij) (a : α) :
    word outside D i j hij [a]=D.gen i j hij (some a) := by rw [word]
lemma word_cons_cons (i j : n) (hij) (a b : α) (t : List α) :
    word outside D i j hij (a::b::t)=
      ⁅word outside D i (middle outside i j) (middle_left outside i j) [a],
        word outside D (middle outside i j) j (middle_right outside i j) (b::t)⁆ := by
  rw [word_singleton]
  rw [word]

def Away (m : ℕ) : Prop := ∀ (u v : List α), u.length ≤ m → v.length ≤ m →
  ∀ i j k l hij hkl, i≠l → j≠k →
    Commute (word outside D i j hij u) (word outside D k l hkl v)

def Chain (m : ℕ) : Prop := ∀ (u v : List α), u.length+v.length ≤ m →
  ∀ i j k hij hjk hik,
    ⁅word outside D i j hij u,word outside D j k hjk v⁆=
      word outside D i k hik (u++v)

lemma base : Away outside D 1 ∧ Chain outside D 1 := by
  constructor
  · intro u v hu hv i j k l hij hkl hil hjk
    cases u with
    | nil =>
      cases v with
      | nil => exact D.away i j k l hij hkl hil hjk _ _
      | cons b s =>
        have hs : s=[] := List.eq_nil_of_length_eq_zero (by simpa using hv)
        subst s; exact D.away i j k l hij hkl hil hjk _ _
    | cons a t =>
      have ht : t=[] := List.eq_nil_of_length_eq_zero (by simpa using hu)
      subst t
      cases v with
      | nil => exact D.away i j k l hij hkl hil hjk _ _
      | cons b s =>
        have hs : s=[] := List.eq_nil_of_length_eq_zero (by simpa using hv)
        subst s; exact D.away i j k l hij hkl hil hjk _ _
  · intro u v huv i j k hij hjk hik
    cases u with
    | nil =>
      cases v with
      | nil => exact D.chain_left i j k hij hjk hik none
      | cons b s =>
        have hs : s=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at huv; omega)
        subst s; exact D.chain_left i j k hij hjk hik (some b)
    | cons a t =>
      have ht : t=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at huv; omega)
      have hv : v=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at huv; omega)
      subst t v; exact D.chain_right i j k hij hjk hik (some a)

lemma split_head {m : ℕ} (hm : 1 ≤ m) (ha : Away outside D m) (hc : Chain outside D m)
    (a : α) (t : List α) (ht : t.length ≤ m)
    (i j k : n) (hij : i≠j) (hik : i≠k) (hkj : k≠j) :
    word outside D i j hij (a::t)=
      ⁅word outside D i k hik [a],word outside D k j hkj t⁆ := by
  cases t with
  | nil => exact (hc [a] [] (by simpa using hm) i k j hik hkj hij).symm
  | cons b t =>
    rw [word_cons_cons]
    let p := middle outside i j
    have hip : i≠p := middle_left outside i j
    have hpj : p≠j := middle_right outside i j
    by_cases hkp : k=p
    · subst k; rfl
    have hleft := hc [a] [] (by simpa using hm) i k p hik hkp hip
    have hright := hc [] (b::t) (by simpa using ht) k p j hkp hpj hkj
    simp only [List.append_nil,List.nil_append] at hleft hright
    have hi := interchange (word outside D i k hik [a]) (word outside D k p hkp [])
      (word outside D p j hpj (b::t))
      (ha [a] (b::t) (by simpa using hm) ht i k p j hik hpj hij hkp)
      (by rw [hleft,hright]; exact ha [a] (b::t) (by simpa using hm) ht i p k j hip hkj hij (Ne.symm hkp))
      (by rw [hright]; exact ha (b::t) (b::t) ht ht k j p j hkj hpj hkj hpj.symm)
    simpa only [hleft,hright] using hi

lemma commute_bracket_left {a b c : H} (hac : Commute a c) (hbc : Commute b c) :
    Commute ⁅a,b⁆ c :=
  ((hac.mul_left hbc).mul_left hac.inv_left).mul_left hbc.inv_left

lemma away_step {m : ℕ} (hm : 1 ≤ m) (ha : Away outside D m) (hc : Chain outside D m) :
    Away outside D (m+1) := by
  have hn : ∀ (u v : List α), u.length ≤ m+1 → v.length ≤ m →
      ∀ i j k l hij hkl, i≠l → j≠k →
        Commute (word outside D i j hij u) (word outside D k l hkl v) := by
    intro u v hu hv i j k l hij hkl hil hjk
    by_cases hu' : u.length ≤ m
    · exact ha u v hu' hv i j k l hij hkl hil hjk
    cases u with
    | nil => simp at hu'
    | cons a t =>
      have ht : t.length ≤ m := by simp only [List.length_cons] at hu; omega
      obtain ⟨p,hpi,hpj,hpk,hpl⟩ := outside i j k l
      rw [split_head outside D hm ha hc a t ht i j p hij hpi.symm hpj]
      apply commute_bracket_left
      · exact ha [a] v (by simpa using hm) hv i p k l hpi.symm hkl hil hpk
      · exact ha t v ht hv p j k l hpj hkl hpl hjk
  intro u v hu hv i j k l hij hkl hil hjk
  by_cases hv' : v.length ≤ m
  · exact hn u v hu hv' i j k l hij hkl hil hjk
  cases v with
  | nil => simp at hv'
  | cons b t =>
    have ht : t.length ≤ m := by simp only [List.length_cons] at hv; omega
    obtain ⟨p,hpk,hpl,hpi,hpj⟩ := outside k l i j
    rw [split_head outside D hm ha hc b t ht k l p hkl hpk.symm hpl]
    exact (commute_bracket_left
      (hn u [b] hu (by simpa using hm) i j k p hij hpk.symm hpi.symm hjk).symm
      (hn u t hu ht i j p l hij hpl hil hpj.symm).symm).symm

lemma chain_step {m : ℕ} (hm : 1 ≤ m) (ha : Away outside D m) (hc : Chain outside D m)
    (han : Away outside D (m+1)) : Chain outside D (m+1) := by
  intro u v huv i j k hij hjk hik
  by_cases ho : u.length+v.length ≤ m
  · exact hc u v ho i j k hij hjk hik
  cases u with
  | nil =>
    cases v with
    | nil => simp at ho
    | cons a t =>
      have ht : t.length ≤ m := by simp only [List.length_nil,List.length_cons] at huv; omega
      obtain ⟨p,hpi,hpj,hpk,_⟩ := outside i j k k
      have hleft := hc [] [a] (by simpa using hm) i j p hij hpj.symm hpi.symm
      simp only [List.nil_append] at hleft
      have hs := split_head outside D hm ha hc a t ht j k p hjk hpj.symm hpk
      have hi := interchange (word outside D i j hij [])
        (word outside D j p hpj.symm [a]) (word outside D p k hpk t)
        (han [] t (by simp) (by omega) i j p k hij hpk hik hpj.symm)
        (by
          rw [hleft,← hs]
          exact han [a] (a::t) (by simp only [List.length_singleton]; omega)
            (by simpa using huv) i p j k hpi.symm hjk hik hpj)
        (by
          rw [← hs]
          exact han (a::t) t (by simpa using huv) (by omega) j k p k hjk hpk hjk hpk.symm)
      simp only [List.nil_append]
      rw [hs,← hi,hleft]
      exact (split_head outside D hm ha hc a t ht i k p hik hpi.symm hpk).symm
  | cons a t =>
    have ht : t.length ≤ m := by simp only [List.length_cons] at huv; omega
    have htv : t.length+v.length ≤ m := by simp only [List.length_cons] at huv; omega
    obtain ⟨p,hpi,hpj,hpk,_⟩ := outside i j k k
    have hs := split_head outside D hm ha hc a t ht i j p hij hpi.symm hpj
    have hr := hc t v htv p j k hpj hjk hpk
    have hi := interchange (word outside D i p hpi.symm [a])
      (word outside D p j hpj t) (word outside D j k hjk v)
      (han [a] v (by simp only [List.length_singleton]; omega) (by simp only [List.length_cons] at huv; omega)
        i p j k hpi.symm hjk hik hpj)
      (by
        rw [← hs,hr]
        exact han (a::t) (t++v) (by simp only [List.length_cons] at *; omega)
          (by simp only [List.length_append]; omega) i j p k hij hpk hik hpj.symm)
      (by
        rw [hr]
        exact han (t++v) v (by simp only [List.length_append]; omega)
          (by simp only [List.length_cons] at huv; omega) p k j k hpk hjk hpk hjk.symm)
    rw [hs,hi,hr]
    exact (split_head outside D hm ha hc a (t++v) (by simpa only [List.length_append] using htv)
      i k p hik hpi.symm hpk).symm

lemma laws (m : ℕ) : Away outside D (m+1) ∧ Chain outside D (m+1) := by
  induction m with
  | zero => exact base outside D
  | succ m ih =>
    have ha := away_step outside D (by omega : 1 ≤ m+1) ih.1 ih.2
    exact ⟨ha,chain_step outside D (by omega) ih.1 ih.2 ha⟩

theorem word_commute (u v : List α) (i j k l : n) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) :
    Commute (word outside D i j hij u) (word outside D k l hkl v) :=
  (laws outside D (u.length+v.length)).1 u v (by omega) (by omega) i j k l hij hkl hil hjk

theorem word_chain (u v : List α) (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅word outside D i j hij u,word outside D j k hjk v⁆=word outside D i k hik (u++v) :=
  (laws outside D (u.length+v.length)).2 u v (by omega) i j k hij hjk hik

def rootSubgroup (i j : n) (hij : i≠j) : Subgroup H :=
  Subgroup.closure (Set.range (word outside D i j hij))

instance rootSubgroupCommutative (i j : n) (hij : i≠j) :
    IsMulCommutative (rootSubgroup outside D i j hij) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ _
  exact word_commute outside D u v i j i j hij hij hij hij.symm

open scoped IsMulCommutative

def polynomialAdd (i j : n) (hij : i≠j) : FreeAbelianGroup (FreeMonoid α) →+ Additive H :=
  (rootSubgroup outside D i j hij).subtype.toAdditive.comp
    (FreeAbelianGroup.lift (fun w : FreeMonoid α =>
      Additive.ofMul (⟨word outside D i j hij w,Subgroup.subset_closure ⟨w,rfl⟩⟩ :
        rootSubgroup outside D i j hij)))

def polynomial (i j : n) (hij : i≠j) (a : FreeAbelianGroup (FreeMonoid α)) : H :=
  Additive.toMul (polynomialAdd outside D i j hij a)

@[simp] lemma polynomial_of (i j : n) (hij : i≠j) (w : FreeMonoid α) :
    polynomial outside D i j hij (FreeAbelianGroup.of w)=word outside D i j hij w := by
  simp [polynomial,polynomialAdd]
@[simp] lemma polynomial_zero (i j : n) (hij : i≠j) :
    polynomial outside D i j hij 0=1 := by simp [polynomial]
lemma polynomial_add (i j : n) (hij : i≠j) (a b : FreeAbelianGroup (FreeMonoid α)) :
    polynomial outside D i j hij (a+b)=polynomial outside D i j hij a*polynomial outside D i j hij b := by
  simp [polynomial]
lemma polynomial_neg (i j : n) (hij : i≠j) (a : FreeAbelianGroup (FreeMonoid α)) :
    polynomial outside D i j hij (-a)=(polynomial outside D i j hij a)⁻¹ := by simp [polynomial]

lemma polynomial_commute (i j k l : n) (hij : i≠j) (hkl : k≠l) (hil : i≠l) (hjk : j≠k)
    (a b : FreeAbelianGroup (FreeMonoid α)) :
    Commute (polynomial outside D i j hij a) (polynomial outside D k l hkl b) := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of u =>
    induction b using FreeAbelianGroup.induction_on with
    | zero => simp
    | of v => simpa only [polynomial_of] using word_commute outside D u v i j k l hij hkl hil hjk
    | neg b hb => simpa only [polynomial_neg] using hb.inv_right
    | add b c hb hc => simpa only [polynomial_add] using hb.mul_right hc
  | neg a ha => simpa only [polynomial_neg] using ha.inv_left
  | add a c ha hc => simpa only [polynomial_add] using ha.mul_left hc

lemma bracket_inv_left (a b : H) (h : Commute a ⁅a,b⁆) : ⁅a⁻¹,b⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_left,← commutatorElement_inv,h.inv_left.inv_right.eq]
  simp only [mul_assoc,inv_mul_cancel,mul_one]

lemma bracket_inv_right (a b : H) (h : Commute b ⁅a,b⁆) : ⁅a,b⁻¹⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,← commutatorElement_inv,h.inv_left.inv_right.eq]
  simp only [mul_assoc,inv_mul_cancel,mul_one]

lemma bracket_mul_left (a c b : H) (h : Commute a ⁅c,b⁆) (hq : Commute ⁅a,b⁆ ⁅c,b⁆) :
    ⁅a*c,b⁆=⁅a,b⁆*⁅c,b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,h.eq]
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hq.symm.eq

lemma bracket_mul_right (a b c : H) (h : Commute b ⁅a,c⁆) :
    ⁅a,b*c⁆=⁅a,b⁆*⁅a,c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅a,b⁆ b ⁅a,c⁆,h.eq]
  group

theorem polynomial_chain (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (a b : FreeAbelianGroup (FreeMonoid α)) :
    ⁅polynomial outside D i j hij a,polynomial outside D j k hjk b⁆=
      polynomial outside D i k hik (a*b) := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of u =>
    induction b using FreeAbelianGroup.induction_on with
    | zero => simp
    | of v =>
      rw [FreeAbelianGroup.of_mul_of,polynomial_of,polynomial_of,polynomial_of]
      exact word_chain outside D u v i j k hij hjk hik
    | neg v hv =>
      rw [polynomial_neg,mul_neg,polynomial_neg,bracket_inv_right _ _ (by
        rw [hv]
        exact polynomial_commute outside D j k i k hjk hik hjk hik.symm _ _),hv]
    | add b c hb hc =>
      rw [polynomial_add,mul_add,polynomial_add,bracket_mul_right _ _ _ (by
        rw [hc]
        exact polynomial_commute outside D j k i k hjk hik hjk hik.symm _ _),hb,hc]
  | neg u hu =>
    rw [polynomial_neg,neg_mul,polynomial_neg,bracket_inv_left _ _ (by
      rw [hu]
      exact polynomial_commute outside D i j i k hij hik hik hij.symm _ _),hu]
  | add a c ha hc =>
    rw [polynomial_add,add_mul,polynomial_add,bracket_mul_left _ _ _ (by
      rw [hc]
      exact polynomial_commute outside D i j i k hij hik hik hij.symm _ _)
      (by rw [ha,hc]; exact polynomial_commute outside D i k i k hik hik hik hik.symm _ _),ha,hc]

end SteinbergWords

end

end OAI
