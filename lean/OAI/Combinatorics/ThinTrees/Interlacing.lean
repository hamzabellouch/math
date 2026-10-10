import OAI.Combinatorics.ThinTrees.OptionalDirections

namespace OAI

universe uα uι uι2 uι3

section

noncomputable section
open Polynomial Finset Set
open scoped Topology
namespace StrongThinTree.MSS.Selection

lemma coeff_prod_negative (s : Multiset ℝ) (hs : ∀r ∈ s, r < 0) :
    (∀k, 0 ≤ ((s.map (fun r => (X-C r : ℝ[X]))).prod).coeff k) ∧
      ∀k ≤ s.card, 0 < ((s.map (fun r => (X-C r : ℝ[X]))).prod).coeff k := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero,Multiset.prod_zero,Multiset.card_zero]
    constructor
    · intro k; simp only [coeff_one]; split_ifs <;> norm_num
    · intro k hk
      have : k=0 := by omega
      subst k
      simp
  | @cons r s ih =>
    have hr : r < 0 := hs r (Multiset.mem_cons_self _ _)
    obtain ⟨hn,hp⟩ := ih (fun a ha => hs a (Multiset.mem_cons_of_mem ha))
    simp only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons]
    constructor
    · intro k
      cases k with
      | zero => simpa only [sub_mul,coeff_sub,coeff_X_mul_zero,coeff_C_mul,zero_sub,neg_mul] using mul_nonneg (neg_nonneg.mpr hr.le) (hn 0)
      | succ k =>
        simp only [sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
        exact sub_nonneg.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg hr.le (hn _)) (hn _))
    · intro k hk
      cases k with
      | zero => simpa only [sub_mul,coeff_sub,coeff_X_mul_zero,coeff_C_mul,zero_sub,neg_mul] using mul_pos (neg_pos.mpr hr) (hp 0 (Nat.zero_le _))
      | succ k =>
        simp only [sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
        exact sub_pos.mpr (lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hr.le (hn _)) (hp k (by omega)))

lemma coeff_pos_of_negative_roots {p : ℝ[X]} (hm : p.Monic) (hs : p.Splits)
    (hr : ∀r ∈ p.roots, r < 0) : ∀k ≤ p.natDegree, 0 < p.coeff k := by
  have hh := (coeff_prod_negative p.roots hr).2
  rw [←hs.eq_prod_roots_of_monic hm] at hh
  simpa only [←hs.natDegree_eq_card_roots] using hh

lemma eval_pos_of_nonneg_coeff {p : ℝ[X]} (hp : ∀k, 0 ≤ p.coeff k) (h0 : 0 < p.coeff 0)
    {x : ℝ} (hx : 0 ≤ x) : 0 < p.eval x := by
  rw [Polynomial.eval_eq_sum]
  apply lt_of_lt_of_le h0
  have hm : 0 ∈ p.support := Polynomial.mem_support_iff.mpr h0.ne'
  simpa only [Polynomial.sum,pow_zero,mul_one] using Finset.single_le_sum
    (fun k _ => mul_nonneg (hp k) (pow_nonneg hx k)) hm

lemma coeff_pos_of_nonneg {p : ℝ[X]} (hm : p.Monic) (hs : p.Splits)
    (hp : ∀k, 0 ≤ p.coeff k) (h0 : 0 < p.coeff 0) :
    ∀k ≤ p.natDegree, 0 < p.coeff k := by
  apply coeff_pos_of_negative_roots hm hs
  intro r hr
  by_contra hh
  exact (eval_pos_of_nonneg_coeff hp h0 (le_of_not_gt hh)).ne'
    ((Polynomial.mem_roots hm.ne_zero).mp hr)

lemma positive_coeff_path {α : Type uα} [TopologicalSpace α] [PreconnectedSpace α]
    (p : α → ℝ[X]) (d : ℕ) (hc : ∀k, Continuous (fun t => (p t).coeff k))
    (hm : ∀t, (p t).Monic) (hs : ∀t, (p t).Splits) (hd : ∀t, (p t).natDegree=d)
    (h0 : ∀t, 0 < (p t).coeff 0) {a : α} (ha : ∀k ≤ d, 0 < (p a).coeff k) :
    ∀t k, k ≤ d → 0 < (p t).coeff k := by
  let C : Set α := {t | ∀k ≤ d, 0 ≤ (p t).coeff k}
  let G : Set α := {t | ∀k ≤ d, 0 < (p t).coeff k}
  have he : C=G := by
    ext t
    constructor
    · intro ht k hk
      have hp : ∀k, 0 ≤ (p t).coeff k := by
        intro k
        by_cases hk' : k ≤ d
        · exact ht k hk'
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega)]
      exact coeff_pos_of_nonneg (hm t) (hs t) hp (h0 t) k (by rwa [hd])
    · exact fun ht k hk => (ht k hk).le
  have hC : IsClosed C := by
    have hh : C=⋂k : Fin (d+1), {t | 0 ≤ (p t).coeff k} := by
      ext t
      simp only [C,Set.mem_ofPred_eq,Set.mem_iInter]
      exact ⟨fun h k => h k (by omega),fun h k hk => h ⟨k,by omega⟩⟩
    rw [hh]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (hc k))
  have hG : IsOpen G := by
    have hh : G=⋂k : Fin (d+1), {t | 0 < (p t).coeff k} := by
      ext t
      simp only [G,Set.mem_ofPred_eq,Set.mem_iInter]
      exact ⟨fun h k => h k (by omega),fun h k hk => h ⟨k,by omega⟩⟩
    rw [hh]
    exact isOpen_iInter_of_finite (fun k => isOpen_lt continuous_const (hc k))
  have heq : G=Set.univ := (IsClopen.eq_univ ⟨he ▸ hC,hG⟩ ⟨a,ha⟩)
  intro t
  have ht : t ∈ G := heq.symm ▸ Set.mem_univ t
  exact ht

lemma monic_segment {p q : ℝ[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (hq : q.IsMonicOfDegree d) (t : ℝ) :
    ((1-t) • p + t • q).IsMonicOfDegree d := by
  rw [isMonicOfDegree_iff]
  constructor
  · exact natDegree_add_le_of_degree_le
      ((natDegree_smul_le _ _).trans hp.natDegree_eq.le)
      ((natDegree_smul_le _ _).trans hq.natDegree_eq.le)
  · rw [coeff_add, coeff_smul, coeff_smul]
    have hp' : p.coeff d=1 := hp.natDegree_eq ▸ hp.monic.coeff_natDegree
    have hq' : q.coeff d=1 := hq.natDegree_eq ▸ hq.monic.coeff_natDegree
    simp only [hp',hq',smul_eq_mul,mul_one]
    ring

lemma negative_roots_segment {p q : ℝ[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (hq : q.IsMonicOfDegree d)
    (hs : ∀t ∈ Set.Icc (0 : ℝ) 1, ((1-t) • p + t • q).Splits)
    (hr : ∀r ∈ p.roots, r < 0) (h0p : 0 < p.coeff 0) (h0q : 0 < q.coeff 0) :
    ∀r ∈ q.roots, r < 0 := by
  let : PreconnectedSpace (Set.Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  let f : Set.Icc (0 : ℝ) 1 → ℝ[X] := fun t => (1-t.val) • p + t.val • q
  have hh := positive_coeff_path f d
    (fun k => by
      simp only [f,coeff_add,coeff_smul,smul_eq_mul]
      fun_prop)
    (fun t => (monic_segment hp hq t).monic)
    (fun t => hs t t.property)
    (fun t => (monic_segment hp hq t).natDegree_eq)
    (fun t => by
      simp only [f,coeff_add,coeff_smul,smul_eq_mul]
      have ht := t.property
      have hh : 0 < (1-t.val)*p.coeff 0+t.val*q.coeff 0 := by
        by_cases ht0 : t.val=0
        · simp [ht0,h0p]
        · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) h0p.le)
            (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) h0q)
      exact hh)
    (a := ⟨0,by simp⟩)
    (by
      simpa only [f,sub_zero,one_smul,zero_smul,add_zero,hp.natDegree_eq] using
        coeff_pos_of_negative_roots hp.monic (by simpa using hs 0 (by simp)) hr)
  have hqpos : ∀k ≤ d, 0 < q.coeff k := by
    simpa only [f,sub_self,zero_smul,one_smul,zero_add] using hh ⟨1,by simp⟩
  intro r hrq
  by_contra hnr
  have hn : ∀k, 0 ≤ q.coeff k := by
    intro k
    by_cases hk : k ≤ d
    · exact (hqpos k hk).le
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hq.natDegree_eq]; omega)]
  exact (eval_pos_of_nonneg_coeff hn h0q (le_of_not_gt hnr)).ne'
    ((mem_roots hq.ne_zero).mp hrq)

lemma roots_shift_iff {p : ℝ[X]} (hp : p ≠ 0) (x r : ℝ) :
    r ∈ (p.comp (X+C x)).roots ↔ r+x ∈ p.roots := by
  rw [mem_roots (comp_X_add_C_ne_zero_iff.mpr hp),mem_roots hp]
  simp [IsRoot,eval_comp]

lemma roots_lt_segment {p q : ℝ[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (hq : q.IsMonicOfDegree d)
    (hs : ∀t ∈ Set.Icc (0 : ℝ) 1, ((1-t) • p + t • q).Splits)
    {x : ℝ} (hr : ∀r ∈ p.roots, r < x) (hxq : 0 < q.eval x) :
    ∀r ∈ q.roots, r < x := by
  have hp' : (p.comp (X+C x)).IsMonicOfDegree d := by
    simpa using hp.comp one_ne_zero (isMonicOfDegree_X_add_one x)
  have hq' : (q.comp (X+C x)).IsMonicOfDegree d := by
    simpa using hq.comp one_ne_zero (isMonicOfDegree_X_add_one x)
  have hrp : ∀r ∈ (p.comp (X+C x)).roots, r < 0 := by
    intro r h
    have hh := hr (r+x) ((roots_shift_iff hp.ne_zero x r).mp h)
    linarith
  have hps : p.Splits := by simpa using hs 0 (by simp)
  have hp0 := coeff_pos_of_negative_roots hp'.monic (hps.comp_X_add_C x) hrp 0 (Nat.zero_le _)
  have hq0 : 0 < (q.comp (X+C x)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]
    simpa using hxq
  have hsr : ∀t ∈ Set.Icc (0 : ℝ) 1,
      ((1-t) • p.comp (X+C x) + t • q.comp (X+C x)).Splits := by
    intro t ht
    simpa only [add_comp,smul_comp] using (hs t ht).comp_X_add_C x
  have hh := negative_roots_segment hp' hq' hsr hrp hp0 hq0
  intro r h
  have hm : r-x ∈ (q.comp (X+C x)).roots := by
    rw [roots_shift_iff hq.ne_zero]
    simpa using h
  have hh' := hh _ hm
  linarith

lemma eval_pos_above_roots {p : ℝ[X]} (hp : p.Monic) (hs : p.Splits)
    {x : ℝ} (hr : ∀r ∈ p.roots, r < x) : 0 < p.eval x := by
  have hshift : ∀r ∈ (p.comp (X+C x)).roots, r < 0 := by
    intro r h
    have hh := hr (r+x) ((roots_shift_iff hp.ne_zero x r).mp h)
    linarith
  have hh := coeff_pos_of_negative_roots (hp.comp_X_add_C x) (hs.comp_X_add_C x)
    hshift 0 (Nat.zero_le _)
  simpa only [coeff_zero_eq_eval_zero,eval_comp,eval_add,eval_X,eval_C,zero_add] using hh

lemma monic_mean {ι : Type uι} [Fintype ι] (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀i, (p i).IsMonicOfDegree d) (w : ι → ℝ) (hw : ∑i, w i=1) :
    (∑i, w i • p i).IsMonicOfDegree d := by
  rw [isMonicOfDegree_iff]
  constructor
  · exact natDegree_sum_le_of_forall_le _ _ (fun i _ =>
      (natDegree_smul_le _ _).trans (hp i).natDegree_eq.le)
  · simp only [finsetSum_coeff,coeff_smul,smul_eq_mul]
    have hh : ∀i, (p i).coeff d=1 := fun i => (hp i).natDegree_eq ▸ (hp i).monic.coeff_natDegree
    simpa only [hh,mul_one] using hw

lemma selection_strict {ι : Type uι2} [Fintype ι] (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀i, (p i).IsMonicOfDegree d) (w : ι → ℝ) (hw : ∀i, 0 < w i)
    (hsum : ∑i, w i=1)
    (hs : ∀i t, t ∈ Set.Icc (0 : ℝ) 1 →
      ((1-t) • (∑j, w j • p j) + t • p i).Splits)
    {x : ℝ} (hroot : ∀r ∈ (∑i, w i • p i).roots, r < x) :
    ∃i, ∀r ∈ (p i).roots, r < x := by
  have hne : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hsum
  let := hne
  have hm := monic_mean p hp w hsum
  have hsplit : (∑i, w i • p i).Splits := by
    simpa using hs (Classical.arbitrary ι) 0 (by simp)
  have he := eval_pos_above_roots hm.monic hsplit hroot
  have hei : ∃i, 0 < (p i).eval x := by
    by_contra! hh
    have hn : ∑i, w i*(p i).eval x ≤ 0 :=
      Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i).le (hh i))
    simp only [eval_finsetSum,eval_smul,smul_eq_mul] at he
    linarith
  obtain ⟨i,hi⟩ := hei
  exact ⟨i,roots_lt_segment hm (hp i) (hs i) hroot hi⟩

lemma selection {ι : Type uι3} [Fintype ι] (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀i, (p i).IsMonicOfDegree d) (w : ι → ℝ) (hw : ∀i, 0 < w i)
    (hsum : ∑i, w i=1)
    (hs : ∀i t, t ∈ Set.Icc (0 : ℝ) 1 →
      ((1-t) • (∑j, w j • p j) + t • p i).Splits)
    {b : ℝ} (hroot : ∀r ∈ (∑i, w i • p i).roots, r ≤ b) :
    ∃i, ∀r ∈ (p i).roots, r ≤ b := by
  classical
  by_contra! hn
  choose r hr hbr using hn
  have hne : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hsum
  let := hne
  have hmin : b < Finset.univ.inf' Finset.univ_nonempty r :=
    (Finset.lt_inf'_iff _).mpr (fun i _ => hbr i)
  obtain ⟨x,hbx,hxmin⟩ := exists_between hmin
  obtain ⟨i,hi⟩ := selection_strict p hp w hw hsum hs (fun a ha => (hroot a ha).trans_lt hbx)
  have hxi : x < r i := hxmin.trans_le (Finset.inf'_le _ (Finset.mem_univ i))
  exact (hi (r i) (hr i)).not_gt hxi

end StrongThinTree.MSS.Selection

end
end

end OAI
