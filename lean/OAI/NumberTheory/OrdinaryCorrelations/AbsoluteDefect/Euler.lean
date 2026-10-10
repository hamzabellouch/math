import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TwistNormLe

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryCorrelations.LocalExpansion
open scoped BigOperators
open Classical

def euler (F : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod F

lemma euler_one (F : ℕ → ℕ → ℂ) : euler F 1 = 1 := by simp [euler]

lemma euler_multiplicative (F : ℕ → ℕ → ℂ) : Multiplicative (euler F) := by
  intro m n hm hn hmn
  simp only [euler,ite_eq_right hm.ne',ite_eq_right hn.ne',ite_eq_right (Nat.mul_pos hm hn).ne',
    Nat.factorization_mul hm.ne' hn.ne']
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors F

lemma euler_bounded (F : ℕ → ℕ → ℂ) (hF : ∀ p k, ‖F p k‖ ≤ 1) :
    OneBounded (euler F) := by
  intro n
  by_cases hn : n = 0
  · simp [euler,hn]
  · simp only [euler,ite_eq_right hn,Finsupp.prod,norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun p _ => hF p _)

lemma euler_primePow (F : ℕ → ℕ → ℂ) (h0 : ∀ p, F p 0 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : euler F (p^k) = F p k := by
  simp only [euler,ite_eq_right (pow_ne_zero k hp.ne_zero),hp.factorization_pow]
  exact Finsupp.prod_single_index (h0 p)

lemma one_or_zero (f : ℕ → ℂ) (hf : Multiplicative f) :
    f 1 = 1 ∨ ∀ n, 0 < n → f n = 0 := by
  by_cases h : f 1 = 1
  · exact Or.inl h
  · right
    intro n hn
    have he := hf 1 n (by omega) hn (by simp)
    simp only [one_mul] at he
    have hz : (1-f 1)*f n = 0 := by linear_combination he
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm h))

lemma factorization_formula (f : ℕ → ℂ) (hf : Multiplicative f) (h1 : f 1 = 1)
    {n : ℕ} (hn : n ≠ 0) : f n = n.factorization.prod (fun p k => f (p^k)) := by
  let g : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else f n,by simp⟩
  have hg : g.IsMultiplicative := ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
    ⟨by simpa [g] using h1,by
      intro m n hm hn hmn
      simp only [g,ArithmeticFunction.coe_mk,ite_eq_right hm,ite_eq_right hn,ite_eq_right (mul_ne_zero hm hn)]
      exact hf m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn⟩
  have he := hg.multiplicative_factorization g hn
  calc
    f n = g n := by simp [g,hn]
    _ = n.factorization.prod (fun p k => g (p^k)) := he
    _ = _ := by
      apply Finsupp.prod_congr
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      change (if p ^ n.factorization p = 0 then 0 else f _) = _
      rw [ite_eq_right (pow_ne_zero _ hprime.ne_zero)]

lemma euler_extend (F : ℕ → ℕ → ℂ) (h0 : ∀ p, F p 0 = 1)
    {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    euler F n = ∏ p ∈ S, F p (n.factorization p) := by
  rw [euler,ite_eq_right hn,Finsupp.prod]
  apply Finset.prod_subset hS
  intro p _ hp
  rw [Finsupp.notMem_support_iff.mp hp,h0]

def patch (S E : Finset ℕ) (B C U : ℕ → ℕ → ℂ) (p k : ℕ) : ℂ :=
  if p ∈ S then if p ∈ E then C p k else B p k else U p k

def summand (S E : Finset ℕ) (B C U : ℕ → ℕ → ℂ) : ℕ → ℂ :=
  euler (patch S E B C U)

lemma summand_bounded (S E : Finset ℕ) (B C U : ℕ → ℕ → ℂ)
    (hB : ∀ p k, ‖B p k‖ ≤ 1) (hC : ∀ p k, ‖C p k‖ ≤ 1)
    (hU : ∀ p k, ‖U p k‖ ≤ 1) : OneBounded (summand S E B C U) := by
  apply euler_bounded
  intro p k
  unfold patch
  split_ifs <;> first | exact hB p k | exact hC p k | exact hU p k

lemma summand_product (S E : Finset ℕ) (B C U : ℕ → ℕ → ℂ)
    (hE : E ⊆ S) (hB : ∀ p, B p 0 = 1) (hC : ∀ p, C p 0 = 1)
    (hU : ∀ p, U p 0 = 1) {n : ℕ} (hn : n ≠ 0) :
    summand S E B C U n =
      (∏ p ∈ S \ E, B p (n.factorization p)) *
      (∏ p ∈ E, C p (n.factorization p)) *
      ∏ p ∈ n.primeFactors \ S, U p (n.factorization p) := by
  have h0 (p : ℕ) : patch S E B C U p 0 = 1 := by simp [patch,hB,hC,hU]
  rw [summand,euler_extend _ h0 hn (S ∪ n.primeFactors) Finset.subset_union_right]
  rw [← Finset.union_sdiff_self_eq_union (s := S) (t := n.primeFactors),
    Finset.prod_union Finset.disjoint_sdiff]
  have hs : S = (S \ E) ∪ E := (Finset.sdiff_union_of_subset hE).symm
  conv_lhs => arg 1; rw [hs,Finset.prod_union Finset.sdiff_disjoint]
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro p hp
      simp only [Finset.mem_sdiff] at hp
      simp [patch,hp.1,hp.2]
    · apply Finset.prod_congr rfl
      intro p hp
      simp [patch,hE hp,hp]
  · apply Finset.prod_congr rfl
    intro p hp
    simp [patch,(Finset.mem_sdiff.mp hp).2]

theorem signed_expansion (S : Finset ℕ) (B C U : ℕ → ℕ → ℂ)
    (hB : ∀ p, B p 0 = 1) (hC : ∀ p, C p 0 = 1)
    (hU : ∀ p, U p 0 = 1) {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ S, (B p (n.factorization p)-C p (n.factorization p))) *
      (∏ p ∈ n.primeFactors \ S, U p (n.factorization p)) =
      ∑ E ∈ S.powerset, (-1:ℂ)^E.card * summand S E B C U n := by
  rw [Finset.prod_sub,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  rw [summand_product S E B C U (Finset.mem_powerset.mp hE) hB hC hU hn]
  ring

def dilation (a : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ := if a ∣ m then f (m/a) else 0

def localA (a : ℕ) (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if a.factorization p ≤ k then f (p^(k-a.factorization p)) else 0

def localB (a : ℕ) (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else localA a f p k

def localC (_ k : ℕ) : ℂ := if k = 0 then 1 else 0

def dilationSummand (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) : ℕ → ℂ :=
  summand a.primeFactors E (localB a f) localC (fun p k => f (p^k))

lemma dilation_union (a : ℕ) (ha : a ≠ 0) (f : ℕ → ℂ)
    (hf : Multiplicative f) (h1 : f 1 = 1) {m : ℕ} (hm : m ≠ 0) :
    dilation a f m = ∏ p ∈ a.primeFactors ∪ m.primeFactors,
      localA a f p (m.factorization p) := by
  by_cases hd : a ∣ m
  · rw [dilation,ite_eq_left hd]
    have ham := (Nat.factorization_le_iff_dvd ha hm).mpr hd
    have hquot : m/a ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd)
      (Nat.pos_of_ne_zero ha)).ne'
    have he := euler_extend (fun p k => f (p^k)) (fun p => by simpa using h1)
      hquot (a.primeFactors ∪ m.primeFactors)
      ((Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd) hm).trans Finset.subset_union_right)
    rw [euler,ite_eq_right hquot,← factorization_formula f hf h1 hquot] at he
    rw [he]
    apply Finset.prod_congr rfl
    intro p _
    simp [localA,ham p,Nat.factorization_div hd]
  · rw [dilation,ite_eq_right hd]
    have hn : ¬ a.factorization ≤ m.factorization :=
      fun h => hd ((Nat.factorization_le_iff_dvd ha hm).mp h)
    rw [Finsupp.le_def] at hn
    push Not at hn
    obtain ⟨p,hp⟩ := hn
    have hpa : p ∈ a.primeFactors := by
      change p ∈ a.factorization.support
      apply Finsupp.mem_support_iff.mpr
      omega
    symm
    apply Finset.prod_eq_zero (Finset.mem_union_left _ hpa)
    simp [localA,not_le.mpr hp]

lemma dilation_product (a : ℕ) (ha : a ≠ 0) (f : ℕ → ℂ)
    (hf : Multiplicative f) (h1 : f 1 = 1) {m : ℕ} (hm : m ≠ 0) :
    dilation a f m =
      (∏ p ∈ a.primeFactors, localA a f p (m.factorization p)) *
      ∏ p ∈ m.primeFactors \ a.primeFactors, f (p^(m.factorization p)) := by
  rw [dilation_union a ha f hf h1 hm,
    ← Finset.union_sdiff_self_eq_union (s := a.primeFactors) (t := m.primeFactors),
    Finset.prod_union Finset.disjoint_sdiff]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hz : a.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hp).2
  simp [localA,hz]

lemma local_sub {a p : ℕ} (f : ℕ → ℂ) (hp : p ∈ a.primeFactors) (k : ℕ) :
    localB a f p k - localC p k = localA a f p k := by
  have hpp : a.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  by_cases hk : k = 0
  · subst k
    simp [localB,localC,localA,hpp]
  · simp [localB,localC,hk]

theorem dilation_expansion (a : ℕ) (ha : 0 < a) (f : ℕ → ℂ)
    (hf : Multiplicative f) (h1 : f 1 = 1) {m : ℕ} (hm : 0 < m) :
    dilation a f m = ∑ E ∈ a.primeFactors.powerset,
      (-1:ℂ)^E.card * dilationSummand a f E m := by
  rw [dilation_product a ha.ne' f hf h1 hm.ne']
  convert signed_expansion a.primeFactors (localB a f) localC (fun p k => f (p^k))
    (by intro p; simp [localB]) (by intro p; simp [localC])
    (by intro p; simpa using h1) hm.ne' using 1
  · congr 1
    apply Finset.prod_congr rfl
    intro p hp
    exact (local_sub f hp _).symm
  · rfl

lemma dilationSummand_bounded (a : ℕ) (f : ℕ → ℂ) (hf : OneBounded f)
    (E : Finset ℕ) : OneBounded (dilationSummand a f E) := by
  apply summand_bounded
  · intro p k
    unfold localB localA
    split_ifs <;> first | exact hf _ | norm_num
  · intro p k
    unfold localC
    split_ifs <;> norm_num
  · intro p k
    exact hf _

lemma dilationSummand_multiplicative (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    Multiplicative (dilationSummand a f E) := euler_multiplicative _

lemma dilationSummand_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationSummand a f E 1 = 1 := euler_one _

lemma dilationSummand_primePow (a : ℕ) (f : ℕ → ℂ) (h1 : f 1 = 1)
    (E : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpa : p ∉ a.primeFactors) (k : ℕ) :
    dilationSummand a f E (p^k) = f (p^k) := by
  have h0 (q : ℕ) : patch a.primeFactors E (localB a f) localC
      (fun p k => f (p^k)) q 0 = 1 := by
    simp [patch,localB,localC,h1]
  change euler _ (p^k) = _
  rw [euler_primePow _ h0 hp k]
  simp [patch,hpa]

theorem dilationSummand_nonpretentious (a : ℕ) (f : ℕ → ℂ) (hf : OneBounded f)
    (h1 : f 1 = 1) (hnp : UniformlyNonpretentious f) (E : Finset ℕ) :
    UniformlyNonpretentious (dilationSummand a f E) := by
  apply PretentiousStability.uniformlyNonpretentious_change f _ hf
    (dilationSummand_bounded a f hf E) a.primeFactors _ hnp
  intro p hp hn
  simpa only [pow_one] using (dilationSummand_primePow a f h1 E hp hn 1).symm

end OrdinaryCorrelations.LocalExpansion

end

end OAI
