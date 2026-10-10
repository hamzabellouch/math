import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.OccurrenceMoment

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

section

lemma prod_sub_one_telescope {R : Type*} [CommRing R] (b : ℕ) (x : Fin b → R) :
    (∏ j, x j)-1 = ∑ j, (x j-1) * ∏ t : Fin b with j<t, x t := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp only [Finset.prod_filter,Fin.prod_univ_succ,Fin.sum_univ_succ,
      Fin.not_lt_zero,ite_false,Fin.succ_pos,ite_true,Fin.succ_lt_succ_iff,one_mul]
    have hs := ih (fun j => x j.succ)
    simp only [Finset.prod_filter] at hs
    rw [← hs]
    ring

variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

abbrev Suffixes {b : ℕ} (c : A → Fin b) := (a : A) × {j : Fin b // c a<j}

def centeredLine {b : ℕ} (f : A → Fin b → L) (c : A → Fin b) : A → L := fun a => f a (c a)

def suffixLine {b : ℕ} (f : A → Fin b → L) (c : A → Fin b) : Suffixes c → L :=
  fun a => f a.1 a.2

omit [Fintype L] in
lemma path_telescope_expansion {b : ℕ} (f : A → Fin b → L) (g : B → L) :
    (∏ a, ((∏ j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ))-1)) *
      (∏ k, MvPolynomial.X (g k)) =
    ∑ c : A → Fin b,
      (∏ a, (MvPolynomial.X (centeredLine f c a)-1)) *
        (∏ k : B ⊕ Suffixes c, MvPolynomial.X (Sum.elim g (suffixLine f c) k)) := by
  simp_rw [prod_sub_one_telescope]
  rw [Fintype.prod_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.prod_mul_distrib,Fintype.prod_sum_type,Fintype.prod_sigma,Sum.elim_inl,Sum.elim_inr,centeredLine,suffixLine]
  have he : ∏ a, ∏ j : Fin b with c a<j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ) =
      ∏ a, ∏ j : {j : Fin b // c a<j}, MvPolynomial.X (f a j) := by
    apply Finset.prod_congr rfl
    intro a _
    exact Finset.prod_subtype _ (by simp) (fun j => MvPolynomial.X (f a j))
  rw [he]
  ring

end

variable {L A B C : Type*} [Fintype L] [Fintype A] [Fintype B] [Fintype C]

omit [Fintype L] in
lemma occurrences_le_of_injective (f : A → L) (g : B → L) (e : A → B)
    (hi : Function.Injective e) (he : ∀ a, g (e a) = f a) (l : L) :
    occurrences f l ≤ occurrences g l := by
  apply Fintype.card_le_of_injective (fun a : {a // f a=l} =>
    (⟨e a, (he a).trans a.property⟩ : {b // g b=l}))
  intro a b h
  exact Subtype.ext (hi (congrArg Subtype.val h))

omit [Fintype L] in
lemma occurrences_sum (f : A → L) (g : B → L) (l : L) :
    occurrences (Sum.elim f g) l = occurrences f l + occurrences g l := by
  have h := Fintype.card_congr (Equiv.subtypeSum (p := fun a : A ⊕ B => Sum.elim f g a=l))
  exact h.trans Fintype.card_sum

variable {b : ℕ}

def telescopeInjection (c : A → Fin b) : A ⊕ (B ⊕ Suffixes c) → B ⊕ (A × Fin b)
  | .inl a => .inr (a,c a)
  | .inr (.inl k) => .inl k
  | .inr (.inr a) => .inr (a.1,a.2)

omit [Fintype A] [Fintype B] in
lemma telescopeInjection_injective (c : A → Fin b) : Function.Injective (telescopeInjection (B:=B) c) := by
  rintro (a | (k | ⟨a,j,hj⟩)) (a' | (k' | ⟨a',j',hj'⟩)) h <;>
    simp only [telescopeInjection,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
      Sum.inr_ne_inl,Prod.mk.injEq] at h
  · exact congrArg Sum.inl h.1
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (lt_irrefl _ hj')
  · exact congrArg (Sum.inr ∘ Sum.inl) h
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (lt_irrefl _ hj)
  · rcases h with ⟨rfl,rfl⟩; rfl

omit [Fintype L] in
lemma telescope_occurrences_le (f : A → Fin b → L) (g : B → L) (c : A → Fin b) (l : L) :
    occurrences (centeredLine f c) l +
      occurrences (Sum.elim g (suffixLine f c)) l ≤
      occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) l := by
  rw [← occurrences_sum]
  apply occurrences_le_of_injective _ _ (telescopeInjection c) (telescopeInjection_injective c)
  rintro (a | (k | a)) <;> rfl

lemma card_suffixes_le (c : A → Fin b) : Fintype.card (Suffixes c) ≤ Fintype.card A * b := by
  apply (Fintype.card_le_of_injective (fun a : Suffixes c => (a.1, a.2.val)) ?_).trans_eq
    (by simp)
  intro a a' h
  obtain ⟨a,j,hj⟩ := a
  obtain ⟨a',j',hj'⟩ := a'
  cases h
  rfl

theorem pathMoment_light (m h : L → ℕ) (f : A → Fin b → L) (g : B → L)
    {η : ℝ} (hm : ∀ l, 0 < m l) (hη0 : 0 ≤ η) (hη : η ≤ 1/4)
    (hl : ∀ l, (h l:ℝ)+
      occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) l ≤ m l*η) :
    let P := (∏ a, ((∏ j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ))-1)) *
      (∏ k, MvPolynomial.X (g k))
    0 ≤ multilineMoment m h P ∧ multilineMoment m h P ≤
      (b:ℝ)^(Fintype.card A) * 2^(Fintype.card B+Fintype.card A*b) *
        (4*Real.sqrt η)^(Fintype.card A) := by
  dsimp only
  rw [path_telescope_expansion,map_sum]
  have hb (c : A → Fin b) := occurrenceMoment_light m h (centeredLine f c)
    (Sum.elim g (suffixLine f c)) hm hη0 hη (fun l => by
      have hn := telescope_occurrences_le f g c l
      have hn' : (occurrences (centeredLine f c) l : ℝ) +
        occurrences (Sum.elim g (suffixLine f c)) l ≤
        occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) l := by exact_mod_cast hn
      linarith [hl l])
  refine ⟨Finset.sum_nonneg (fun c _ => (hb c).1), ?_⟩
  calc
    _ ≤ ∑ c : A → Fin b, (2:ℝ)^(Fintype.card B+Fintype.card A*b) *
        (4*Real.sqrt η)^(Fintype.card A) := by
      apply Finset.sum_le_sum
      intro c _
      apply (hb c).2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      simpa using Nat.add_le_add_left (card_suffixes_le c) (Fintype.card B)
    _ = _ := by simp [Fintype.card_pi,← mul_assoc]

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

lemma fallingMoment_nonneg (m h n : ℕ) : 0≤fallingMoment m h n := by
  unfold fallingMoment
  positivity

lemma fallingMoment_log {m h n : ℕ} (hm : 0 < m) (hn : h+n ≤ m) :
    Real.log (fallingMoment m h n)=fallingCost m (h+n)-fallingCost m h := by
  have hh : h ≤ m := by omega
  have hp : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hnh : n ≤ m-h := by omega
  have hdf : ((m-h).descFactorial n:ℝ)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hnh).ne'
  have hdh : (m.descFactorial h:ℝ)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hh).ne'
  have he : (m-h).descFactorial n * m.descFactorial h=m.descFactorial (h+n) := by
    simpa only [Nat.add_sub_cancel_left] using
      (Nat.descFactorial_mul_descFactorial (show h≤h+n by omega) (n:=m))
  rw [fallingMoment,Real.log_div (pow_ne_zero _ hp) hdf,Real.log_pow,
    fallingCost_formula hm hn,fallingCost_formula hm hh,← he,Nat.cast_mul,
    Real.log_mul hdf hdh,Nat.cast_add]
  ring

lemma fallingMoment_le_exp {m h n : ℕ} (hm : 0 < m) :
    fallingMoment m h n≤Real.exp (h+n) := by
  by_cases hn : h+n ≤ m
  · have hp := fallingMoment_pos hm hn
    rw [← Real.exp_log hp] at ⊢
    apply Real.exp_le_exp.mpr
    rw [fallingMoment_log hm hn]
    have h1 := fallingCost_le hm hn
    have h0 := fallingCost_nonneg hm (show h ≤ m by omega)
    push_cast at h1
    linarith
  · by_cases hn0 : n=0
    · subst n
      simp only [fallingMoment_zero,Nat.cast_zero,add_zero]
      exact Real.one_le_exp (by positivity)
    · have hd : (m-h).descFactorial n=0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp only [fallingMoment,hd,Nat.cast_zero,div_zero]
      exact (Real.exp_pos _).le

end BinaryCoordinateSweeps.Sparse

end

end OAI
