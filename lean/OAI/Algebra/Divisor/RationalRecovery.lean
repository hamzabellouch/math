import Mathlib

namespace OAI

 

 

noncomputable section
open scoped BigOperators

namespace ControlledBoundary
namespace RationalRecovery

 
structure Form (n : ℕ) where
  constant : ℚ
  coeff : Fin n → ℚ

namespace Form

variable {n : ℕ} {K : Type*} [Field K] [CharZero K]

 
def eval (f : Form n) (x : Fin n → K) : K :=
  (f.constant : K) + ∑ j, (f.coeff j : K) * x j

 
def tail (f : Form (n + 1)) : Form n :=
  ⟨f.constant, fun j => f.coeff j.succ⟩

 
def combine (a b : ℚ) (f g : Form n) : Form n :=
  ⟨a * f.constant + b * g.constant, fun j => a * f.coeff j + b * g.coeff j⟩

lemma eval_combine (a b : ℚ) (f g : Form n) (x : Fin n → K) :
    (combine a b f g).eval x = (a : K) * f.eval x + (b : K) * g.eval x := by
  simp only [eval, combine, Rat.cast_add, Rat.cast_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

omit [CharZero K] in
lemma eval_succ (f : Form (n + 1)) (x : Fin (n + 1) → K) :
    f.eval x = (f.coeff 0 : K) * x 0 + f.tail.eval (fun j => x j.succ) := by
  simp only [eval, tail, Fin.sum_univ_succ]
  ring

lemma cast_eval (f : Form n) (q : Fin n → ℚ) :
    ((f.eval q : ℚ) : ℝ) = f.eval (fun j => (q j : ℝ)) := by
  simp [eval]

end Form

 

lemma finite_interval (L U : Finset ℚ)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℚ, (∀ l ∈ L, l ≤ t) ∧ (∀ u ∈ U, t ≤ u) := by
  classical
  by_cases hL : L.Nonempty
  · exact ⟨L.max' hL, fun l hl => L.le_max' l hl,
      fun u hu => L.max'_le hL u (fun l hl => h l hl u hu)⟩
  · have hL' : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    by_cases hU : U.Nonempty
    · exact ⟨U.min' hU, by simp [hL'], fun u hu => U.min'_le u hu⟩
    · have hU' : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      exact ⟨0, by simp [hL'], by simp [hU']⟩

lemma finite_interval_indexed {I J : Type*} [Fintype I] [Fintype J]
    (l : I → ℚ) (u : J → ℚ) (h : ∀ i j, l i ≤ u j) :
    ∃ t : ℚ, (∀ i, l i ≤ t) ∧ (∀ j, t ≤ u j) := by
  classical
  obtain ⟨t, htL, htU⟩ := finite_interval
    (Finset.univ.image l) (Finset.univ.image u) (by
      intro a ha b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      exact h i j)
  exact ⟨t, fun i => htL _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩),
    fun j => htU _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩

 

theorem exists_rat_solution (n : ℕ) {I : Type*} [Fintype I]
    (f : I → Form n) (h : ∃ x : Fin n → ℝ, ∀ i, 0 ≤ (f i).eval x) :
    ∃ q : Fin n → ℚ, ∀ i, 0 ≤ (f i).eval q := by
  classical
  induction n generalizing I with
  | zero =>
    obtain ⟨x, hx⟩ := h
    refine ⟨fun j => Fin.elim0 j, fun i => ?_⟩
    have hi := hx i
    simpa only [Form.eval, Fin.sum_univ_zero, add_zero, Rat.cast_id] using
      (show 0 ≤ (f i).constant from by
        exact_mod_cast (show (0 : ℝ) ≤ ((f i).constant : ℝ) from by
          simpa [Form.eval] using hi))
  | succ n ih =>
    obtain ⟨x, hx⟩ := h
    let Z := {i : I // (f i).coeff 0 = 0}
    let P := {i : I // 0 < (f i).coeff 0}
    let N := {i : I // (f i).coeff 0 < 0}
    let red : Z ⊕ (P × N) → Form n
      | Sum.inl i => (f i.val).tail
      | Sum.inr (p, m) =>
          Form.combine ((f p.val).coeff 0)⁻¹ (-((f m.val).coeff 0)⁻¹)
            (f p.val).tail (f m.val).tail
    let y : Fin n → ℝ := fun j => x j.succ
    have hred : ∀ i, 0 ≤ (red i).eval y := by
      intro i
      rcases i with i | ⟨p, m⟩
      · have hi := hx i.val
        rw [Form.eval_succ, i.property, Rat.cast_zero, zero_mul, zero_add] at hi
        exact hi
      · have hp : (0 : ℝ) < ((f p.val).coeff 0 : ℝ) := by exact_mod_cast p.property
        have hm : ((f m.val).coeff 0 : ℝ) < 0 := by exact_mod_cast m.property
        have hpx := hx p.val
        have hmx := hx m.val
        rw [Form.eval_succ] at hpx hmx
        have hl : -x 0 ≤ (f p.val).tail.eval y / ((f p.val).coeff 0 : ℝ) := by
          apply (le_div_iff₀ hp).mpr
          dsimp only [y]
          nlinarith only [hpx]
        have hu : (f m.val).tail.eval y / ((f m.val).coeff 0 : ℝ) ≤ -x 0 := by
          apply (div_le_iff_of_neg hm).mpr
          dsimp only [y]
          nlinarith only [hmx]
        have he : (red (Sum.inr (p, m))).eval y =
            (f p.val).tail.eval y / ((f p.val).coeff 0 : ℝ) -
              (f m.val).tail.eval y / ((f m.val).coeff 0 : ℝ) := by
          simp only [red, Form.eval_combine, Rat.cast_inv, Rat.cast_neg, div_eq_mul_inv]
          ring
        rw [he]
        linarith only [hl, hu]
    obtain ⟨q, hq⟩ := ih red ⟨y, hred⟩
    let lower (p : P) : ℚ := -(f p.val).tail.eval q / (f p.val).coeff 0
    let upper (m : N) : ℚ := -(f m.val).tail.eval q / (f m.val).coeff 0
    have hcross : ∀ p m, lower p ≤ upper m := by
      intro p m
      have hr := hq (Sum.inr (p, m))
      have he : (red (Sum.inr (p, m))).eval q = upper m - lower p := by
        simp only [red, Form.eval_combine, Rat.cast_id, lower, upper, div_eq_mul_inv]
        ring
      rw [he] at hr
      exact sub_nonneg.mp hr
    obtain ⟨t, htL, htU⟩ := finite_interval_indexed lower upper hcross
    refine ⟨Fin.cons t q, fun i => ?_⟩
    rw [Form.eval_succ]
    simp only [Rat.cast_id, Fin.cons_zero, Fin.cons_succ]
    rcases lt_trichotomy ((f i).coeff 0) 0 with hn | hz | hp
    · have ht := htU ⟨i, hn⟩
      change t ≤ -(f i).tail.eval q / (f i).coeff 0 at ht
      have hb := (le_div_iff_of_neg hn).mp ht
      nlinarith only [hb]
    · have hi := hq (Sum.inl ⟨i, hz⟩)
      change 0 ≤ (f i).tail.eval q at hi
      simpa only [hz, zero_mul, zero_add] using hi
    · have ht := htL ⟨i, hp⟩
      change -(f i).tail.eval q / (f i).coeff 0 ≤ t at ht
      have hb := (div_le_iff₀ hp).mp ht
      nlinarith only [hb]

 
def realify {Prime : Type*} (D : Prime →₀ ℚ) : Prime →₀ ℝ :=
  D.mapRange (fun a : ℚ => (a : ℝ)) (by simp)

@[simp] lemma realify_apply {Prime : Type*} (D : Prime →₀ ℚ) (p : Prime) :
    realify D p = (D p : ℝ) := rfl

 

theorem recover_coefficients {Prime : Type*} {n : ℕ}
    (D : Prime →₀ ℚ) (P : Fin n → Prime →₀ ℚ) (a : Fin n → ℝ)
    (ha : 0 ≤ realify D + ∑ j, a j • realify (P j)) :
    ∃ b : Fin n → ℚ, 0 ≤ D + ∑ j, b j • P j := by
  classical
  let S : Finset Prime := D.support ∪ Finset.univ.biUnion (fun j => (P j).support)
  let forms : S → Form n := fun p => ⟨D p.val, fun j => P j p.val⟩
  have hforms : ∀ p : S, 0 ≤ (forms p).eval a := by
    intro p
    have h := ha p.val
    simpa only [Finsupp.zero_apply, Finsupp.add_apply, realify_apply,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      forms, Form.eval, mul_comm] using h
  obtain ⟨b, hb⟩ := exists_rat_solution n forms ⟨a, hforms⟩
  refine ⟨b, fun p => ?_⟩
  by_cases hp : p ∈ S
  · have h := hb ⟨p, hp⟩
    simpa only [forms, Form.eval, Rat.cast_id, Finsupp.zero_apply, Finsupp.add_apply,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm] using h
  · have hD : D p = 0 := Finsupp.notMem_support_iff.mp (by
      intro h
      exact hp (Finset.mem_union_left _ h))
    have hP : ∀ j, P j p = 0 := by
      intro j
      apply Finsupp.notMem_support_iff.mp
      intro h
      apply hp
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩)
    simp [hD, hP]

 

theorem rational_recovery {Prime Functions : Type*}
    (principal : Functions → Prime →₀ ℚ) (D : Prime →₀ ℚ)
    (h : ∃ E : Prime →₀ ℝ, 0 ≤ E ∧
      ∃ (n : ℕ) (f : Fin n → Functions) (a : Fin n → ℝ),
        E = realify D + ∑ j, a j • realify (principal (f j))) :
    ∃ E : Prime →₀ ℚ, 0 ≤ E ∧
      ∃ (n : ℕ) (f : Fin n → Functions) (b : Fin n → ℚ),
        E = D + ∑ j, b j • principal (f j) := by
  obtain ⟨E, hE, n, f, a, rfl⟩ := h
  obtain ⟨b, hb⟩ := recover_coefficients D (fun j => principal (f j)) a hE
  exact ⟨D + ∑ j, b j • principal (f j), hb, n, f, b, rfl⟩

end RationalRecovery
end ControlledBoundary

end

end OAI
