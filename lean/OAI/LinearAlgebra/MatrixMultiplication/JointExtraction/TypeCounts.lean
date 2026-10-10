import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexHierarchyTypeCounting
import Mathlib.GroupTheory.GroupAction.Basic

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointTypeCounts

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

section Incidence

variable {G C B : Type*} [Group G] [MulAction G C] [MulAction G B]
  [MulAction.IsPretransitive G C] [MulAction.IsPretransitive G B]
  [Fintype C] [Fintype B]

theorem invariant_incidence_count
    (R : C → B → Prop) [∀ c b, Decidable (R c b)]
    (hR : ∀ (g : G) (c : C) (b : B), R (g • c) (g • b) ↔ R c b)
    (c₀ : C) (b₀ : B) :
    Fintype.card C * Fintype.card {b : B // R c₀ b} =
      Fintype.card B * Fintype.card {c : C // R c b₀} := by
  classical
  have hrow (c : C) : Fintype.card {b : B // R c b} =
      Fintype.card {b : B // R c₀ b} := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G c c₀
    apply Fintype.card_congr
    exact (MulAction.toPerm (β := B) g).subtypeEquiv (fun b => by
      change R c b ↔ R c₀ (g • b)
      rw [← hg]
      exact (hR g c b).symm)
  have hcol (b : B) : Fintype.card {c : C // R c b} =
      Fintype.card {c : C // R c b₀} := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b b₀
    apply Fintype.card_congr
    exact (MulAction.toPerm (β := C) g).subtypeEquiv (fun c => by
      change R c b ↔ R (g • c) b₀
      rw [← hg]
      exact (hR g c b).symm)
  let swap : (Σ c : C, {b : B // R c b}) ≃
      (Σ b : B, {c : C // R c b}) :=
    { toFun := fun x => ⟨x.2.1, x.1, x.2.2⟩
      invFun := fun x => ⟨x.2.1, x.1, x.2.2⟩
      left_inv := fun ⟨c, b, h⟩ => rfl
      right_inv := fun ⟨b, c, h⟩ => rfl }
  simpa only [Fintype.card_sigma, hrow, hcol, Finset.sum_const,
    Finset.card_univ, Nat.nsmul_eq_mul] using Fintype.card_congr swap

theorem invariant_incidence_degree_eq
    (R : C → B → Prop) [∀ c b, Decidable (R c b)]
    (hR : ∀ (g : G) (c : C) (b : B), R (g • c) (g • b) ↔ R c b)
    (c₀ : C) (b₀ : B) :
    (Fintype.card {c : C // R c b₀} : ℝ) =
      (Fintype.card C : ℝ) * Fintype.card {b : B // R c₀ b} /
        Fintype.card B := by
  have : Nonempty B := ⟨b₀⟩
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card B))
  apply (eq_div_iff hB).mpr
  have h := invariant_incidence_count R hR c₀ b₀
  exact_mod_cast (by simpa only [Nat.mul_comm] using h.symm)

theorem invariant_incidence_degree_le_exp
    (R : C → B → Prop) [∀ c b, Decidable (R c b)]
    (hR : ∀ (g : G) (c : C) (b : B), R (g • c) (g • b) ↔ R c b)
    (c₀ : C) (b₀ : B) (candidateRate statisticRate rowRate : ℝ)
    (hC : (Fintype.card C : ℝ) ≤ Real.exp candidateRate)
    (hB : Real.exp statisticRate ≤ (Fintype.card B : ℝ))
    (hrow : (Fintype.card {b : B // R c₀ b} : ℝ) ≤ Real.exp rowRate) :
    (Fintype.card {c : C // R c b₀} : ℝ) ≤
      Real.exp (candidateRate - statisticRate + rowRate) := by
  rw [invariant_incidence_degree_eq R hR c₀ b₀]
  have hnum : (Fintype.card C : ℝ) * Fintype.card {b : B // R c₀ b} ≤
      Real.exp (candidateRate + rowRate) := by
    rw [Real.exp_add]
    exact mul_le_mul hC hrow (Nat.cast_nonneg _) (Real.exp_pos _).le
  calc
    (Fintype.card C : ℝ) * Fintype.card {b : B // R c₀ b} /
        Fintype.card B ≤
      Real.exp (candidateRate + rowRate) / Real.exp statisticRate :=
        div_le_div₀ (Real.exp_pos _).le hnum (Real.exp_pos _) hB
    _ = Real.exp (candidateRate - statisticRate + rowRate) := by
      rw [← Real.exp_sub]
      congr 1
      ring

end Incidence

section FixedClasses

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev FixedClassWords (counts : ∀ c, A c → ℕ) :=
  ∀ c, {w : P c → A c // ∀ a, wordPopulation w a = counts c a}

def fixedWordsEquiv {I B : Type*} [Fintype I] [DecidableEq I]
    [Fintype B] [DecidableEq B] (counts : B → ℕ)
    (hsize : Fintype.card I = ∑ b, counts b) :
    {w : I → B // ∀ b, wordPopulation w b = counts b} ≃ ExactWords counts := by
  classical
  let e : Fin (∑ b, counts b) ≃ I := Fintype.equivOfCardEq (by simpa using hsize.symm)
  exact
    { toFun := fun w => ⟨w.val ∘ e, fun b => by
        rw [wordPopulation_reindex]
        exact w.property b⟩
      invFun := fun w => ⟨w.val ∘ e.symm, fun b => by
        rw [wordPopulation_reindex]
        exact w.property b⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

theorem fixedClassWords_card (counts : ∀ c, A c → ℕ)
    (hsize : ∀ c, Fintype.card (P c) = ∑ a, counts c a) :
    Fintype.card (FixedClassWords P A counts) =
      ∏ c, Nat.multinomial Finset.univ (counts c) := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  exact (Fintype.card_congr (fixedWordsEquiv (counts c) (hsize c))).trans
    (exactWords_card (counts c))

abbrev ClassExactWords (counts : ∀ c, A c → ℕ) := ∀ c, ExactWords (counts c)

theorem classExactWords_card (counts : ∀ c, A c → ℕ) :
    Fintype.card (ClassExactWords A counts) =
      ∏ c, Nat.multinomial Finset.univ (counts c) := by
  classical
  simp only [ClassExactWords, Fintype.card_pi, exactWords_card]

theorem classExactWords_card_pos (counts : ∀ c, A c → ℕ) :
    0 < Fintype.card (ClassExactWords A counts) := by
  rw [classExactWords_card]
  exact Finset.prod_pos fun c _ => Nat.multinomial_pos _ _

theorem classExactWords_card_mul_factorials (counts : ∀ c, A c → ℕ) :
    Fintype.card (ClassExactWords A counts) *
      (∏ c, ∏ a, (counts c a).factorial) =
        ∏ c, (∑ a, counts c a).factorial := by
  rw [classExactWords_card, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  simpa only [mul_comm] using Nat.multinomial_spec Finset.univ (counts c)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] [∀ c, Fintype (A c)] in
theorem fixedClassWords_transitive (counts : ∀ c, A c → ℕ)
    (w v : FixedClassWords P A counts) :
    ∃ e : ∀ c, Equiv.Perm (P c), ∀ c, (w c).val ∘ e c = (v c).val := by
  have he : ∀ c, ∃ e : Equiv.Perm (P c), (w c).val ∘ e = (v c).val := by
    intro c
    apply (samePopulation_iff_permutation (w c).val (v c).val).mp
    intro a
    rw [(w c).property a, (v c).property a]
  choose e he using he
  exact ⟨e, he⟩

theorem log_classExactWords_card (counts : ∀ c, A c → ℕ) :
    Real.log (Fintype.card (ClassExactWords A counts) : ℝ) =
      ∑ c, Real.log (Nat.multinomial Finset.univ (counts c) : ℝ) := by
  rw [classExactWords_card, Nat.cast_prod]
  exact Real.log_prod fun c _ => by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (counts c)))

theorem log_classExactWords_card_eq_factorials (counts : ∀ c, A c → ℕ) :
    Real.log (Fintype.card (ClassExactWords A counts) : ℝ) =
      (∑ c, Real.log ((∑ a, counts c a).factorial : ℝ)) -
        ∑ c, ∑ a, Real.log ((counts c a).factorial : ℝ) := by
  simp only [log_classExactWords_card, log_multinomial, Finset.sum_sub_distrib]

theorem abs_log_classExactWords_card_sub_entropy_le (counts : ∀ c, A c → ℕ) :
    |Real.log (Fintype.card (ClassExactWords A counts) : ℝ) -
      ∑ c, (∑ a, counts c a : ℕ) *
        finiteEntropy (fun a => (counts c a : ℝ) / (∑ b, counts c b : ℕ))| ≤
      ∑ c, ((Fintype.card (A c) : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts c a) + 1 : ℕ)) := by
  rw [log_classExactWords_card, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun c _ => abs_log_multinomial_sub_entropy_le (counts c))

theorem abs_log_fixedClassWords_card_sub_entropy_le (counts : ∀ c, A c → ℕ)
    (hsize : ∀ c, Fintype.card (P c) = ∑ a, counts c a) :
    |Real.log (Fintype.card (FixedClassWords P A counts) : ℝ) -
      ∑ c, (∑ a, counts c a : ℕ) *
        finiteEntropy (fun a => (counts c a : ℝ) / (∑ b, counts c b : ℕ))| ≤
      ∑ c, ((Fintype.card (A c) : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts c a) + 1 : ℕ)) := by
  rw [fixedClassWords_card P A counts hsize, ← classExactWords_card A counts]
  exact abs_log_classExactWords_card_sub_entropy_le A counts

theorem tendsto_log_classExactWords_card_div (counts : ∀ c, A c → ℕ)
    (hpos : ∀ c, 0 < ∑ a, counts c a) :
    Tendsto (fun t : ℕ =>
      Real.log (Fintype.card (ClassExactWords A (fun c a => t * counts c a)) : ℝ) /
        (t : ℝ)) atTop
      (𝓝 (∑ c, (∑ a, counts c a : ℕ) *
        finiteEntropy (fun a => (counts c a : ℝ) / (∑ b, counts c b : ℕ)))) := by
  have hclass (c : C) : Tendsto
      (fun t : ℕ => Real.log (Nat.multinomial Finset.univ
        (fun a => t * counts c a) : ℝ) / (t : ℝ)) atTop
      (𝓝 ((∑ a, counts c a : ℕ) *
        finiteEntropy (fun a => (counts c a : ℝ) / (∑ b, counts c b : ℕ)))) := by
    have hD : ((∑ a, counts c a : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hpos c))
    have h := (tendsto_log_multinomial_mul (counts c) (hpos c)).const_mul
      ((∑ a, counts c a : ℕ) : ℝ)
    convert h using 1
    funext t
    rw [← mul_div_assoc, mul_comm (t : ℝ) ((∑ a, counts c a : ℕ) : ℝ),
      mul_div_mul_left _ _ hD]
  have hsum := tendsto_finsetSum Finset.univ (fun c _ => hclass c)
  simpa only [log_classExactWords_card, Finset.sum_div] using hsum

end FixedClasses

section CoarseFibers

variable {I A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [Fintype B] in
private theorem pushforwardCounts_eq_sum (counts : A → ℕ) (f : A → B) (b : B) :
    pushforwardCounts counts f b = ∑ a, if f a = b then counts a else 0 := by
  classical
  dsimp only [pushforwardCounts]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, ite_false]

abbrev FixedCoarseWords (counts : A → ℕ) (f : A → B) (k : I → B) :=
  {w : I → A // (∀ a, wordPopulation w a = counts a) ∧ ∀ i, f (w i) = k i}

def fixedCoarseWordsEquiv (counts : A → ℕ) (f : A → B) (k : I → B) :
    FixedCoarseWords counts f k ≃
      ConditionalWords k (fun b a => if f a = b then counts a else 0) := by
  classical
  apply Equiv.subtypeEquivRight
  intro w
  constructor
  · rintro ⟨hw, hk⟩ b a
    change Fintype.card {i : I // k i = b ∧ w i = a} =
      if f a = b then counts a else 0
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ← hw a]
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro i
      constructor
      · exact And.right
      · intro hwa
        exact ⟨by rw [← hk i, hwa, hab], hwa⟩
    · rw [ite_eq_right hab]
      have : IsEmpty {i : I // k i = b ∧ w i = a} := ⟨fun i => by
        apply hab
        rw [← i.property.2, hk i.val, i.property.1]⟩
      exact Fintype.card_of_isEmpty
  · intro hw
    constructor
    · intro a
      calc
        wordPopulation w a =
            ∑ b, wordPopulation (fun i : {i // w i = a} => k i.val) b :=
          (wordPopulation_sum _).symm
        _ = ∑ b, Fintype.card {i : I // k i = b ∧ w i = a} := by
          apply Finset.sum_congr rfl
          intro b _
          rw [wordPopulation_fiber]
          exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
        _ = counts a := by simp only [hw]; simp
    · intro i
      by_cases h : f (w i) = k i
      · exact h
      exfalso
      have hzero := hw (k i) (w i)
      simp only [h, ite_false] at hzero
      have hpos : 0 < Fintype.card {j : I // k j = k i ∧ w j = w i} :=
        Fintype.card_pos_iff.mpr ⟨⟨i, rfl, rfl⟩⟩
      exact (Nat.ne_of_gt hpos) hzero

theorem fixedCoarseWords_card (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Fintype.card (FixedCoarseWords counts f k) =
      ∏ b, Nat.multinomial Finset.univ (fun a => if f a = b then counts a else 0) := by
  rw [Fintype.card_congr (fixedCoarseWordsEquiv counts f k)]
  apply conditionalWords_card
  intro b
  rw [← pushforwardCounts_eq_sum]
  exact hk b

theorem fixedCoarseWords_card_pos (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    0 < Fintype.card (FixedCoarseWords counts f k) := by
  rw [fixedCoarseWords_card counts f k hk]
  exact Finset.prod_pos fun b _ => Nat.multinomial_pos _ _

theorem exactWords_card_eq_coarse_mul_fixed (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (pushforwardCounts counts f)) *
        Fintype.card (FixedCoarseWords counts f k) := by
  classical
  have hgraph (b : B) (a : A) :
      pushforwardCounts counts (fun a => (f a, a)) (b, a) =
        if f a = b then counts a else 0 := by
    simp [pushforwardCounts, Prod.mk.injEq, and_comm, ite_and]
  have hinj : Function.Injective (fun a : A => (f a, a)) :=
    fun _ _ h => congrArg Prod.snd h
  have hmain := multinomial_prod_counts
    (pushforwardCounts counts (fun a => (f a, a)))
  rw [multinomial_pushforwardCounts_of_injective counts _ hinj] at hmain
  simp_rw [pushforwardCounts_sum_pair, hgraph] at hmain
  rw [exactWords_card, exactWords_card, fixedCoarseWords_card counts f k hk]
  exact hmain

theorem log_fixedCoarseWords_card (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        Real.log (Nat.multinomial Finset.univ (pushforwardCounts counts f) : ℝ) := by
  have h := congrArg (fun n : ℕ => Real.log (n : ℝ))
    (exactWords_card_eq_coarse_mul_fixed counts f k hk)
  rw [Nat.cast_mul, Real.log_mul] at h
  · simpa only [exactWords_card] using (eq_sub_iff_add_eq.mpr (by linarith :
      Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) +
        Real.log (Fintype.card (ExactWords (pushforwardCounts counts f)) : ℝ) =
          Real.log (Fintype.card (ExactWords counts) : ℝ)))
  · exact_mod_cast (Nat.ne_of_gt (exactWords_card_pos (pushforwardCounts counts f)))
  · exact_mod_cast (Nat.ne_of_gt (fixedCoarseWords_card_pos counts f k hk))

theorem log_fixedCoarseWords_card_eq_factorials
    (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) =
      (∑ b, Real.log ((pushforwardCounts counts f b).factorial : ℝ)) -
        ∑ a, Real.log ((counts a).factorial : ℝ) := by
  rw [log_fixedCoarseWords_card counts f k hk, log_multinomial,
    log_multinomial, pushforwardCounts_sum]
  ring

theorem abs_log_fixedCoarseWords_card_sub_entropy_le
    (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    |Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) -
      (∑ a, counts a : ℕ) *
        (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) -
          finiteEntropy (fun b => (pushforwardCounts counts f b : ℝ) /
            (∑ a, counts a : ℕ)))| ≤
      ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hA := abs_log_multinomial_sub_entropy_le counts
  have hB := abs_log_multinomial_sub_entropy_le (pushforwardCounts counts f)
  rw [pushforwardCounts_sum] at hB
  rw [log_fixedCoarseWords_card counts f k hk]
  have h := (abs_sub
    (Real.log (Nat.multinomial Finset.univ counts : ℝ) -
      (∑ a, counts a : ℕ) *
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))
    (Real.log (Nat.multinomial Finset.univ (pushforwardCounts counts f) : ℝ) -
      (∑ a, counts a : ℕ) *
        finiteEntropy (fun b => (pushforwardCounts counts f b : ℝ) /
          (∑ a, counts a : ℕ)))).trans (add_le_add hA hB)
  convert h using 1 <;> congr 1 <;> ring

theorem card_allowed_over_coarse_le
    (f : A → B) (k : I → B) (allowed : (I → A) → Prop) [DecidablePred allowed]
    (H : ℝ)
    (hcoarse : ∀ w, allowed w → ∀ i, f (w i) = k i)
    (hentropy : ∀ w, allowed w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H) :
    (Fintype.card {w : I → A // allowed w} : ℝ) ≤
      ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) *
          (H - finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) +
          ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
  classical
  let S := {w : I → A // allowed w}
  let T := A → Fin (Fintype.card I + 1)
  let E : ℝ := (Fintype.card I : ℝ) *
    (H - finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) +
    ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
      (1 + Real.log (Fintype.card I + 1 : ℕ))
  let profile : S → T := fun w a =>
    ⟨wordPopulation w.val a,
      Nat.lt_succ_of_le (Fintype.card_subtype_le (fun i : I => w.val i = a))⟩
  have hcap (p : T) :
      (Fintype.card {w : S // profile w = p} : ℝ) ≤ Real.exp E := by
    let Fiber := {w : S // profile w = p}
    by_cases hn : Nonempty Fiber
    · let : Nonempty Fiber := hn
      let w : Fiber := Classical.choice hn
      let counts : A → ℕ := wordPopulation w.val.val
      let encode : Fiber → FixedCoarseWords counts f k := fun v =>
        ⟨v.val.val, ⟨fun a => by
          change wordPopulation v.val.val a = wordPopulation w.val.val a
          exact congrArg Fin.val (congrFun (v.property.trans w.property.symm) a),
          hcoarse v.val.val v.val.property⟩⟩
      have hinj : Function.Injective encode := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : FixedCoarseWords counts f k => z.val) h
      have hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b := by
        have hh := (conditionalWords_nonempty_iff k
          (fun b a => if f a = b then counts a else 0)).mp
            ⟨fixedCoarseWordsEquiv counts f k (encode w)⟩
        intro b
        rw [pushforwardCounts_eq_sum]
        exact hh b
      have htotal : (∑ a, counts a) = Fintype.card I := wordPopulation_sum w.val.val
      have hbound := (abs_le.mp
        (abs_log_fixedCoarseWords_card_sub_entropy_le counts f k hk)).2
      rw [htotal] at hbound
      simp_rw [← hk] at hbound
      have hw := hentropy w.val.val w.val.property
      have hmain := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hw
          (finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)))
        (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ Fintype.card I)
      have hfixed : Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) ≤ E := by
        dsimp only [E]
        change (Fintype.card I : ℝ) *
          (finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) -
            finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) ≤
          _ at hmain
        linarith
      have hpos : (0 : ℝ) < Fintype.card Fiber := Nat.cast_pos.mpr Fintype.card_pos
      have hlog : Real.log (Fintype.card Fiber : ℝ) ≤ E :=
        (Real.log_le_log hpos
          (Nat.cast_le.mpr (Fintype.card_le_of_injective encode hinj))).trans hfixed
      simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
    · let : IsEmpty Fiber := ⟨fun w => hn ⟨w⟩⟩
      change (Fintype.card Fiber : ℝ) ≤ Real.exp E
      simpa only [Fintype.card_of_isEmpty, Nat.cast_zero] using (Real.exp_pos E).le
  have hdecomp : Fintype.card S = ∑ p : T, Fintype.card {w : S // profile w = p} := by
    simpa only [Fintype.card_sigma] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv profile)).symm
  calc
    (Fintype.card S : ℝ) =
        ∑ p : T, (Fintype.card {w : S // profile w = p} : ℝ) := by
      exact_mod_cast hdecomp
    _ ≤ ∑ _p : T, Real.exp E := Finset.sum_le_sum fun p _ => hcap p
    _ = (Fintype.card T : ℝ) * Real.exp E := by simp
    _ = _ := by simp [T, E]

end CoarseFibers

section Windows

theorem card_entropy_bounded_words_le
    {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] (H : ℝ) :
    (Fintype.card {w : I → A //
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H} : ℝ) ≤
      ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) * H +
          ((Fintype.card A : ℝ) + 1) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
  classical
  let S := {w : I → A //
    finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H}
  let T := A → Fin (Fintype.card I + 1)
  let E : ℝ := (Fintype.card I : ℝ) * H +
    ((Fintype.card A : ℝ) + 1) *
      (1 + Real.log (Fintype.card I + 1 : ℕ))
  let profile : S → T := fun w a =>
    ⟨wordPopulation w.val a,
      Nat.lt_succ_of_le (Fintype.card_subtype_le (fun i : I => w.val i = a))⟩
  have hcap (p : T) :
      (Fintype.card {w : S // profile w = p} : ℝ) ≤ Real.exp E := by
    let Fiber := {w : S // profile w = p}
    by_cases hn : Nonempty Fiber
    · let : Nonempty Fiber := hn
      let w : Fiber := Classical.choice hn
      let counts : A → ℕ := wordPopulation w.val.val
      let encode₀ : Fiber → {v : I → A // ∀ a, wordPopulation v a = counts a} :=
        fun v => ⟨v.val.val, fun a => by
          change wordPopulation v.val.val a = wordPopulation w.val.val a
          exact congrArg Fin.val
            (congrFun (v.property.trans w.property.symm) a)⟩
      have hinj₀ : Function.Injective encode₀ := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : {v : I → A // ∀ a, wordPopulation v a = counts a} => z.val) h
      have hsize : Fintype.card I = ∑ a, counts a :=
        (wordPopulation_sum w.val.val).symm
      let encode : Fiber → ExactWords counts :=
        fun v => fixedWordsEquiv (I := I) counts hsize (encode₀ v)
      have hinj : Function.Injective encode :=
        (fixedWordsEquiv (I := I) counts hsize).injective.comp hinj₀
      have hlog := log_card_le_entropy_of_injective_exactWords counts encode hinj
      have htotal : (∑ a, counts a) = Fintype.card I := hsize.symm
      rw [htotal] at hlog
      have hw : finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) ≤ H :=
        w.val.property
      have hmain : (Fintype.card I : ℝ) *
          finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) ≤
          (Fintype.card I : ℝ) * H :=
        mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
      have hlog' : Real.log (Fintype.card Fiber : ℝ) ≤ E := by
        dsimp only [E]
        exact hlog.trans (add_le_add hmain le_rfl)
      have hpos : (0 : ℝ) < Fintype.card Fiber :=
        Nat.cast_pos.mpr Fintype.card_pos
      simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog'
    · let : IsEmpty Fiber := ⟨fun x => hn ⟨x⟩⟩
      change (Fintype.card Fiber : ℝ) ≤ Real.exp E
      simpa only [Fintype.card_of_isEmpty, Nat.cast_zero] using (Real.exp_pos E).le
  have hdecomp : Fintype.card S =
      ∑ p : T, Fintype.card {w : S // profile w = p} := by
    simpa only [Fintype.card_sigma] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv profile)).symm
  calc
    (Fintype.card S : ℝ) =
        ∑ p : T, (Fintype.card {w : S // profile w = p} : ℝ) := by
      exact_mod_cast hdecomp
    _ ≤ ∑ _p : T, Real.exp E := Finset.sum_le_sum (fun p _ => hcap p)
    _ = (Fintype.card T : ℝ) * Real.exp E := by simp
    _ = ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) * H +
          ((Fintype.card A : ℝ) + 1) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
      simp [T, E]

theorem card_class_entropy_bounded_words_le
    {C : Type*} [Fintype C] [DecidableEq C] (P A : C → Type*)
    [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] (H : C → ℝ) :
    (Fintype.card (∀ c, {w : P c → A c //
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card (P c)) ≤ H c}) : ℝ) ≤
      ∏ c, ((Fintype.card (P c) : ℝ) + 1) ^ Fintype.card (A c) *
        Real.exp ((Fintype.card (P c) : ℝ) * H c +
          ((Fintype.card (A c) : ℝ) + 1) *
            (1 + Real.log (Fintype.card (P c) + 1 : ℕ))) := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun c _ => Nat.cast_nonneg _)
    (fun c _ => card_entropy_bounded_words_le (I := P c) (A := A c) (H c))

theorem marginal_coordinate_error {A : Type*} [Fintype A]
    (x y : A → ℝ) (η : ℝ) (h : ∀ a, |x a - y a| ≤ η) :
    |(∑ a, x a) - ∑ a, y a| ≤ (Fintype.card A : ℝ) * η := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a, (x a - y a)| ≤ ∑ a, |x a - y a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : A, η := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp

theorem designated_coordinate_error {I : Type*} [Fintype I]
    (weights actual target : I → ℝ) {χ : ℝ}
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i ≤ 1)
    (hχ : 0 ≤ χ) (herror : ∀ i, |actual i - target i| ≤ χ) :
    |(∑ i, weights i * actual i) - ∑ i, weights i * target i| ≤ χ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ i, weights i * (actual i - target i)| ≤
        ∑ i, |weights i * (actual i - target i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, weights i * |actual i - target i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, weights i * χ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (herror i) (hw i)
    _ ≤ χ := by
      rw [← Finset.sum_mul]
      simpa using mul_le_mul_of_nonneg_right hsum hχ

theorem residual_window_error {mass actual target total targetTotal designated
    targetDesignated η χ : ℝ}
    (hmass : 0 < mass)
    (hactual : mass * actual = total - designated)
    (htarget : mass * target = targetTotal - targetDesignated)
    (htotal : |total - targetTotal| ≤ η)
    (hdesignated : |designated - targetDesignated| ≤ χ) :
    |actual - target| ≤ (η + χ) / mass := by
  apply (le_div_iff₀ hmass).mpr
  calc
    |actual - target| * mass = |mass * (actual - target)| := by
      rw [abs_mul, abs_of_pos hmass, mul_comm]
    _ = |(total - targetTotal) - (designated - targetDesignated)| := by
      rw [mul_sub, hactual, htarget]
      congr 1
      ring
    _ ≤ |total - targetTotal| + |designated - targetDesignated| := abs_sub _ _
    _ ≤ η + χ := add_le_add htotal hdesignated

theorem exists_entropy_window {A : Type*} [Fintype A]
    (p : A → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : A → ℝ,
      (∀ a, |q a - p a| ≤ δ) → |finiteEntropy q - finiteEntropy p| < ε := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_finiteEntropy.continuousAt : ContinuousAt finiteEntropy p) ε hε
  refine ⟨δ / 2, half_pos hδ, fun q hq => ?_⟩
  apply hcont
  rw [dist_pi_lt_iff hδ]
  intro a
  rw [Real.dist_eq]
  exact (hq a).trans_lt (half_lt_self hδ)

theorem exists_window_word_count {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (I : Type*) [Fintype I] [DecidableEq I],
      (Fintype.card {w : I → A //
        ∀ a, |(wordPopulation w a : ℝ) / Fintype.card I - p a| ≤ δ} : ℝ) ≤
        ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
          Real.exp ((Fintype.card I : ℝ) * (finiteEntropy p + ε) +
            ((Fintype.card A : ℝ) + 1) *
              (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
  classical
  obtain ⟨δ, hδ, hwindow⟩ := exists_entropy_window p hε
  refine ⟨δ, hδ, fun I _ _ => ?_⟩
  let encode : {w : I → A //
      ∀ a, |(wordPopulation w a : ℝ) / Fintype.card I - p a| ≤ δ} →
      {w : I → A // finiteEntropy
        (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ finiteEntropy p + ε} :=
    fun w => ⟨w.val, by
      have h := (abs_lt.mp (hwindow _ w.property)).2
      linarith⟩
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun z : {w : I → A // finiteEntropy
        (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ finiteEntropy p + ε} =>
        z.val) h
  exact (Nat.cast_le.mpr (Fintype.card_le_of_injective encode hinj)).trans
    (card_entropy_bounded_words_le (I := I) (finiteEntropy p + ε))

end Windows

end MatrixMultiplication.JointTypeCounts

end

end OAI
