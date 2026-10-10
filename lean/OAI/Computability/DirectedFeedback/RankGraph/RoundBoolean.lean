import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.FailureEvent

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport DFVSMaxCut.BooleanFourthMoment
open DFVSMaxCut.Analytic

def roundBoolean {n : ℕ} (p : Cube (Fin n) → ℝ) (x : Cube (Fin n)) : ℝ :=
  if (1 : ℝ) / 2 ≤ p x then 1 else 0

theorem roundBoolean_isBoolean {n : ℕ} (p : Cube (Fin n) → ℝ) :
    IsBoolean (roundBoolean p) := by
  intro x
  unfold roundBoolean
  split_ifs <;> simp

theorem roundBoolean_onCoordinates {n : ℕ} (J : Finset (Fin n))
    (p : Cube (Fin n) → ℝ) (hp : OnCoordinates J p) : OnCoordinates J (roundBoolean p) := by
  intro x y h
  unfold roundBoolean
  rw [hp x y h]

theorem rounding_error_le {n : ℕ} (f p : Cube (Fin n) → ℝ) (hf : IsBoolean f) :
    error f (roundBoolean p) ≤ 4 * (𝔼 x, (f x - p x) ^ 2) := by
  unfold error
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro x _
  by_cases heq : f x = roundBoolean p x
  · rw [ite_eq_left heq]
    positivity
  · rw [ite_eq_right heq]
    rcases hf x with hf0 | hf1
    · have hp : (1 : ℝ) / 2 ≤ p x := by
        by_contra h
        exact heq (by rw [hf0]; unfold roundBoolean; rw [ite_eq_right h])
      rw [hf0]
      nlinarith [sq_nonneg (p x - 1 / 2)]
    · have hp : p x < (1 : ℝ) / 2 := by
        by_contra h
        exact heq (by rw [hf1]; unfold roundBoolean; rw [ite_eq_left (le_of_not_gt h)])
      rw [hf1]
      nlinarith [sq_nonneg (p x - 1 / 2)]

theorem friedgut_uniform (b α : ℝ) (hb : 0 ≤ b) (hα : 0 < α) :
    ∃ Jmax : ℕ, ∀ (n : ℕ) (f : Cube (Fin n) → ℝ),
      IsBoolean f → totalInfluence f ≤ b →
      ∃ J : Finset (Fin n), J.card ≤ Jmax ∧
        ∃ g : Cube (Fin n) → ℝ, IsBoolean g ∧ OnCoordinates J g ∧ error f g ≤ α := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * b / α)
  have hKpos : (0 : ℝ) < K + 1 := by positivity
  have hKb : 2 * b ≤ (K + 1 : ℝ) * α := by
    have := (div_lt_iff₀ hα).mp hK
    nlinarith
  let τ : ℝ := α / (2 * 3 ^ K * (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτid : (3 : ℝ) ^ K * τ * (b + 1) = α / 2 := by
    dsimp [τ]
    field_simp
  have hτb : (3 : ℝ) ^ K * τ * b ≤ α / 2 := by
    rw [← hτid]
    exact mul_le_mul_of_nonneg_left (by linarith : b ≤ b + 1) (by positivity)
  refine ⟨Nat.ceil (b / τ ^ 2), ?_⟩
  intro n f hf hIf
  let J := highInfluences f τ
  have hcard : (J.card : ℝ) ≤ b / τ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    exact (highInfluences_card_bound f τ).trans hIf
  refine ⟨J, ?_, roundBoolean (project J f), roundBoolean_isBoolean _,
    roundBoolean_onCoordinates J _ (project_onCoordinates J f), ?_⟩
  · exact_mod_cast hcard.trans (Nat.le_ceil _)
  · have htail := (spectral_tail f K).trans hIf
    have htail' : 8 *
        (∑ s ∈ Finset.univ.filter (fun s => K < degree s), coefficient f s ^ 2) ≤ α := by
      apply (mul_le_mul_iff_of_pos_left hKpos).mp
      nlinarith
    have hlow := lowDiff_sum_outside f hf K τ hτ.le
    have hlow' : 8 * (∑ i ∈ Finset.univ \ J, (𝔼 x, lowDiff f K i x ^ 2)) ≤ α := by
      have hh := mul_le_mul_of_nonneg_left hIf (by positivity : 0 ≤ (3 : ℝ) ^ K * τ)
      dsimp [J]
      nlinarith
    have hproject := project_squared_error_le J f K
    have hround := rounding_error_le f (project J f) hf
    linarith

def cubeEquiv {I J : Type*} (e : I ≃ J) : (I → Bool) ≃ (J → Bool) where
  toFun x := fun j => x (e.symm j)
  invFun y := fun i => y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

theorem cubeEquiv_update {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (x : I → Bool) (i : I) (a : Bool) :
    cubeEquiv e (Function.update x i a) = Function.update (cubeEquiv e x) (e i) a := by
  funext j
  by_cases hj : j = e i
  · subst j; simp [cubeEquiv]
  · have hji : e.symm j ≠ i := by
      intro heq
      apply hj
      simpa using congrArg e heq
    simp [cubeEquiv, hj, hji]

def DependsOn {I : Type*} (J : Finset I) (f : (I → Bool) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

def cubeInfluence {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → ℝ) (i : I) : ℝ :=
  𝔼 x, (f x - f (Function.update x i (!x i))) ^ 2

def cubeError {I : Type*} [Fintype I] [DecidableEq I] (f g : (I → Bool) → ℝ) : ℝ :=
  𝔼 x, if f x = g x then 0 else 1

theorem cubeInfluence_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (f : (J → Bool) → ℝ) (i : I) :
    cubeInfluence (fun x => f (cubeEquiv e x)) i = cubeInfluence f (e i) := by
  apply Fintype.expect_equiv (cubeEquiv e)
  intro x
  simp only [cubeEquiv_update]
  simp [cubeEquiv]

theorem friedgut_finite (b α : ℝ) (hb : 0 ≤ b) (hα : 0 < α) :
    ∃ Jmax : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (f : (I → Bool) → ℝ),
      (∀ x, f x = 0 ∨ f x = 1) → (∑ i, cubeInfluence f i) ≤ b →
      ∃ J : Finset I, J.card ≤ Jmax ∧
        ∃ g : (I → Bool) → ℝ, (∀ x, g x = 0 ∨ g x = 1) ∧
          DependsOn J g ∧ cubeError f g ≤ α := by
  obtain ⟨Jmax, hJmax⟩ := friedgut_uniform b α hb hα
  refine ⟨Jmax, ?_⟩
  intro I _ _ f hf hIf
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : Cube (Fin (Fintype.card I)) → ℝ := fun x => f (cubeEquiv e x)
  have htrans : totalInfluence f' = ∑ i, cubeInfluence f i := by
    unfold totalInfluence
    change (∑ i, cubeInfluence (fun x => f (cubeEquiv e x)) i) = _
    simp_rw [cubeInfluence_reindex]
    exact e.sum_comp (cubeInfluence f)
  obtain ⟨J, hcard, g, hg, hdep, herr⟩ :=
    hJmax (Fintype.card I) f' (fun x => hf _) (htrans ▸ hIf)
  refine ⟨J.map e.toEmbedding, by simpa using hcard,
    (fun x => g (cubeEquiv e.symm x)), (fun x => hg _), ?_, ?_⟩
  · intro x y h
    apply hdep
    intro i hi
    exact h (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  · have heq : cubeError f (fun x => g (cubeEquiv e.symm x)) = error f' g := by
      unfold cubeError error
      apply Fintype.expect_equiv (cubeEquiv e.symm)
      intro x
      have hx : cubeEquiv e (cubeEquiv e.symm x) = x := by funext i; simp [cubeEquiv]
      change (if f x = g (cubeEquiv e.symm x) then (0 : ℝ) else 1) =
        (if f (cubeEquiv e (cubeEquiv e.symm x)) = g (cubeEquiv e.symm x) then 0 else 1)
      rw [hx]
    exact heq ▸ herr

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability

variable {I : Type} [Fintype I] [DecidableEq I]

def merge (J : Finset I) (x y : I → Bool) : I → Bool :=
  fun i => if i ∈ J then x i else y i

def swapOutside (J : Finset I) : ((I → Bool) × (I → Bool)) ≃ ((I → Bool) × (I → Bool)) where
  toFun p := (merge J p.1 p.2, merge J p.2 p.1)
  invFun p := (merge J p.1 p.2, merge J p.2 p.1)
  left_inv p := by ext i <;> by_cases hi : i ∈ J <;> simp [merge, hi]
  right_inv p := by ext i <;> by_cases hi : i ∈ J <;> simp [merge, hi]

theorem expect_merge (J : Finset I) (h : (I → Bool) → ℝ) :
    (𝔼 x, 𝔼 y, h (merge J x y)) = 𝔼 x, h x := by
  calc
    _ = 𝔼 p : (I → Bool) × (I → Bool), h (merge J p.1 p.2) := by
      rw [← Finset.expect_product']; simp
    _ = 𝔼 p : (I → Bool) × (I → Bool), h p.1 := by
      exact (Fintype.expect_equiv (swapOutside J) (fun p => h p.1)
        (fun p => h (merge J p.1 p.2)) (by
          intro p
          congr 1
          funext i
          by_cases hi : i ∈ J <;> simp [swapOutside, merge, hi])).symm
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]; simp

def disagree (a b : ℝ) : ℝ := if a = b then 0 else 1

theorem disagree_triangle (a b c : ℝ) : disagree a c ≤ disagree a b + disagree b c := by
  by_cases hab : a = b
  · subst b; simp [disagree]
  by_cases hbc : b = c
  · subst c; simp [disagree]
  simp only [disagree, ite_eq_right hab, ite_eq_right hbc]
  split_ifs <;> norm_num

theorem restriction_approximation (J : Finset I) (f h : (I → Bool) → ℝ)
    (hh : DependsOn J h) :
    ∃ y, cubeError f (fun x => f (merge J x y)) ≤ 2 * cubeError f h := by
  have hdep (x y : I → Bool) : h x = h (merge J x y) := by
    apply hh
    intro i hi
    simp [merge, hi]
  have hbound : (𝔼 y, cubeError f (fun x => f (merge J x y))) ≤ 2 * cubeError f h := by
    unfold cubeError
    change (𝔼 y, 𝔼 x, disagree (f x) (f (merge J x y))) ≤ _
    calc
      _ ≤ 𝔼 y, 𝔼 x, (disagree (f x) (h x) + disagree (f (merge J x y)) (h (merge J x y))) := by
        apply Finset.expect_le_expect
        intro y _
        apply Finset.expect_le_expect
        intro x _
        have ht := disagree_triangle (f x) (h x) (f (merge J x y))
        simpa [hdep x y, disagree, eq_comm] using ht
      _ = (𝔼 x, disagree (f x) (h x)) + (𝔼 y, 𝔼 x,
          disagree (f (merge J x y)) (h (merge J x y))) := by
        simp_rw [Finset.expect_add_distrib]
        simp
      _ = _ := by
        rw [Finset.expect_comm]
        rw [expect_merge J (fun z => disagree (f z) (h z))]
        change cubeError f h + cubeError f h = 2 * cubeError f h
        ring
  obtain ⟨y, _, hy⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hbound
  exact ⟨y, hy⟩

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability
variable {I : Type} [Fintype I] [DecidableEq I]

def flatAnd {k : ℕ} (x : I × Fin k → Bool) : I → Bool :=
  fun i => andBit (fun a => x (i, a))

theorem flatAnd_expectation (k : ℕ) (f : (I → Bool) → ℝ) :
    (𝔼 x : I × Fin k → Bool, f (flatAnd x)) = (dyadicLaw I k).expectation f := by
  rw [← blockAnd_expectation]
  apply Fintype.expect_equiv (Equiv.curry I (Fin k) Bool)
  intro x
  rfl

def biasedInfluence (k : ℕ) (f : (I → Bool) → ℝ) (i : I) : ℝ :=
  (dyadicLaw I k).expectation (fun x => (f x - f (Function.update x i (!x i))) ^ 2)

omit [Fintype I] in
theorem flatAnd_update_other {k : ℕ} (x : I × Fin k → Bool) (q : I × Fin k)
    (i : I) (hi : i ≠ q.1) :
    flatAnd (Function.update x q (!x q)) i = flatAnd x i := by
  unfold flatAnd
  congr 1
  funext a
  have hia : (i, a) ≠ q := fun h => hi (congrArg Prod.fst h)
  simp [hia]

omit [Fintype I] in
theorem flatAnd_update_cases {k : ℕ} (x : I × Fin k → Bool) (q : I × Fin k) :
    flatAnd (Function.update x q (!x q)) = flatAnd x ∨
    flatAnd (Function.update x q (!x q)) =
      Function.update (flatAnd x) q.1 (!(flatAnd x q.1)) := by
  by_cases h : flatAnd (Function.update x q (!x q)) q.1 = flatAnd x q.1
  · left
    funext i
    by_cases hi : i = q.1
    · simpa [hi] using h
    · exact flatAnd_update_other x q i hi
  · right
    funext i
    by_cases hi : i = q.1
    · subst i
      simp only [Function.update_self]
      cases ha : flatAnd (Function.update x q (!x q)) q.1 <;>
        cases hb : flatAnd x q.1 <;> simp_all
    · rw [Function.update_of_ne hi]
      exact flatAnd_update_other x q i hi

theorem flatAnd_influence_le (k : ℕ) (f : (I → Bool) → ℝ) (q : I × Fin k) :
    cubeInfluence (fun x => f (flatAnd x)) q ≤ biasedInfluence k f q.1 := by
  unfold cubeInfluence biasedInfluence
  rw [← flatAnd_expectation k]
  apply Finset.expect_le_expect
  intro x _
  dsimp only
  obtain h | h := flatAnd_update_cases x q
  · simp only [h, sub_self, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · rw [h]

theorem flatAnd_totalInfluence_le (k : ℕ) (f : (I → Bool) → ℝ) :
    (∑ q : I × Fin k, cubeInfluence (fun x => f (flatAnd x)) q) ≤
      k * ∑ i, biasedInfluence k f i := by
  calc
    _ ≤ ∑ q : I × Fin k, biasedInfluence k f q.1 :=
      Finset.sum_le_sum (fun q _ => flatAnd_influence_le k f q)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [← Finset.mul_sum]

theorem friedgut_dyadic (k : ℕ) (b α : ℝ) (hb : 0 ≤ b) (hα : 0 < α) :
    ∃ Jmax : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → ℝ),
      (∀ x, f x = 0 ∨ f x = 1) → (∑ i, biasedInfluence k f i) ≤ b →
      ∃ J : Finset I, J.card ≤ Jmax ∧ ∃ g : (I → Bool) → ℝ,
        (∀ x, g x = 0 ∨ g x = 1) ∧ DependsOn J g ∧
          (dyadicLaw I k).expectation (fun x => disagree (f x) (g x)) ≤ α := by
  obtain ⟨Jmax, hJmax⟩ := friedgut_finite (k * b) (α / 2) (mul_nonneg (Nat.cast_nonneg _) hb)
    (by positivity)
  refine ⟨Jmax, ?_⟩
  intro I _ _ f hf hIf
  let F : (I × Fin k → Bool) → ℝ := fun x => f (flatAnd x)
  have hIF : (∑ q, cubeInfluence F q) ≤ k * b :=
    (flatAnd_totalInfluence_le k f).trans (mul_le_mul_of_nonneg_left hIf (Nat.cast_nonneg _))
  obtain ⟨L, hL, H, _, hH, herror⟩ := hJmax (I × Fin k) F (fun x => hf _) hIF
  let J : Finset I := L.image Prod.fst
  let K : Finset (I × Fin k) := Finset.univ.filter (fun q => q.1 ∈ J)
  have hHK : DependsOn K H := by
    intro x y hxy
    apply hH
    intro q hq
    apply hxy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  obtain ⟨y, hy⟩ := restriction_approximation K F H hHK
  let g : (I → Bool) → ℝ := fun z => f (merge J z (flatAnd y))
  have hmerge (x : I × Fin k → Bool) :
      flatAnd (merge K x y) = merge J (flatAnd x) (flatAnd y) := by
    funext i
    by_cases hi : i ∈ J <;> simp [flatAnd, merge, K, hi]
  refine ⟨J, (Finset.card_image_le).trans hL, g, (fun x => hf _), ?_, ?_⟩
  · intro x z hxz
    apply congrArg f
    funext i
    by_cases hi : i ∈ J
    · simp [merge, hi, hxz i hi]
    · simp [merge, hi]
  · have heq : cubeError F (fun x => F (merge K x y)) =
        (dyadicLaw I k).expectation (fun z => disagree (f z) (g z)) := by
      unfold cubeError
      change (𝔼 x, disagree (F x) (F (merge K x y))) = _
      simp only [F, hmerge]
      exact flatAnd_expectation k (fun z => disagree (f z) (g z))
    rw [heq] at hy
    linarith

end DirectedFeedback.Junta

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability
variable {I : Type} [Fintype I] [DecidableEq I]

theorem bitValue_boolean (b : Bool) : bitValue b = 0 ∨ bitValue b = 1 := by
  cases b <;> simp [bitValue]

theorem dyadic_coin (k : ℕ) :
    andCoin k = coin ((2 : ℝ)⁻¹ ^ k) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) := by
  apply eq_of_weight_eq
  intro b
  cases b
  · exact andCoin_false k
  · exact andCoin_true k

theorem dyadic_law (k : ℕ) :
    dyadicLaw I k = law ((2 : ℝ)⁻¹ ^ k) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) := by
  simp only [dyadicLaw, law, dyadic_coin]

omit [Fintype I] in
theorem update_insertBit (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    Function.update (insertBit j b x) j (!b) = insertBit j (!b) x := by
  funext i
  by_cases hi : i = j
  · subst i; simp
  · simp [insertBit, hi]

theorem prod_insertBit (p : ℝ) (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    (∏ i, atom p (insertBit j b x i)) = atom p b * ∏ i : {i : I // i ≠ j}, atom p (x i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [insertBit_self, prod_except]
  simp only [insertBit_other]

omit [Fintype I] in
theorem flip_square (f : (I → Bool) → Bool) (hf : Monotone f)
    (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    (bitValue (f (insertBit j b x)) -
      bitValue (f (Function.update (insertBit j b x) j (!(insertBit j b x j)))))^2 =
      discreteDerivative f j x := by
  rw [insertBit_self, update_insertBit, discreteDerivative_eq_indicator f hf]
  have hm : f (insertBit j false x) ≤ f (insertBit j true x) := by
    apply hf
    intro i
    by_cases hi : i = j
    · subst i; simp
    · simp [insertBit, hi]
  cases b <;> cases h0 : f (insertBit j false x) <;> cases h1 : f (insertBit j true x) <;>
    simp_all [bitValue, pivotalEvent, Bool.le_iff_imp]

theorem biasedInfluence_eq (k : ℕ) (f : (I → Bool) → Bool) (hf : Monotone f) (j : I) :
    Junta.biasedInfluence k (fun x => bitValue (f x)) j =
      ∑ x : {i : I // i ≠ j} → Bool,
        (∏ i, atom ((2 : ℝ)⁻¹^k) (x i)) * discreteDerivative f j x := by
  unfold Junta.biasedInfluence
  rw [dyadic_law]
  change (∑ x, (∏ i, atom ((2 : ℝ)⁻¹^k) (x i)) *
    (bitValue (f x) - bitValue (f (Function.update x j (!(x j)))))^2) = _
  rw [sum_split j]
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_insertBit, prod_insertBit, flip_square f hf, flip_square f hf]
  simp only [atom, Bool.false_eq_true, ↓reduceIte]
  ring

theorem dyadic_influences_le_budget (k : ℕ) (f : (I → Bool) → Bool) (hf : Monotone f) :
    (∑ j, Junta.biasedInfluence k (fun x => bitValue (f x)) j) ≤ budget f := by
  simp_rw [biasedInfluence_eq k f hf]
  exact influence_le_budget f hf _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem boolean_dyadic_junta (k : ℕ) (B γ : ℝ) (hB : 0 ≤ B) (hγ : 0 < γ) :
    ∃ Jmax : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool),
      Monotone f → budget f ≤ B →
      ∃ J : Finset I, J.card ≤ Jmax ∧ ∃ g : (I → Bool) → Bool,
        (∀ x y, (∀ i ∈ J, x i = y i) → g x = g y) ∧
          (law ((2 : ℝ)⁻¹^k) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))).probability
            (fun x => decide (f x ≠ g x)) ≤ γ := by
  obtain ⟨Jmax, hJmax⟩ := Junta.friedgut_dyadic k B γ hB hγ
  refine ⟨Jmax, ?_⟩
  intro I _ _ f hf hbf
  obtain ⟨J,hJ,g,hg,hdep,herr⟩ := hJmax I (fun x => bitValue (f x))
    (fun x => bitValue_boolean (f x)) ((dyadic_influences_le_budget k f hf).trans hbf)
  let g' : (I → Bool) → Bool := fun x => decide (g x = 1)
  refine ⟨J,hJ,g',?_,?_⟩
  · intro x y hxy
    simp only [g', hdep x y hxy]
  · rw [probability_eq_expectation, ← dyadic_law]
    convert herr using 1
    apply expectation_congr
    intro x
    obtain hx | hx := hg x <;> cases hfx : f x <;>
      simp [g', Junta.disagree, bitValue, hx]

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution

def DyadicJuntaBound (M : ℕ) (B γ : ℝ) (Jmax : ℕ) : Prop :=
  ∀ k : Fin (M+2), ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool),
    Monotone f → budget f ≤ B →
    ∃ J : Finset I, J.card ≤ Jmax ∧ ∃ g : (I → Bool) → Bool,
      (∀ x y, (∀ i ∈ J, x i = y i) → g x = g y) ∧
      (law ((2:ℝ)⁻¹^k.val) (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num))).probability
          (fun x => decide (f x ≠ g x)) ≤ γ

theorem uniform_dyadic_junta (M : ℕ) (B γ : ℝ) (hB : 0 ≤ B) (hγ : 0 < γ) :
    ∃ Jmax : ℕ, 1 ≤ Jmax ∧ DyadicJuntaBound M B γ Jmax := by
  have h := fun k : Fin (M+2) => boolean_dyadic_junta k.val B γ hB hγ
  choose J hJ using h
  refine ⟨1 + ∑ k, J k, by omega, ?_⟩
  intro k I _ _ f hf hb
  obtain ⟨S,hS,g,hg,herr⟩ := hJ k I f hf hb
  refine ⟨S, ?_,g,hg,herr⟩
  have hh : J k ≤ ∑ j : Fin (M+2), J j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

theorem family_dyadic_junta {M Jmax : ℕ} {B γ : ℝ}
    (hJ : DyadicJuntaBound M B γ Jmax) (k : Fin (M+2))
    {Ω U I : Type} [Fintype I] [DecidableEq I]
    (f : Ω → U → (I → Bool) → Bool) (hf : ∀ ω u, Monotone (f ω u)) :
    ∃ (S : Ω → U → Finset I) (g : Ω → U → (I → Bool) → Bool),
      (∀ ω u, (S ω u).card ≤ Jmax) ∧
      (∀ ω u x y, (∀ i ∈ S ω u, x i = y i) → g ω u x = g ω u y) ∧
      (∀ ω u, budget (f ω u) ≤ B →
        (law ((2:ℝ)⁻¹^k.val) (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num))).probability
            (fun x => decide (f ω u x ≠ g ω u x)) ≤ γ) := by
  have hex (ω : Ω) (u : U) : ∃ S : Finset I, S.card ≤ Jmax ∧
      ∃ g : (I → Bool) → Bool,
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (budget (f ω u) ≤ B →
          (law ((2:ℝ)⁻¹^k.val) (by positivity)
            (pow_le_one₀ (by norm_num) (by norm_num))).probability
              (fun x => decide (f ω u x ≠ g x)) ≤ γ) := by
    by_cases hb : budget (f ω u) ≤ B
    · obtain ⟨S,hS,g,hg,herr⟩ := hJ k I (f ω u) (hf ω u) hb
      exact ⟨S,hS,g,hg,fun _ => herr⟩
    · exact ⟨∅,by simp,fun _ => false,by simp,fun h => (hb h).elim⟩
  choose S hS g hg herr using hex
  exact ⟨S,g,hS,hg,herr⟩

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem product_pattern_lipschitz {a b c d ε δ : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hb1 : b ≤ 1) (hε : |a-c| ≤ ε) (hδ : |b-d| ≤ δ) :
    |a*(1-b)-c*(1-d)| ≤ ε + δ := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  calc
    _ = |(a-c)*(1-b) + c*(d-b)| := by congr 1; ring
    _ ≤ |a-c| *|1-b| + |c| *|d-b| := by simpa only [abs_mul] using abs_add_le ((a-c)*(1-b)) (c*(d-b))
    _ = |a-c| *(1-b) + c*|b-d| := by rw [abs_of_nonneg (by linarith : 0 ≤ 1-b), abs_of_nonneg hc, abs_sub_comm d b]
    _ ≤ ε*(1-b) + c*δ := add_le_add (mul_le_mul_of_nonneg_right hε (by linarith))
      (mul_le_mul_of_nonneg_left hδ hc)
    _ ≤ ε + δ := by nlinarith [mul_nonneg hε0 hb, mul_nonneg (sub_nonneg.mpr hc1) hδ0]

theorem comparison_juntas (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (J : Finset X) (K : Finset Y) (hJK : Disjoint (J.image (fun x => (e x).1)) K)
    (f f' : (X → Bool) → Bool) (g g' : (Y → Bool) → Bool)
    (hf' : Uses J f') (hg' : Uses K g') (γ : ℝ)
    (hf : (Pivotal.law p hp0 (by linarith)).probability (fun x => decide (f x ≠ f' x)) ≤ γ)
    (hg : (Pivotal.law (2*p) (by positivity) (by linarith)).probability (fun y => decide (g y ≠ g' y)) ≤ γ) :
    |(Pivotal.law p hp0 (by linarith)).probability f *
      (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability g) -
      (law p hp0 hp).probability (fun z => f (bigBits e z) && !(g (smallBits z)))| ≤ 4*γ := by
  let μ := Pivotal.law (I := X) p hp0 (by linarith)
  let ν := Pivotal.law (I := Y) (2*p) (by positivity) (by linarith)
  let ρ := law (Y := Y) p hp0 hp
  have hprod : |μ.probability f * (1-ν.probability g) -
      μ.probability f' * (1-ν.probability g')| ≤ 2*γ := by
    have h := product_pattern_lipschitz (probability_nonnegative ν g)
      (probability_nonnegative μ f') (probability_le_one μ f') (probability_le_one ν g)
      ((probability_abs_sub_le_disagree μ f f').trans hf)
      ((probability_abs_sub_le_disagree ν g g').trans hg)
    linarith
  have hc := pair_event_disagree ρ (fun z => f (bigBits e z)) (fun z => f' (bigBits e z))
    (fun z => !(g (smallBits z))) (fun z => !(g' (smallBits z)))
  have hnot : (fun z : Y → Block => decide ((!g (smallBits z)) ≠ (!g' (smallBits z)))) =
      fun z => decide (g (smallBits z) ≠ g' (smallBits z)) := by
    funext z; simp
  rw [hnot] at hc
  change |_ - _| ≤ (law p hp0 hp).probability (fun z => (fun x => decide (f x ≠ f' x)) (bigBits e z)) +
    (law p hp0 hp).probability (fun z => (fun y => decide (g y ≠ g' y)) (smallBits z)) at hc
  rw [big_probability e p hp0 hp (fun x => decide (f x ≠ f' x)),
    small_probability p hp0 hp (fun y => decide (g y ≠ g' y))] at hc
  have hcc : |ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z))) -
      ρ.probability (fun z => f' (bigBits e z) && !(g' (smallBits z)))| ≤ 2*γ := by
    linarith
  have heq := disjoint_pattern e p hp0 hp J K hJK f' g' hf' hg'
  change ρ.probability (fun z => f' (bigBits e z) && !(g' (smallBits z))) =
    μ.probability f' * (1 - ν.probability g') at heq
  change |μ.probability f * (1-ν.probability g) -
      ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z)))| ≤ _
  calc
    _ ≤ |μ.probability f * (1-ν.probability g) - μ.probability f' * (1-ν.probability g')| +
      |μ.probability f' * (1-ν.probability g') -
        ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z)))| := abs_sub_le _ _ _
    _ ≤ 4*γ := by
      have hc' : |μ.probability f' * (1-ν.probability g') -
          ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z)))| ≤ 2*γ := by
        rw [← heq, abs_sub_comm]
        exact hcc
      linarith

end DirectedFeedback.Coupling

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Soundness
open DirectedFeedback.SourceProbability FiniteDistribution
open Games
variable {Ω U V E X Y : Type} [Fintype Ω] [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem averaged_comparison (μ : FiniteDistribution Ω) (G : Game U V E X Y)
    (θ : ℝ) (hsound : G.Sound θ) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (p γ C : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hγ : 0 < γ) (hC : 0 < C)
    (f : Ω → U → (X → Bool) → Bool) (g : Ω → V → (Y → Bool) → Bool)
    (Bu : Ω → U → ℝ) (Bv : Ω → V → ℝ)
    (hBu0 : ∀ ω u, 0 ≤ Bu ω u) (hBv0 : ∀ ω v, 0 ≤ Bv ω v)
    (hBu : (μ.product G.edgeLaw).expectation (fun a => Bu a.1 (G.left a.2)) ≤ C)
    (hBv : (μ.product G.edgeLaw).expectation (fun a => Bv a.1 (G.right a.2)) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) (Ju : Ω → U → Finset X) (Jv : Ω → V → Finset Y)
    (f' : Ω → U → (X → Bool) → Bool) (g' : Ω → V → (Y → Bool) → Bool)
    (hJu : ∀ ω u, (Ju ω u).card ≤ J) (hJv : ∀ ω v, (Jv ω v).card ≤ J)
    (hf' : ∀ ω u, Uses (Ju ω u) (f' ω u)) (hg' : ∀ ω v, Uses (Jv ω v) (g' ω v))
    (hf : ∀ ω u, Bu ω u ≤ C/γ →
      (Pivotal.law p hp0 (by linarith)).probability (fun x => decide (f ω u x ≠ f' ω u x)) ≤ γ)
    (hg : ∀ ω v, Bv ω v ≤ C/γ →
      (Pivotal.law (2*p) (by positivity) (by linarith)).probability
        (fun y => decide (g ω v y ≠ g' ω v y)) ≤ γ) :
    (μ.product G.edgeLaw).expectation (fun a =>
      (Pivotal.law p hp0 (by linarith)).probability (f a.1 (G.left a.2)) *
        (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability (g a.1 (G.right a.2)))) ≤
    (μ.product G.edgeLaw).expectation (fun a =>
      (Coupling.law p hp0 hp).probability (fun z =>
        f a.1 (G.left a.2) (Coupling.bigBits (fiber a.2) z) &&
          !(g a.1 (G.right a.2) (Coupling.smallBits z)))) + 2*γ + θ*(J:ℝ)^2 + 4*γ := by
  let μc := μ.product G.edgeLaw
  let bU : Ω × E → Bool := fun a => decide (C/γ < Bu a.1 (G.left a.2))
  let bV : Ω × E → Bool := fun a => decide (C/γ < Bv a.1 (G.right a.2))
  let meet : Ω × E → Bool := fun a =>
    decide (∃ x ∈ Ju a.1 (G.left a.2), G.project a.2 x ∈ Jv a.1 (G.right a.2))
  have hU : μc.probability bU ≤ γ := by
    have hh := markov_bound μc (fun a => Bu a.1 (G.left a.2)) (fun a => hBu0 _ _)
      (C/γ) (div_pos hC hγ)
    have he : C / (C/γ) = γ := by field_simp
    exact hh.trans ((div_le_div_of_nonneg_right hBu (by positivity)).trans_eq he)
  have hV : μc.probability bV ≤ γ := by
    have hh := markov_bound μc (fun a => Bv a.1 (G.right a.2)) (fun a => hBv0 _ _)
      (C/γ) (div_pos hC hγ)
    have he : C / (C/γ) = γ := by field_simp
    exact hh.trans ((div_le_div_of_nonneg_right hBv (by positivity)).trans_eq he)
  have hmeet : μc.probability meet ≤ θ*(J:ℝ)^2 := by
    rw [probability_eq_expect, expectation_product]
    simp_rw [← probability_eq_expect]
    change μ.expectation (fun ω => G.edgeLaw.probability (fun e =>
      decide (∃ x ∈ Ju ω (G.left e), G.project e x ∈ Jv ω (G.right e)))) ≤ _
    calc
      _ ≤ μ.expectation (fun _ => θ*(J:ℝ)^2) := expectation_mono _
        (fun ω => list_decoding G θ hsound (Ju ω) (Jv ω) J hJ (hJu ω) (hJv ω))
      _ = _ := expectation_const _ _
  let A : Ω × E → ℝ := fun a =>
    (Pivotal.law p hp0 (by linarith)).probability (f a.1 (G.left a.2)) *
      (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability (g a.1 (G.right a.2)))
  let B : Ω × E → ℝ := fun a =>
    (Coupling.law p hp0 hp).probability (fun z => f a.1 (G.left a.2) (Coupling.bigBits (fiber a.2) z) &&
      !(g a.1 (G.right a.2) (Coupling.smallBits z)))
  have hA1 (a : Ω × E) : A a ≤ 1 := by
    have h0 := probability_nonnegative (Pivotal.law (I := Y) (2*p) (by positivity) (by linarith))
      (g a.1 (G.right a.2))
    have h1 := probability_le_one (Pivotal.law (I := Y) (2*p) (by positivity) (by linarith))
      (g a.1 (G.right a.2))
    have hh := probability_le_one (Pivotal.law (I := X) p hp0 (by linarith)) (f a.1 (G.left a.2))
    exact (mul_le_mul_of_nonneg_right hh (by linarith)).trans (by simpa using h0)
  have hB0 (a : Ω × E) : 0 ≤ B a := probability_nonnegative _ _
  have hpoint (a : Ω × E) : A a ≤ B a + 4*γ +
      (if bU a then 1 else 0) + (if bV a then 1 else 0) + (if meet a then 1 else 0) := by
    by_cases hu : Bu a.1 (G.left a.2) ≤ C/γ
    · by_cases hv : Bv a.1 (G.right a.2) ≤ C/γ
      · by_cases hm : ∃ x ∈ Ju a.1 (G.left a.2), G.project a.2 x ∈ Jv a.1 (G.right a.2)
        · simp only [bU, bV, meet, not_lt.mpr hu, not_lt.mpr hv, hm, decide_false, decide_true,
            Bool.false_eq_true, ↓reduceIte, add_zero]
          linarith [hA1 a, hB0 a]
        · have hd : Disjoint ((Ju a.1 (G.left a.2)).image (fun x => (fiber a.2 x).1))
              (Jv a.1 (G.right a.2)) := by
            rw [Finset.disjoint_left]
            intro y hy hy'
            obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
            exact hm ⟨x,hx, by simpa [hproj] using hy'⟩
          have hh := Coupling.comparison_juntas (fiber a.2) p hp0 hp _ _ hd _ _ _ _
            (hf' _ _) (hg' _ _) γ (hf _ _ hu) (hg _ _ hv)
          have hh' : A a - B a ≤ 4*γ := (le_abs_self _).trans hh
          simpa only [bU, bV, meet, not_lt.mpr hu, not_lt.mpr hv, hm, decide_false,
            Bool.false_eq_true, ↓reduceIte, add_zero] using (show A a ≤ B a + 4*γ by linarith)
      · have hv' := lt_of_not_ge hv
        simp only [bU, bV, not_lt.mpr hu, hv', decide_false, decide_true,
          Bool.false_eq_true, ↓reduceIte, add_zero]
        split_ifs <;> linarith [hA1 a, hB0 a]
    · have hu' := lt_of_not_ge hu
      simp only [bU, hu', decide_true, ↓reduceIte]
      split_ifs <;> linarith [hA1 a, hB0 a]
  have hh := expectation_mono μc hpoint
  simp only [expectation_add, expectation_const, ← probability_eq_expect] at hh
  change μc.expectation A ≤ μc.expectation B + 2*γ + θ*(J:ℝ)^2 + 4*γ
  linarith

end DirectedFeedback.Soundness

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero M] in
theorem double_bias (i : Fin M) : 2*bias i = (2:ℝ)⁻¹^(i.val+1) := by
  unfold bias
  rw [show i.val+2 = (i.val+1)+1 by omega, pow_succ]
  ring

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def bigAcceptance (fallback : X) (i : Fin M) (a : Common U X M T N × E) : ℝ :=
  (subsetLaw i).probability (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.left a.2))

def smallAcceptance (fallback : Y) (i : Fin M) (a : Common U X M T N × E) : ℝ :=
  (Pivotal.law (2*bias i) (mul_nonneg (by norm_num) (bias_pos i).le) (by linarith [bias_le_quarter i])).probability
    (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.right a.2))

def bigBudget (fallback : X) (a : Common U X M T N × E) : ℝ :=
  budget (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.left a.2))

def smallBudget (fallback : Y) (a : Common U X M T N × E) : ℝ :=
  budget (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.right a.2))

theorem independent_comparison (fallbackX : X) (fallbackY : Y) (i : Fin M)
    (D K ρ γ θ : ℝ) (hD : 0 ≤ D) (hK : 0 < K) (hγ : 0 < γ)
    (hsound : G.Sound θ) (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (J : ℕ) (hJ : 1 ≤ J) (hJunta : DyadicJuntaBound M ((D+1)/γ) γ J)
    (hBu : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (bigBudget G ψLaw hYX fiber deleted ord hord hrank fallbackX) ≤ D+1)
    (hBv : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (smallBudget G ψLaw hYX fiber deleted ord hord hrank fallbackY) ≤ D+1)
    (hcost : K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D)
    (hbU : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬bigGood G ψLaw ord a.1 (G.left a.2))) ≤ ρ)
    (hbV : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬smallGood G ψLaw ord a.1 (G.right a.2))) ≤ ρ) :
    ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
      bigAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackX i a *
        (1-smallAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackY i a)) ≤
      2*ρ + M*(2:ℝ)^T*D/K + 6*γ + θ*(J:ℝ)^2 := by
  let f := bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX
  let g := smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY
  have hfm : ∀ d u, Monotone (f d u) := fun d u =>
    (bigFunction_properties G ψLaw hYX fiber deleted ord hord hrank fallbackX d u).1
  have hgm : ∀ d v, Monotone (g d v) := fun d v =>
    (smallFunction_properties G ψLaw hYX fiber deleted ord hord hrank fallbackY d v).1
  obtain ⟨Ju,fu,hJu,hfu,hEu⟩ := family_dyadic_junta hJunta
    ⟨i.val+2,by have := i.isLt; omega⟩ f hfm
  obtain ⟨Jv,gv,hJv,hgv,hEv⟩ := family_dyadic_junta hJunta
    ⟨i.val+1,by have := i.isLt; omega⟩ g hgm
  have hh := Soundness.averaged_comparison (common G ψLaw) G θ hsound fiber hproj
    (bias i) γ (D+1) (bias_pos i).le (by linarith [bias_le_quarter i]) hγ (by linarith)
    f g (fun d u => budget (f d u)) (fun d v => budget (g d v))
    (fun d u => budget_nonneg _) (fun d v => budget_nonneg _) hBu hBv
    J hJ Ju Jv fu gv hJu hJv hfu hgv hEu (by
      intro d v hv
      simpa only [double_bias] using hEv d v hv)
  have hc := comparison_charge G ψLaw hYX fiber deleted ord hord hrank
    fallbackX fallbackY i D K ρ hK hcost hbU hbV
  change _ ≤ _ at hh
  change _ ≤ _ at hc
  have he : ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
      bigAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackX i a *
        (1-smallAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackY i a)) ≤
      ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
        (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
          (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a)) +
        2*γ + θ*(J:ℝ)^2 + 4*γ := hh
  linarith

end DirectedFeedback.Construction

namespace DirectedFeedback

theorem transGen_loop_walk {V : Type*} {R : V → V → Prop} {a : V}
    (h : Relation.TransGen R a a) :
    ∃ (n : ℕ) (f : Fin (n + 1) → V), CyclicWalk R f := by
  obtain ⟨b, hab, hba⟩ := Relation.TransGen.head'_iff.mp h
  obtain ⟨l, hl, hend⟩ := List.exists_isChain_cons_of_relationReflTransGen hba
  have hc : List.IsChain R (a :: b :: l) := .cons_cons hab hl
  let f : Fin (l.length + 1) → V := fun i => (a :: b :: l)[i.val]'(by simp)
  refine ⟨l.length, f, ?_⟩
  intro i
  have hedge := List.isChain_iff_getElem.mp hc i.val (by simp; have := i.isLt; omega)
  by_cases hi : i.val + 1 < l.length + 1
  · simpa only [f, Fin.val_add_one_of_lt' hi] using hedge
  · have hilast : i.val = l.length := by have := i.isLt; omega
    have hwrap : i + 1 = 0 := by apply Fin.ext; simp [Fin.val_add, hilast]
    have he : (a :: b :: l)[i.val + 1]'(by simp; have := i.isLt; omega) = a := by
      have hlast : (a :: b :: l).getLast (by simp) = a := by
        simpa using hend
      rw [List.getLast_eq_getElem] at hlast
      simpa [hilast] using hlast
    simpa only [f, hwrap, Fin.val_zero, List.getElem_cons_zero, he] using hedge

theorem exists_topological_order {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (F : Finset V) (hF : FeedbackR R F) :
    ∃ order : V → ℕ, (∀ a b, a ∉ F → b ∉ F → R a b → order a < order b) ∧
      (∀ a b, a ∉ F → b ∉ F → order a = order b → a = b) := by
  classical
  let S := {v : V // v ∉ F}
  let r : S → S → Prop := fun a b => R a.val b.val
  have hr : ∀ a : S, ¬Relation.TransGen r a a := by
    intro a ha
    obtain ⟨n, f, hf⟩ := transGen_loop_walk ha
    have hw : CyclicWalk R (fun i => (f i).val) := hf
    obtain ⟨i, hi⟩ := feedback_hits_walk R F hF n (fun i => (f i).val) hw
    exact (f i).property hi
  let po : PartialOrder S :=
    { le := Relation.ReflTransGen r
      le_refl a := .refl
      le_trans _ _ _ := Relation.ReflTransGen.trans
      le_antisymm a b hab hba := by
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with heq | hne
        · exact heq.symm
        · exact False.elim (hr a (hne.trans_left hba)) }
  let := po
  let : Fintype (LinearExtension S) := Fintype.ofEquiv S (Equiv.refl _)
  let e := (Fintype.orderIsoFinOfCardEq (LinearExtension S) rfl).symm
  let rank (a : S) : ℕ := (e (toLinearExtension a)).val
  have hlt {a b : S} (h : r a b) : rank a < rank b := by
    apply e.strictMono
    apply (toLinearExtension.monotone (show a ≤ b from Relation.ReflTransGen.single h)).lt_of_ne
    intro heq
    have heq' : a = b := heq
    subst b
    exact hr a (.single h)
  have hinj {a b : S} (h : rank a = rank b) : a = b := by
    have hh := e.injective (Fin.ext h)
    exact hh
  refine ⟨fun a => if ha : a ∉ F then rank ⟨a, ha⟩ else 0, ?_, ?_⟩
  · intro a b ha hb hab
    simpa [ha, hb] using hlt (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hab
  · intro a b ha hb heq
    have hh : rank ⟨a, ha⟩ = rank ⟨b, hb⟩ := by simpa [ha, hb] using heq
    exact congrArg Subtype.val (hinj hh)

end DirectedFeedback

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix

theorem prefixCell_congr {X : Type} (t : ℕ) (P Q : ℕ → Set X)
    (h : ∀ j < t, P j = Q j) : prefixCell t P = prefixCell t Q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext a
    dsimp only [prefixCell]
    rw [ih (fun j hj => h j (by omega)), h t (by omega)]

end DirectedFeedback.Prefix

namespace DirectedFeedback.RankGraph
open DirectedFeedback.SourceProbability.FiniteDistribution Prefix
variable {U V X Y : Type} {T N L : ℕ}

theorem good_take_prefix (ord : Rank U V X Y T N → ℕ) (ψ : Fin L → Fin N)
    (hL : 30 ≤ L) (n : ℕ) (hn : n ≤ T) (s : Fin n → U)
    (hg : Good ord ψ hL (.inl ⟨⟨n,by omega⟩,s⟩)) (t : ℕ) (ht : t ≤ n) :
    Good ord ψ hL (.inl ⟨⟨t,by omega⟩,takePrefix ht s⟩) := by
  induction n with
  | zero => have he : t = 0 := by omega
            subst t
            exact hg
  | succ n ih =>
    by_cases ht' : t ≤ n
    · have hp := good_prefix_big (ord := ord) (ψ := ψ) hL n (by omega) s hg
      exact ih (by omega) (Fin.init s) hp ht'
    · have he : t = n+1 := by omega
      subst t
      exact hg

end DirectedFeedback.RankGraph

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [Fintype U] [Fintype X] [NeZero M] [NeZero T] [Nonempty X] in
theorem cell_takePrefix {t : ℕ} (ht : t ≤ T) (a : PrefixData U X M T) :
    cell (takePrefix ht a) = prefixCell t (sets a) := by
  apply prefixCell_congr
  intro j hj
  simp only [sets, hj, dite_eq_left, takePrefix, lt_of_lt_of_le hj ht]

end DirectedFeedback.Construction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
