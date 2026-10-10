import OAI.Analysis.MarkovType.FiniteChains
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S : Type*} [sectionFintypeS : Fintype S]

theorem sum_π_mul_P (C : FiniteReversibleChain S) (t : S) :
    ∑ s, C.π s * C.P s t = C.π t := by
  simp_rw [C.balance]
  rw [← Finset.mul_sum, C.sum_P, mul_one]

theorem balance_product (n : ℕ) (m : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (h : ∀ i, m i.castSucc * a i = m i.succ * b i) :
    m 0 * ∏ i, a i = m (Fin.last n) * ∏ i, b i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ht := ih (fun i => m i.succ) (fun i => a i.succ)
        (fun i => b i.succ) (fun i => by
          simpa only [Fin.succ_castSucc] using h i.succ)
      simp only [Fin.succ_last] at ht
      have h0 : m 0 * a 0 = m (Fin.succ 0) * b 0 := by
        simpa only [Fin.castSucc_zero] using h 0
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      calc
        m 0 * (a 0 * ∏ i : Fin n, a i.succ) =
            (m 0 * a 0) * ∏ i : Fin n, a i.succ := by ring
        _ = (m (Fin.succ 0) * b 0) * ∏ i : Fin n, a i.succ := by rw [h0]
        _ = b 0 * (m (Fin.succ 0) * ∏ i : Fin n, a i.succ) := by ring
        _ = b 0 * (m (Fin.last (n + 1)) * ∏ i : Fin n, b i.succ) := by rw [ht]
        _ = m (Fin.last (n + 1)) * (b 0 * ∏ i : Fin n, b i.succ) := by ring

def pathReverse {n : ℕ} (ω : StatePath S n) : StatePath S n :=
  fun i => ω i.rev

omit sectionFintypeS in
@[simp] theorem pathReverse_reverse [Fintype S] {n : ℕ} (ω : StatePath S n) :
    pathReverse (pathReverse ω) = ω := by
  funext i
  simp [pathReverse]

def pathReverseEquiv (n : ℕ) : StatePath S n ≃ StatePath S n where
  toFun := pathReverse
  invFun := pathReverse
  left_inv := pathReverse_reverse
  right_inv := pathReverse_reverse

theorem pathWeight_reverse (C : FiniteReversibleChain S) (n : ℕ)
    (ω : StatePath S n) : pathWeight C n (pathReverse ω) = pathWeight C n ω := by
  have hp := Fin.rev_involutive.bijective.prod_comp
    (fun i : Fin n => C.P (ω i.succ) (ω i.castSucc))
  change (∏ i : Fin n, C.P (ω i.rev.succ) (ω i.rev.castSucc)) =
    ∏ i : Fin n, C.P (ω i.succ) (ω i.castSucc) at hp
  simp only [pathWeight, pathReverse, Fin.rev_zero, Fin.rev_castSucc, Fin.rev_succ]
  rw [hp]
  exact (balance_product n (fun i => C.π (ω i))
    (fun i => C.P (ω i.castSucc) (ω i.succ))
    (fun i => C.P (ω i.succ) (ω i.castSucc))
    (fun i => C.balance _ _)).symm

theorem pathWeight_snoc (C : FiniteReversibleChain S) (n : ℕ)
    (ω : StatePath S n) (t : S) :
    pathWeight C (n + 1) (Fin.snoc ω t) =
      pathWeight C n ω * C.P (ω (Fin.last n)) t := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  have hz : (0 : Fin (n + 1 + 1)) = (0 : Fin (n + 1)).castSucc := rfl
  simp only [hz, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

section VectorExpectations

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

theorem sum_pathWeight_snoc_v (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S (n + 1) → V) :
    (∑ ω, pathWeight C (n + 1) ω • F ω) =
      ∑ η : StatePath S n, ∑ t : S,
        (pathWeight C n η * C.P (η (Fin.last n)) t) • F (Fin.snoc η t) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1 + 1) => S)).sum_comp
    (fun ω => pathWeight C (n + 1) ω • F ω)]
  change (∑ z : S × StatePath S n,
    pathWeight C (n + 1) (Fin.snoc z.2 z.1) • F (Fin.snoc z.2 z.1)) = _
  simp only [Fintype.sum_prod_type, pathWeight_snoc]
  exact Finset.sum_comm

theorem sum_pathWeight_reverse_v (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S n → V) :
    (∑ ω, pathWeight C n ω • F (pathReverse ω)) =
      ∑ ω, pathWeight C n ω • F ω := by
  have h := (pathReverseEquiv (S := S) n).sum_comp
    (fun ω => pathWeight C n ω • F ω)
  change (∑ ω, pathWeight C n (pathReverse ω) • F (pathReverse ω)) = _ at h
  simpa only [pathWeight_reverse] using h

end VectorExpectations

theorem sum_pathWeight_snoc (C : FiniteReversibleChain S) (n : ℕ)
    (F : StatePath S (n + 1) → ℝ) :
    (∑ ω, pathWeight C (n + 1) ω * F ω) =
      ∑ η : StatePath S n, ∑ t : S,
        (pathWeight C n η * C.P (η (Fin.last n)) t) * F (Fin.snoc η t) :=
  sum_pathWeight_snoc_v C n F

theorem sum_pathWeight (C : FiniteReversibleChain S) (n : ℕ) :
    ∑ ω : StatePath S n, pathWeight C n ω = 1 := by
  classical
  induction n with
  | zero =>
      let e : S ≃ StatePath S 0 :=
        { toFun := fun s _ => s
          invFun := fun ω => ω 0
          left_inv := fun _ => rfl
          right_inv := fun ω => funext fun i => congrArg ω (Fin.subsingleton_one.elim _ _) }
      rw [← e.sum_comp (pathWeight C 0)]
      simpa [e, pathWeight] using C.sum_π
  | succ n ih =>
      have h := sum_pathWeight_snoc C n (fun _ => 1)
      simp only [mul_one] at h
      rw [h]
      simp_rw [← Finset.mul_sum, C.sum_P, mul_one]
      exact ih

def pathLaw (C : FiniteReversibleChain S) (n : ℕ) : FiniteLaw (StatePath S n) where
  mass := pathWeight C n
  mass_nonneg := pathWeight_nonneg C n
  sum_mass := sum_pathWeight C n

def pathTake {n : ℕ} (k : ℕ) (hk : k ≤ n) (ω : StatePath S n) : StatePath S k :=
  fun i => ω (Fin.castLE (Nat.add_le_add_right hk 1) i)

def pathPrefix (k m : ℕ) (ω : StatePath S (k + m)) : StatePath S k :=
  pathTake k (Nat.le_add_right k m) ω

omit sectionFintypeS in
@[simp] theorem pathTake_self [Fintype S] {n : ℕ} (ω : StatePath S n) :
    pathTake n le_rfl ω = ω := by
  funext i
  rfl

omit sectionFintypeS in
@[simp] theorem pathTake_snoc [Fintype S] {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (ω : StatePath S n) (t : S) :
    pathTake k (Nat.le_trans hk (Nat.le_succ n)) (Fin.snoc ω t) =
      pathTake k hk ω := by
  funext i
  change Fin.snoc (α := fun _ : Fin (n + 1 + 1) => S) ω t
    ((Fin.castLE (Nat.add_le_add_right hk 1) i).castSucc) = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1 + 1) => S) t ω
    (Fin.castLE (Nat.add_le_add_right hk 1) i)

section PrefixExpectations

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

theorem sum_pathWeight_take_v (C : FiniteReversibleChain S) {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (H : StatePath S k → V) :
    (∑ ω : StatePath S n, pathWeight C n ω • H (pathTake k hk ω)) =
      ∑ η : StatePath S k, pathWeight C k η • H η := by
  classical
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      by_cases hkn : k ≤ n
      · rw [sum_pathWeight_snoc_v]
        simp only [pathTake_snoc k hkn, mul_smul]
        simp only [← Finset.smul_sum, ← Finset.sum_smul, C.sum_P, one_smul]
        exact ih k hkn H
      · have hnk : n + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn)
        have hk' : k = n + 1 := Nat.le_antisymm hk hnk
        subst k
        simp

end PrefixExpectations

theorem sum_pathWeight_take (C : FiniteReversibleChain S) {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (H : StatePath S k → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω * H (pathTake k hk ω)) =
      ∑ η : StatePath S k, pathWeight C k η * H η :=
  sum_pathWeight_take_v C k hk H

theorem sum_pathWeight_prefix (C : FiniteReversibleChain S) (k m : ℕ)
    (H : StatePath S k → ℝ) :
    (∑ ω : StatePath S (k + m), pathWeight C (k + m) ω * H (pathPrefix k m ω)) =
      ∑ η : StatePath S k, pathWeight C k η * H η :=
  sum_pathWeight_take C k (Nat.le_add_right k m) H

theorem sum_pathWeight_last (C : FiniteReversibleChain S) (n : ℕ) (H : S → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω * H (ω (Fin.last n))) =
      ∑ s, C.π s * H s := by
  classical
  induction n generalizing H with
  | zero =>
      let e : S ≃ StatePath S 0 :=
        { toFun := fun s _ => s
          invFun := fun ω => ω 0
          left_inv := fun _ => rfl
          right_inv := fun ω => funext fun i => congrArg ω (Fin.subsingleton_one.elim _ _) }
      rw [← e.sum_comp (fun ω => pathWeight C 0 ω * H (ω (Fin.last 0)))]
      simp [e, pathWeight]
  | succ n ih =>
      rw [sum_pathWeight_snoc]
      simp only [Fin.snoc_last, mul_assoc]
      simp_rw [← Finset.mul_sum]
      rw [ih (fun s => ∑ t, C.P s t * H t)]
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, sum_π_mul_P]

theorem sum_pathWeight_last_pair (C : FiniteReversibleChain S) (n : ℕ)
    (H : S → S → ℝ) :
    (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω *
      H (ω (Fin.last n).castSucc) (ω (Fin.last (n + 1)))) =
      ∑ s, ∑ t, (C.π s * C.P s t) * H s t := by
  classical
  rw [sum_pathWeight_snoc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]
  simp_rw [← Finset.mul_sum]
  exact sum_pathWeight_last C n (fun s => ∑ t, C.P s t * H s t)

theorem sum_pathWeight_pair (C : FiniteReversibleChain S) {n : ℕ}
    (r : ℕ) (hr : r < n) (H : S → S → ℝ) :
    (∑ ω : StatePath S n, pathWeight C n ω *
      H (ω (⟨r, hr⟩ : Fin n).castSucc) (ω (⟨r, hr⟩ : Fin n).succ)) =
      ∑ s, ∑ t, (C.π s * C.P s t) * H s t := by
  have hk : r + 1 ≤ n := Nat.succ_le_of_lt hr
  calc
    _ = ∑ ω : StatePath S n, pathWeight C n ω *
        (fun η : StatePath S (r + 1) =>
          H (η (Fin.last r).castSucc) (η (Fin.last (r + 1))))
          (pathTake (r + 1) hk ω) := by rfl
    _ = ∑ η : StatePath S (r + 1), pathWeight C (r + 1) η *
        H (η (Fin.last r).castSucc) (η (Fin.last (r + 1))) :=
      sum_pathWeight_take C (r + 1) hk
        (fun η : StatePath S (r + 1) => H (η (Fin.last r).castSucc) (η (Fin.last (r + 1))))
    _ = _ := sum_pathWeight_last_pair C r H

theorem stateCost_one {X : Type*} [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) :
    stateCost C f p 1 =
      ∑ s, ∑ t, (C.π s * C.P s t) * Real.rpow (‖f t - f s‖) p := by
  simpa only [stateCost, Fin.last_zero, Fin.castSucc_zero] using
    sum_pathWeight_last_pair C 0 (fun s t => Real.rpow (‖f t - f s‖) p)

theorem sum_pathWeight_take_next {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (C : FiniteReversibleChain S) {n : ℕ} (k : ℕ) (hk : k < n)
    (η : StatePath S k) (H : S → V) :
    (∑ ω : StatePath S n,
      if pathTake k (Nat.le_of_lt hk) ω = η then
        pathWeight C n ω • H (ω ⟨k + 1, Nat.succ_lt_succ hk⟩)
      else 0) =
      pathWeight C k η • ∑ t, C.P (η (Fin.last k)) t • H t := by
  classical
  have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hk
  let F : StatePath S (k + 1) → V := fun ζ =>
    if Fin.init ζ = η then H (ζ (Fin.last (k + 1))) else 0
  calc
    _ = ∑ ω : StatePath S n, pathWeight C n ω • F (pathTake (k + 1) hk1 ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      have hi : Fin.init (pathTake (k + 1) hk1 ω) =
          pathTake k (Nat.le_of_lt hk) ω := by funext i; rfl
      have hl : pathTake (k + 1) hk1 ω (Fin.last (k + 1)) =
          ω ⟨k + 1, Nat.succ_lt_succ hk⟩ := rfl
      simp only [F, hi, hl, smul_ite, smul_zero]
    _ = ∑ ζ : StatePath S (k + 1), pathWeight C (k + 1) ζ • F ζ :=
      sum_pathWeight_take_v C (k + 1) hk1 F
    _ = _ := by
      rw [sum_pathWeight_snoc_v]
      simp only [F, Fin.init_snoc, Fin.snoc_last]
      have hf (ζ : StatePath S k) :
          (∑ t, (pathWeight C k ζ * C.P (ζ (Fin.last k)) t) •
            (if ζ = η then H t else 0)) =
          if ζ = η then pathWeight C k ζ • ∑ t, C.P (ζ (Fin.last k)) t • H t
          else 0 := by
        by_cases hζη : ζ = η
        · simp only [hζη, ite_true, mul_smul, ← Finset.smul_sum]
        · simp only [hζη, ite_false, smul_zero, Finset.sum_const_zero]
      simp_rw [hf]
      simp

end MarkovSuperreflexivity

end

end OAI
