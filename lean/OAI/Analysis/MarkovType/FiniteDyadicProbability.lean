import OAI.Analysis.MarkovType.FiniteIndependentCopies
import OAI.Analysis.MarkovType.FiniteStoppingTime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

abbrev DyadicWord (N : ℕ) := Fin N → Bool

def fairBitLaw : FiniteLaw Bool where
  mass _ := (2 : ℝ)⁻¹
  mass_nonneg _ := by norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

def dyadicLaw (N : ℕ) : FiniteLaw (DyadicWord N) := fairBitLaw.independentCopies N

@[simp] theorem dyadicLaw_mass (N : ℕ) (ω : DyadicWord N) :
    (dyadicLaw N).mass ω = (2 : ℝ)⁻¹ ^ N := by
  simp [dyadicLaw, FiniteLaw.independentCopies_mass, fairBitLaw]

@[simp] theorem fairBitLaw_prob_eq (b : Bool) :
    fairBitLaw.prob (fun c => c = b) = (2 : ℝ)⁻¹ := by
  cases b <;> norm_num [FiniteLaw.prob, fairBitLaw, Fintype.sum_bool]

def dyadicFiltration (N : ℕ) : FinitePartitionFiltration (DyadicWord N) where
  part n := {
    r := fun ω η => ∀ i : Fin N, i.val < n → ω i = η i
    iseqv := {
      refl := fun ω i _ => rfl
      symm := fun h i hi => (h i hi).symm
      trans := fun h₁ h₂ i hi => (h₁ i hi).trans (h₂ i hi) } }
  refines := by
    intro m n hmn ω η hωη i hi
    exact hωη i (hi.trans_le hmn)

def dyadicPrefix {N : ℕ} (ω : DyadicWord N) (j : ℕ) (hj : j ≤ N) : DyadicWord j :=
  fun i => ω ⟨i.val, i.is_lt.trans_le hj⟩

theorem dyadicPrefix_eq_of_rel {N j : ℕ} {ω η : DyadicWord N} (hj : j ≤ N)
    (h : ((dyadicFiltration N).part j).r ω η) :
    dyadicPrefix ω j hj = dyadicPrefix η j hj := by
  funext i
  exact h ⟨i.val, i.is_lt.trans_le hj⟩ i.is_lt

theorem dyadic_rel_of_prefix_eq {N j : ℕ} {ω η : DyadicWord N} (hj : j ≤ N)
    (h : dyadicPrefix ω j hj = dyadicPrefix η j hj) :
    ((dyadicFiltration N).part j).r ω η := by
  intro i hi
  simpa only [dyadicPrefix] using congrFun h ⟨i.val, hi⟩

theorem dyadic_prod_initial (N j : ℕ) (hj : j ≤ N) (a : ℝ) :
    (∏ i : Fin N, if i.val < j then a else 1) = a ^ j := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < j then a else 1) N]
  induction N with
  | zero =>
      have hj₀ : j = 0 := by omega
      simp [hj₀]
  | succ N ih =>
      rw [Finset.prod_range_succ]
      by_cases hjN : j ≤ N
      · rw [ih hjN, ite_eq_right (not_lt.mpr hjN), mul_one]
      · have hj' : j = N + 1 := by omega
        subst j
        have hprod : (∏ i ∈ Finset.range N, if i < N + 1 then a else 1) = a ^ N := by
          calc
            _ = ∏ _i ∈ Finset.range N, a := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [ite_eq_left ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self N))]
            _ = a ^ N := by simp
        rw [hprod, ite_eq_left (Nat.lt_succ_self N), pow_succ]

theorem dyadicLaw_prob_prefix {N j : ℕ} (hj : j ≤ N) (α : DyadicWord j) :
    (dyadicLaw N).prob (fun ω => dyadicPrefix ω j hj = α) = (dyadicLaw j).mass α := by
  classical
  let A : Fin N → Bool → Prop := fun i b =>
    if hi : i.val < j then b = α ⟨i.val, hi⟩ else True
  have hevent : (fun ω : DyadicWord N => dyadicPrefix ω j hj = α) =
      (fun ω => ∀ i, A i (ω i)) := by
    funext ω
    apply propext
    constructor
    · intro h i
      by_cases hi : i.val < j
      · have heq := congrFun h ⟨i.val, hi⟩
        simpa only [A, dite_eq_left hi, dyadicPrefix] using heq
      · simp only [A, dite_eq_right hi]
    · intro h
      funext i
      have hi : (⟨i.val, i.is_lt.trans_le hj⟩ : Fin N).val < j := i.is_lt
      simpa only [A, dite_eq_left hi, dyadicPrefix] using h ⟨i.val, i.is_lt.trans_le hj⟩
  rw [hevent]
  change (fairBitLaw.independentCopies N).prob (fun ω => ∀ i, A i (ω i)) = _
  rw [FiniteLaw.independentCopies_prob_rect, dyadicLaw_mass]
  calc
    (∏ i, fairBitLaw.prob (A i)) = ∏ i : Fin N, if i.val < j then (2 : ℝ)⁻¹ else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i.val < j
      · simp only [A, dite_eq_left hi, fairBitLaw_prob_eq, ite_eq_left hi]
      · simp only [A, dite_eq_right hi, FiniteLaw.prob_true, ite_eq_right hi]
    _ = (2 : ℝ)⁻¹ ^ j := dyadic_prod_initial N j hj _

theorem FiniteLaw.expect_eq_sum_fiber {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (π : Ω → Ξ) (f : Ξ → ℝ) :
    μ.expect (fun ω => f (π ω)) = ∑ ξ, μ.prob (fun ω => π ω = ξ) * f ξ := by
  classical
  unfold FiniteLaw.expect FiniteLaw.prob
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul, zero_mul]
  simp

theorem dyadicLaw_expect_prefix {N j : ℕ} (hj : j ≤ N) (f : DyadicWord j → ℝ) :
    (dyadicLaw N).expect (fun ω => f (dyadicPrefix ω j hj)) = (dyadicLaw j).expect f := by
  rw [FiniteLaw.expect_eq_sum_fiber]
  simp_rw [dyadicLaw_prob_prefix hj]
  rfl

def dyadicFlip {N : ℕ} (i : Fin N) (ω : DyadicWord N) : DyadicWord N :=
  Function.update ω i (!(ω i))

@[simp] theorem dyadicFlip_at {N : ℕ} (i : Fin N) (ω : DyadicWord N) :
    dyadicFlip i ω i = !(ω i) := by simp [dyadicFlip]

theorem dyadicFlip_of_ne {N : ℕ} (i j : Fin N) (ω : DyadicWord N) (hji : j ≠ i) :
    dyadicFlip i ω j = ω j := by simp [dyadicFlip, hji]

theorem dyadicFlip_involutive {N : ℕ} (i : Fin N) : Function.Involutive (dyadicFlip i) := by
  intro ω
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · rw [dyadicFlip_of_ne i j _ hji, dyadicFlip_of_ne i j _ hji]

def dyadicFlipEquiv {N : ℕ} (i : Fin N) : DyadicWord N ≃ DyadicWord N where
  toFun := dyadicFlip i
  invFun := dyadicFlip i
  left_inv := dyadicFlip_involutive i
  right_inv := dyadicFlip_involutive i

theorem dyadicFlip_rel {N : ℕ} (i : Fin N) (ω : DyadicWord N) :
    ((dyadicFiltration N).part i.val).r (dyadicFlip i ω) ω := by
  intro j hj
  apply dyadicFlip_of_ne
  intro hji
  subst j
  exact (Nat.lt_irrefl i.val) hj

@[simp] theorem dyadicFlip_prefix {N : ℕ} (i : Fin N) (ω : DyadicWord N) :
    dyadicPrefix (dyadicFlip i ω) i.val (Nat.le_of_lt i.is_lt) =
      dyadicPrefix ω i.val (Nat.le_of_lt i.is_lt) :=
  dyadicPrefix_eq_of_rel _ (dyadicFlip_rel i ω)

end MarkovSuperreflexivity

end

end OAI
