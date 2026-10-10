import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Finite-phase resonance combinatorics

These are the elementary finite combinatorial ingredients of §7,
Lemma `phase:quantile-gap`, of *A uniform Hilbert transform estimate for
Lipschitz directions*. The frequency separation is quantitative; no
assumption about additive independence is made.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

def Separated (frequency : ι → ℝ) (gap : ℝ) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → gap ≤ |frequency i - frequency j|

def Resonant (frequency : ι → ℝ) (gap : ℝ) (i j k l : ι) : Prop :=
  |frequency i + frequency j - frequency k - frequency l| < gap / 4

theorem resonant_swap_left {frequency : ι → ℝ} {gap : ℝ} {i j k l : ι} :
    Resonant frequency gap i j k l ↔ Resonant frequency gap j i k l := by
  simp only [Resonant, add_comm (frequency i) (frequency j)]

theorem resonant_swap_right {frequency : ι → ℝ} {gap : ℝ} {i j k l : ι} :
    Resonant frequency gap i j k l ↔ Resonant frequency gap i j l k := by
  simp only [Resonant, sub_sub, add_comm (frequency k) (frequency l)]

theorem resonant_swap_pairs {frequency : ι → ℝ} {gap : ℝ} {i j k l : ι} :
    Resonant frequency gap i j k l ↔ Resonant frequency gap k l i j := by
  unfold Resonant
  have h : frequency k + frequency l - frequency i - frequency j =
      -(frequency i + frequency j - frequency k - frequency l) := by ring
  rw [h, abs_neg]

/-- Three fixed indices determine at most one fourth index. -/
theorem unique_fourth {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    {i j k l l' : ι} (h : Resonant frequency gap i j k l)
    (h' : Resonant frequency gap i j k l') : l = l' := by
  by_contra hne
  have hs := hsep hne
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  obtain ⟨hlo', hhi'⟩ := abs_lt.mp h'
  have hlt : |frequency l - frequency l'| < gap := by
    apply abs_lt.mpr
    constructor <;> linarith
  exact (not_lt_of_ge hs) hlt

theorem unique_third {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    {i j k k' l : ι} (h : Resonant frequency gap i j k l)
    (h' : Resonant frequency gap i j k' l) : k = k' :=
  unique_fourth hgap hsep (resonant_swap_right.mp h) (resonant_swap_right.mp h')

theorem unique_second {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    {i j j' k l : ι} (h : Resonant frequency gap i j k l)
    (h' : Resonant frequency gap i j' k l) : j = j' :=
  unique_fourth hgap hsep (resonant_swap_pairs.mp h) (resonant_swap_pairs.mp h')

theorem unique_first {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    {i i' j k l : ι} (h : Resonant frequency gap i j k l)
    (h' : Resonant frequency gap i' j k l) : i = i' :=
  unique_second hgap hsep (resonant_swap_left.mp h) (resonant_swap_left.mp h')

/-- For three fixed indices, summing a nonnegative weight over resonant
completions costs at most that weight. -/
theorem sum_completions_le [Fintype ι] {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (i j k : ι) (a : ℝ) (ha : 0 ≤ a) :
    (∑ l, if Resonant frequency gap i j k l then a else 0) ≤ a := by
  classical
  by_cases hex : ∃ l, Resonant frequency gap i j k l
  · obtain ⟨l₀, hl₀⟩ := hex
    have heq (l : ι) :
        (if Resonant frequency gap i j k l then a else 0) =
          if l = l₀ then a else 0 := by
      by_cases hl : l = l₀
      · subst l
        simp [hl₀]
      · have hn : ¬ Resonant frequency gap i j k l := by
          intro hr
          exact hl (unique_fourth hgap hsep hr hl₀)
        simp [hl, hn]
    simp_rw [heq]
    simp
  · have hn (l : ι) : ¬ Resonant frequency gap i j k l := fun hl => hex ⟨l, hl⟩
    simpa [hn] using ha

/-- Each triple-coordinate marginal used in the fourth-moment argument
has total mass at most one. This is the first marginal, omitting the
fourth coordinate. -/
theorem resonance_triple_mass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if Resonant frequency gap i j k l then x i * x j * x k else 0) ≤ 1 := by
  classical
  calc
    (∑ i, ∑ j, ∑ k, ∑ l,
        if Resonant frequency gap i j k l then x i * x j * x k else 0) ≤
        ∑ i, ∑ j, ∑ k, x i * x j * x k := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact sum_completions_le hgap hsep i j k _ (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k))
    _ = 1 := by
      simp [← Finset.mul_sum, hsum]

abbrev Quadruple (ι : Type*) := ι × ι × ι × ι

def swapPairs : Quadruple ι ≃ Quadruple ι where
  toFun q := (q.2.2.1, q.2.2.2, q.1, q.2.1)
  invFun q := (q.2.2.1, q.2.2.2, q.1, q.2.1)
  left_inv := by rintro ⟨i, j, k, l⟩; rfl
  right_inv := by rintro ⟨i, j, k, l⟩; rfl

def swapLast : Quadruple ι ≃ Quadruple ι where
  toFun q := (q.1, q.2.1, q.2.2.2, q.2.2.1)
  invFun q := (q.1, q.2.1, q.2.2.2, q.2.2.1)
  left_inv := by rintro ⟨i, j, k, l⟩; rfl
  right_inv := by rintro ⟨i, j, k, l⟩; rfl

/-- The first of the four triple-coordinate subprobability weights. -/
def marginal (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) (q : Quadruple ι) : ℝ :=
  if Resonant frequency gap q.1 q.2.1 q.2.2.1 q.2.2.2 then
    x q.1 * x q.2.1 * x q.2.2.1 else 0

theorem marginal_nonneg {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (q : Quadruple ι) : 0 ≤ marginal frequency gap x q := by
  unfold marginal
  split
  · exact mul_nonneg (mul_nonneg (hx _) (hx _)) (hx _)
  · exact le_rfl

theorem marginal_mass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    (∑ q : Quadruple ι, marginal frequency gap x q) ≤ 1 := by
  simpa only [Fintype.sum_prod_type, marginal] using
    resonance_triple_mass_le_one hgap hsep x hx hsum

/-- Reindexing gives all four subprobability bounds without further losses. -/
theorem permuted_marginal_mass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (e : Quadruple ι ≃ Quadruple ι) :
    (∑ q : Quadruple ι, marginal frequency gap x (e q)) ≤ 1 := by
  rw [Equiv.sum_comp e]
  exact marginal_mass_le_one hgap hsep x hx hsum

/-- The elementary affinity bound for two subprobabilities. -/
theorem affinity_le_one [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i ≤ 1) (hsb : ∑ i, b i ≤ 1) :
    (∑ i, Real.sqrt (a i * b i)) ≤ 1 := by
  calc
    (∑ i, Real.sqrt (a i * b i)) = ∑ i, Real.sqrt (a i) * Real.sqrt (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Real.sqrt_mul (ha i) _
    _ ≤ Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ ha hb
    _ ≤ 1 * 1 := mul_le_mul
      (by simpa using Real.sqrt_le_sqrt hsa)
      (by simpa using Real.sqrt_le_sqrt hsb)
      (Real.sqrt_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Four-factor Hölder in the form used by the quantile argument: the square
of the geometric sum is bounded by the affinity of its first two weights. -/
theorem geometric_sum_sq_le_affinity [Fintype ι] (a b c d : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (hsc : ∑ i, c i ≤ 1) (hsd : ∑ i, d i ≤ 1) :
    (∑ i, Real.sqrt (Real.sqrt (a i * b i) * Real.sqrt (c i * d i))) ^ 2 ≤
      ∑ i, Real.sqrt (a i * b i) := by
  let A := ∑ i, Real.sqrt (a i * b i)
  let B := ∑ i, Real.sqrt (c i * d i)
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hB1 : B ≤ 1 := affinity_le_one c d hc hd hsc hsd
  have hq : (∑ i, Real.sqrt (Real.sqrt (a i * b i) * Real.sqrt (c i * d i))) ≤
      Real.sqrt A * Real.sqrt B := by
    calc
      _ = ∑ i, Real.sqrt (Real.sqrt (a i * b i)) *
          Real.sqrt (Real.sqrt (c i * d i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Real.sqrt_mul (Real.sqrt_nonneg _) _
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
        (fun i => Real.sqrt_nonneg (a i * b i))
        (fun i => Real.sqrt_nonneg (c i * d i))
  have hq0 : 0 ≤ ∑ i, Real.sqrt (Real.sqrt (a i * b i) * Real.sqrt (c i * d i)) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc
    _ ≤ (Real.sqrt A * Real.sqrt B) ^ 2 :=
      (sq_le_sq₀ hq0 (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))).2 hq
    _ = A * B := by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hB1 hA
    _ = _ := mul_one A

def geometricTerm (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ)
    (q : Quadruple ι) : ℝ :=
  Real.sqrt
    (Real.sqrt (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) *
      Real.sqrt (marginal frequency gap x (swapLast q) *
        marginal frequency gap x ((swapPairs.trans swapLast) q)))

/-- The four triple-coordinate weights have geometric mean
`(xᵢ xⱼ xₖ xₗ)^(3/4)`, written with square roots. -/
theorem geometricTerm_eq {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i j k l : ι) :
    geometricTerm frequency gap x (i, j, k, l) =
      if Resonant frequency gap i j k l then
        Real.sqrt (Real.sqrt ((x i * x j * x k * x l) ^ 3)) else 0 := by
  by_cases hr : Resonant frequency gap i j k l
  · have hp := resonant_swap_pairs.mp hr
    have hl := resonant_swap_right.mp hr
    have hpl := resonant_swap_right.mp hp
    have hi := hx i
    have hj := hx j
    have hk := hx k
    have hlx := hx l
    simp only [geometricTerm, marginal, swapPairs, swapLast, Equiv.trans_apply,
      Equiv.coe_fn_mk, hr, hp, hl, hpl, ite_true]
    rw [← Real.sqrt_mul (show 0 ≤ (x i * x j * x k) * (x k * x l * x i) by positivity)]
    congr 2
    ring
  · simp [geometricTerm, marginal, swapPairs, swapLast, hr]

theorem sqrt_sqrt_cube_eq_rpow {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (Real.sqrt (u ^ 3)) = u ^ (3 / 4 : ℝ) := by
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (pow_nonneg hu _), ← Real.rpow_natCast_mul hu]
  norm_num

theorem geometricTerm_eq_rpow {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i j k l : ι) :
    geometricTerm frequency gap x (i, j, k, l) =
      if Resonant frequency gap i j k l then
        (x i * x j * x k * x l) ^ (3 / 4 : ℝ) else 0 := by
  rw [geometricTerm_eq hx]
  congr 1
  exact sqrt_sqrt_cube_eq_rpow
    (mul_nonneg (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k)) (hx l))

/-- The ordinary fourth-moment quantity in the manuscript. -/
def resonanceSum [Fintype ι] (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ q : Quadruple ι, geometricTerm frequency gap x q

/-- The affinity inequality that precedes the strict quantile deficit. -/
theorem resonanceSum_sq_le_affinity [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    resonanceSum frequency gap x ^ 2 ≤
      ∑ q : Quadruple ι, Real.sqrt
        (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) := by
  apply geometric_sum_sq_le_affinity
  · exact fun q => marginal_nonneg hx (swapLast q)
  · exact fun q => marginal_nonneg hx ((swapPairs.trans swapLast) q)
  · exact permuted_marginal_mass_le_one hgap hsep x hx hsum swapLast
  · exact permuted_marginal_mass_le_one hgap hsep x hx hsum (swapPairs.trans swapLast)

/-- The usual constant-one fourth-moment bound, before its strict improvement. -/
theorem resonanceSum_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    resonanceSum frequency gap x ≤ 1 := by
  have hq := resonanceSum_sq_le_affinity hgap hsep x hx hsum
  have ha := affinity_le_one (marginal frequency gap x)
    (fun q => marginal frequency gap x (swapPairs q))
    (marginal_nonneg hx) (fun q => marginal_nonneg hx (swapPairs q))
    (marginal_mass_le_one hgap hsep x hx hsum)
    (permuted_marginal_mass_le_one hgap hsep x hx hsum swapPairs)
  nlinarith [sq_nonneg (resonanceSum frequency gap x - 1)]

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
