import OAI.NumberTheory.TwoPoint.Bounds.ResidueCounts
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.Pi

namespace OAI

/-!
# Finite CRT marginals and contraction under independent randomization

A selected finite set of pairwise coprime residue coordinates has the law
of one residue modulo their product. The exact interval count from
`ResidueCounts` gives total variation at most `D / (2N)`. Applying any
finite stochastic kernel preserves this bound; in particular one may add
independent finite randomness and project to any selected encoded bits.
These are the finite arithmetic and data-processing steps in `q:crt-bits`.
-/

open Finset

namespace TwoPointCorrelations

/-- Total variation between two finite real mass functions. -/
noncomputable def finiteTotalVariation {α : Type*} [Fintype α] (f g : α → ℝ) : ℝ :=
  (∑ x, |f x - g x|) / 2

/-- Application of a finite transition kernel. -/
noncomputable def kernelTransport {α β : Type*} [Fintype α]
    (K : α → β → ℝ) (f : α → ℝ) (y : β) : ℝ :=
  ∑ x, f x * K x y

lemma kernelTransport_nonneg {α β : Type*} [Fintype α]
    (K : α → β → ℝ) (f : α → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hf : ∀ x, 0 ≤ f x) (y : β) : 0 ≤ kernelTransport K f y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hf x) (hK x y))

lemma kernelTransport_sum {α β : Type*} [Fintype α] [Fintype β]
    (K : α → β → ℝ) (f : α → ℝ) (hK : ∀ x, ∑ y, K x y = 1) :
    ∑ y, kernelTransport K f y = ∑ x, f x := by
  unfold kernelTransport
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]

/-- Adding independent randomness and then forgetting information cannot
increase total variation. -/
theorem finiteTotalVariation_kernel {α β : Type*} [Fintype α] [Fintype β]
    (K : α → β → ℝ) (f g : α → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hKsum : ∀ x, ∑ y, K x y = 1) :
    finiteTotalVariation (kernelTransport K f) (kernelTransport K g) ≤
      finiteTotalVariation f g := by
  have hpoint (y : β) : |kernelTransport K f y - kernelTransport K g y| ≤
      ∑ x, |f x - g x| * K x y := by
    unfold kernelTransport
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ x, (f x * K x y - g x * K x y)| = |∑ x, (f x - g x) * K x y| := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ∑ x, |(f x - g x) * K x y| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hK _ _)]
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset β)) => hpoint y)
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum, hKsum, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num)

/-- A bounded observable has expectation difference at most twice TV. -/
lemma finite_observable_difference {α : Type*} [Fintype α]
    (f g u : α → ℝ) (hu : ∀ x, |u x| ≤ 1) :
    |(∑ x, f x * u x) - ∑ x, g x * u x| ≤ 2 * finiteTotalVariation f g := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (f x * u x - g x * u x)| = |∑ x, (f x - g x) * u x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, |(f x - g x) * u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |f x - g x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hu x)
    _ = 2 * finiteTotalVariation f g := by unfold finiteTotalVariation; ring

/-- A deterministic map with independent uniform finite auxiliary randomness. -/
noncomputable def finiteRandomKernel {α β J : Type*} [DecidableEq β] [Fintype J]
    (F : α → J → β) (x : α) (y : β) : ℝ :=
  (∑ j, if F x j = y then (1 : ℝ) else 0) / Fintype.card J

lemma finiteRandomKernel_nonneg {α β J : Type*} [DecidableEq β] [Fintype J]
    (F : α → J → β) (x : α) (y : β) : 0 ≤ finiteRandomKernel F x y := by
  unfold finiteRandomKernel
  positivity

lemma finiteRandomKernel_sum {α β J : Type*} [Fintype β] [DecidableEq β]
    [Fintype J] [Nonempty J] (F : α → J → β) (x : α) :
    ∑ y, finiteRandomKernel F x y = 1 := by
  unfold finiteRandomKernel
  rw [← Finset.sum_div, Finset.sum_comm]
  simp

instance modulusProduct_neZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] : NeZero (∏ i, s i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (s i))⟩

/-- The actual joint residue law of an interval under the CRT equivalence. -/
noncomputable def crtJointProbability {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (r : ∀ i, ZMod (s i)) : ℝ :=
  residueProbability A N ((ZMod.prodEquivPi s hcop).symm r)

/-- Uniform independent residue coordinates. -/
noncomputable def crtUniform {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (_r : ∀ i, ZMod (s i)) : ℝ := 1 / (∏ i, s i : ℕ)

lemma crtUniform_product {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (r : ∀ i, ZMod (s i)) : crtUniform s r = ∏ i, (1 / (s i : ℝ)) := by
  simp [crtUniform, one_div, Nat.cast_prod, Finset.prod_inv_distrib]

/-- This CRT-transported mass is the actual empirical joint residue law. -/
lemma crtJointProbability_eq_count {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (r : ∀ i, ZMod (s i)) :
    crtJointProbability s hcop A N r =
      (∑ j ∈ Finset.range N,
        if ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) = r
          then (1 : ℝ) else 0) / N := by
  unfold crtJointProbability residueProbability residueCount
  rw [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have heq : A + (j : ZMod (∏ i, s i)) = (ZMod.prodEquivPi s hcop).symm r ↔
      ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) = r :=
    (ZMod.prodEquivPi s hcop).toEquiv.eq_symm_apply
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, heq]

/-- The CRT equivalence is the expected coordinatewise residue map. -/
lemma crt_coordinates_add_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (j : ℕ) (i : ι) :
    ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) i =
      ZMod.castHom (Finset.dvd_prod_of_mem s (Finset.mem_univ i)) (ZMod (s i)) A +
        (j : ZMod (s i)) := by
  simp only [ZMod.prodEquivPi_apply, map_add, map_natCast]

lemma crtJointProbability_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (r : ∀ i, ZMod (s i)) :
    0 ≤ crtJointProbability s hcop A N r := by
  unfold crtJointProbability residueProbability
  positivity

lemma crtJointProbability_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N) :
    ∑ r, crtJointProbability s hcop A N r = 1 := by
  unfold crtJointProbability
  calc
    _ = ∑ z : ZMod (∏ i, s i), residueProbability A N z :=
      (ZMod.prodEquivPi s hcop).symm.toEquiv.sum_comp (residueProbability A N)
    _ = 1 := residueProbability_sum A N hN

lemma crtJointProbability_totalVariation {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) :
    finiteTotalVariation (crtJointProbability s hcop A N) (crtUniform s) =
      residueTotalVariation A N := by
  unfold finiteTotalVariation crtJointProbability crtUniform residueTotalVariation
  congr 1
  exact (ZMod.prodEquivPi s hcop).symm.toEquiv.sum_comp
    (fun z => |residueProbability A N z - 1 / (∏ i, s i : ℕ)|)

/-- Selected CRT coordinates followed by any finite random encoding or
projection satisfy the interval discrepancy bound. -/
theorem crt_kernel_totalVariation {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N)
    (K : (∀ i, ZMod (s i)) → β → ℝ)
    (hK : ∀ r y, 0 ≤ K r y) (hKsum : ∀ r, ∑ y, K r y = 1) :
    finiteTotalVariation (kernelTransport K (crtJointProbability s hcop A N))
      (kernelTransport K (crtUniform s)) ≤ (∏ i, s i : ℕ) / (2 * (N : ℝ)) := by
  apply (finiteTotalVariation_kernel K _ _ hK hKsum).trans
  rw [crtJointProbability_totalVariation]
  exact residueTotalVariation_le A N hN

/-- Independent finite auxiliary variables and a projection are a special
case, so in particular selecting encoded bit marginals cannot increase TV. -/
theorem crt_random_projection_totalVariation {ι β J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] [Fintype J] [Nonempty J]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N)
    (F : (∀ i, ZMod (s i)) → J → β) :
    finiteTotalVariation
      (kernelTransport (finiteRandomKernel F) (crtJointProbability s hcop A N))
      (kernelTransport (finiteRandomKernel F) (crtUniform s)) ≤
        (∏ i, s i : ℕ) / (2 * (N : ℝ)) :=
  crt_kernel_totalVariation s hcop A N hN _ (finiteRandomKernel_nonneg F)
    (finiteRandomKernel_sum F)

end TwoPointCorrelations

end OAI
