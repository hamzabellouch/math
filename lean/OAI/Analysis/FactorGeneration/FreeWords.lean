import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.Linarith

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

def freePrefix : ℕ → FreeGroup ℕ
  | 0 => 1
  | n + 1 => freePrefix n * FreeGroup.of n

def prefixRatio (k j : ℕ) : FreeGroup ℕ := freePrefix k * (freePrefix j)⁻¹

def exponentCoordinate (i : ℕ) : FreeGroup ℕ →* Multiplicative ℤ :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if i = j then 1 else 0)

theorem freePrefix_eq_prod (n : ℕ) :
    freePrefix n = ((List.range n).map FreeGroup.of).prod := by
  induction n with
  | zero => simp [freePrefix]
  | succ n ih => rw [freePrefix, List.prod_range_succ, ih]

theorem exponentCoordinate_prefix (i n : ℕ) :
    Multiplicative.toAdd (exponentCoordinate i (freePrefix n)) =
      if i < n then 1 else 0 := by
  induction n with
  | zero => simp [freePrefix]
  | succ n ih =>
    rw [freePrefix, map_mul, toAdd_mul, ih]
    simp only [exponentCoordinate, FreeGroup.lift_apply_of, toAdd_ofAdd]
    split_ifs <;> omega

theorem exponentCoordinate_ratio (i k j : ℕ) :
    Multiplicative.toAdd (exponentCoordinate i (prefixRatio k j)) =
      (if i < k then 1 else 0) - (if i < j then 1 else 0) := by
  simp [prefixRatio, exponentCoordinate_prefix, sub_eq_add_neg]

/-- Two differences of initial-segment indicators identify their endpoints,
provided the first interval is nonempty. -/
theorem indicator_difference_injective {k j k' j' : ℕ} (hkj : k ≠ j)
    (h : ∀ i : ℕ, (if i < k then (1 : ℤ) else 0) - (if i < j then 1 else 0) =
      (if i < k' then 1 else 0) - (if i < j' then 1 else 0)) :
    k = k' ∧ j = j' := by
  have hk := h k
  have hj := h j
  have hk' := h k'
  have hj' := h j'
  omega

theorem prefixRatio_injective_offDiagonal {k j k' j' : ℕ} (hkj : k ≠ j)
    (h : prefixRatio k j = prefixRatio k' j') : k = k' ∧ j = j' := by
  apply indicator_difference_injective hkj
  intro i
  simpa only [exponentCoordinate_ratio] using
    congrArg (fun g => Multiplicative.toAdd (exponentCoordinate i g)) h

theorem freePrefix_injective : Function.Injective freePrefix := by
  intro k j h
  have hk := congrArg (fun g => Multiplicative.toAdd (exponentCoordinate k g)) h
  have hj := congrArg (fun g => Multiplicative.toAdd (exponentCoordinate j g)) h
  simp only [exponentCoordinate_prefix] at hk hj
  omega

theorem prefixRatio_eq_one_iff (k j : ℕ) : prefixRatio k j = 1 ↔ k = j := by
  rw [prefixRatio, mul_inv_eq_one]
  exact freePrefix_injective.eq_iff

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/
noncomputable section
open scoped BigOperators
local instance : DecidableEq (FreeGroup ℕ) := Classical.decEq _

def pairRatio {n : ℕ} (ij : Fin n × Fin n) : FreeGroup ℕ :=
  prefixRatio (ij.1.val + 1) (ij.2.val + 1)

theorem pairRatio_eq_one_iff {n : ℕ} (ij : Fin n × Fin n) :
    pairRatio ij = 1 ↔ ij.1 = ij.2 := by
  simp [pairRatio, prefixRatio_eq_one_iff, Fin.ext_iff]

theorem pairRatio_injective_offDiagonal {n : ℕ} {ij kl : Fin n × Fin n}
    (hij : ij.1 ≠ ij.2) (h : pairRatio ij = pairRatio kl) : ij = kl := by
  have hne : ij.1.val + 1 ≠ ij.2.val + 1 := by
    intro hval
    apply hij
    apply Fin.ext
    omega
  have he := prefixRatio_injective_offDiagonal hne h
  apply Prod.ext <;> apply Fin.ext <;> omega

def multiplicity (n : ℕ) (p : FreeGroup ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun ij : Fin n × Fin n => pairRatio ij = p).card

def ratioLabels (n : ℕ) : Finset (FreeGroup ℕ) := by
  classical
  exact insert 1 ((Finset.univ : Finset (Fin n)).offDiag.image pairRatio)

theorem multiplicity_one (n : ℕ) : multiplicity n 1 = n := by
  classical
  have hset : (Finset.univ.filter fun ij : Fin n × Fin n => pairRatio ij = 1) =
      (Finset.univ : Finset (Fin n)).diag := by
    ext ij
    simp [pairRatio_eq_one_iff]
  simp [multiplicity, hset]

theorem multiplicity_offDiagonal {n : ℕ} {ij : Fin n × Fin n} (hij : ij.1 ≠ ij.2) :
    multiplicity n (pairRatio ij) = 1 := by
  classical
  have hset : (Finset.univ.filter fun kl : Fin n × Fin n => pairRatio kl = pairRatio ij) =
      {ij} := by
    ext kl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => (pairRatio_injective_offDiagonal hij h.symm).symm, fun h => h ▸ rfl⟩
  simp [multiplicity, hset]

/-- For n > 0 this is exactly the image of all ordered pairs in the source. -/
theorem ratioLabels_eq_image {n : ℕ} (hn : 0 < n) :
    ratioLabels n = (Finset.univ : Finset (Fin n × Fin n)).image pairRatio := by
  classical
  ext p
  simp only [ratioLabels, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨ij, _, hp⟩)
    · exact ⟨(⟨0, hn⟩, ⟨0, hn⟩), (pairRatio_eq_one_iff _).mpr rfl⟩
    · exact ⟨ij, hp⟩
  · rintro ⟨ij, rfl⟩
    by_cases hij : ij.1 = ij.2
    · exact Or.inl ((pairRatio_eq_one_iff _).mpr hij)
    · exact Or.inr ⟨ij, by simp [hij], rfl⟩

/-- n_e = n and every off-diagonal label has multiplicity one. -/
theorem multiplicity_square_sum (n : ℕ) :
    ∑ p ∈ ratioLabels n, multiplicity n p ^ 2 = 2 * n ^ 2 - n := by
  classical
  have hnot : (1 : FreeGroup ℕ) ∉ (Finset.univ : Finset (Fin n)).offDiag.image pairRatio := by
    intro h
    obtain ⟨ij, hij, heq⟩ := Finset.mem_image.mp h
    exact (Finset.mem_offDiag.mp hij).2.2 ((pairRatio_eq_one_iff _).mp heq)
  have hsum : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag.image pairRatio,
      multiplicity n p ^ 2 = n * n - n := by
    rw [Finset.sum_image]
    · calc
        _ = ∑ _ij ∈ (Finset.univ : Finset (Fin n)).offDiag, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro ij hij
          rw [multiplicity_offDiagonal (Finset.mem_offDiag.mp hij).2.2]
          simp
        _ = n * n - n := by simp
    · intro ij hij kl _hkl heq
      exact pairRatio_injective_offDiagonal (Finset.mem_offDiag.mp hij).2.2 heq
  rw [ratioLabels, Finset.sum_insert hnot, multiplicity_one, hsum]
  have hn : n ≤ n * n := by nlinarith
  simp only [pow_two]
  omega

end

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/
variable {G : Type*} [Group G]

def prefixes : List G → List G
  | [] => []
  | s :: ss => s :: (prefixes ss).map (fun g => s * g)

theorem conjugate_list_prod (s : G) (xs : List G) :
    (xs.map (fun g => s * g * s⁻¹)).prod = s * xs.prod * s⁻¹ := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    simp [mul_assoc]

theorem prefix_perturbation (ss : List G) (h : G) :
    ((prefixes ss).map (fun g => g * h * g⁻¹)).prod * ss.prod =
      (ss.map (fun s => s * h)).prod := by
  induction ss with
  | nil => simp [prefixes]
  | cons s ss ih =>
    have hmap : ((prefixes ss).map (fun g => (s * g) * h * (s * g)⁻¹)).prod =
        s * ((prefixes ss).map (fun g => g * h * g⁻¹)).prod * s⁻¹ := by
      rw [← conjugate_list_prod]
      simp [List.map_map, Function.comp_def, mul_assoc]
    simp only [prefixes, List.map_cons, List.map_map, Function.comp_def, List.prod_cons]
    rw [hmap]
    simpa only [mul_assoc, inv_mul_cancel_left] using congrArg (fun v => s * h * v) ih

/-- The exact prefix cancellation identity with the unperturbed terminal factor. -/
theorem prefix_perturbation_terminal (ss : List G) (h terminal : G) :
    ((prefixes ss).map (fun g => g * h * g⁻¹)).prod * (ss.prod * terminal) =
      (ss.map (fun s => s * h)).prod * terminal := by
  rw [← mul_assoc, prefix_perturbation]

end Generator

end OAI
