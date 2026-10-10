import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Data.Set.Countable
import OAI.AlgebraicGeometry.PlaneCurves.Configuration

namespace OAI

/-!
# Finite-root and countable polynomial avoidance over the complex numbers
-/

section

/-! Direct countable polynomial avoidance by induction on the number of variables.
At each step, one nonzero coefficient is retained from each polynomial, followed
by avoidance of the countable union of finite univariate root sets. -/
namespace Nagata.Workers.W25
open MvPolynomial

/-- A countable family of nonzero polynomials in finitely many variables has a
simultaneous nonvanishing point over every uncountable integral domain. -/
theorem exists_countable_nonzero_eval_fin (K : Type*) [CommRing K] [IsDomain K]
    [Uncountable K] (n : ℕ) {ι : Type*} [Countable ι] :
    ∀ p : ι → MvPolynomial (Fin n) K, (∀ i, p i ≠ 0) →
      ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      intro p hp
      refine ⟨Fin.elim0, fun i hi => hp i ?_⟩
      apply (isEmptyRingEquiv K (Fin 0)).injective
      rw [map_zero, isEmptyRingEquiv_eq_coeff_zero]
      rw [(p i).eq_C_of_isEmpty, eval_C] at hi
      exact hi
  | succ n ih =>
      intro p hp
      let Q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hQ : ∀ i, Q i ≠ 0 := by
        intro i hi
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [map_zero] using hi
      have hcoeff : ∀ i, ∃ d, (Q i).coeff d ≠ 0 := by
        intro i
        by_contra h
        apply hQ i
        apply Polynomial.ext
        intro d
        simp only [Polynomial.coeff_zero]
        exact Classical.not_not.mp (fun hd => h ⟨d, hd⟩)
      let k : ι → ℕ := fun i => Classical.choose (hcoeff i)
      have hk : ∀ i, (Q i).coeff (k i) ≠ 0 :=
        fun i => Classical.choose_spec (hcoeff i)
      obtain ⟨x, hx⟩ := ih (fun i => (Q i).coeff (k i)) hk
      let q : ι → Polynomial K := fun i => Polynomial.map (eval x) (Q i)
      have hq : ∀ i, q i ≠ 0 := by
        intro i hi
        apply hx i
        have h := congrArg (fun P : Polynomial K => P.coeff (k i)) hi
        simpa only [q, Polynomial.coeff_map, Polynomial.coeff_zero] using h
      let B : Set K := ⋃ i, {y | (q i).IsRoot y}
      have hB : B.Countable := Set.countable_iUnion fun i =>
        (Polynomial.finite_setOfPred_isRoot (hq i)).countable
      have hex : ∃ y : K, y ∉ B := by
        by_contra h
        have hBu : B = Set.univ := Set.eq_univ_of_forall fun y =>
          Classical.not_not.mp (fun hy => h ⟨y, hy⟩)
        exact Set.not_countable_univ (hBu ▸ hB)
      obtain ⟨y, hy⟩ := hex
      refine ⟨Fin.cons y x, fun i hi => hy ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change Polynomial.eval y (q i) = 0
      simpa only [eval_eq_eval_mv_eval', q, Q] using hi

/-- Coordinate-type-independent form of direct countable polynomial avoidance. -/
theorem exists_countable_nonzero_eval (K : Type*) [CommRing K] [IsDomain K]
    [Uncountable K] {σ ι : Type*} [Fintype σ] [Countable ι]
    (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  let e := Fintype.equivFin σ
  have hq : ∀ i, rename e (p i) ≠ 0 := by
    intro i hi
    apply hp i
    apply rename_injective e e.injective
    simpa only [map_zero] using hi
  obtain ⟨x, hx⟩ := exists_countable_nonzero_eval_fin K (Fintype.card σ)
    (fun i => rename e (p i)) hq
  refine ⟨x ∘ e, fun i => ?_⟩
  simpa only [eval_rename] using hx i

end Nagata.Workers.W25

end

section

/-! Direct avoidance for actual complex affine coordinates. -/
namespace Nagata.Workers.W25

/-- A countable family of nonzero complex polynomials in finitely many variables
has a simultaneous nonvanishing complex point. This proof uses finite root sets. -/
theorem exists_complex_polynomial_avoidance_direct {σ ι : Type*} [Fintype σ] [Countable ι]
    (p : ι → MvPolynomial σ ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → ℂ, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.cantor Cardinal.aleph0)
  exact exists_countable_nonzero_eval ℂ p hp

end Nagata.Workers.W25

end

section

/-! Simultaneous polynomial avoidance by genuine distinct projective points in
the standard affine chart. Pairwise difference equations are included explicitly. -/
noncomputable section
namespace Nagata.Workers.W25
open Nagata.ProjectiveGeometry

/-- A countable family of nonzero affine equations admits a simultaneous avoiding
tuple whose first coordinates are pairwise distinct. -/
theorem exists_distinct_affine_avoidance {r : ℕ} {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin r × Fin 2) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin r × Fin 2 → ℂ,
      (∀ i, MvPolynomial.eval x (p i) ≠ 0) ∧
      Function.Injective (fun i : Fin r => x (i, 0)) := by
  classical
  let J := {ij : Fin r × Fin r // ij.1 ≠ ij.2}
  let q : Sum ι J → MvPolynomial (Fin r × Fin 2) ℂ :=
    Sum.elim p (fun ij => MvPolynomial.X (ij.val.1, 0) - MvPolynomial.X (ij.val.2, 0))
  have hq : ∀ j, q j ≠ 0 := by
    intro j
    cases j with
    | inl i => exact hp i
    | inr ij =>
      apply sub_ne_zero.mpr
      intro h
      exact ij.property (congrArg Prod.fst (MvPolynomial.X_injective h))
  obtain ⟨x, hx⟩ := exists_complex_polynomial_avoidance_direct q hq
  refine ⟨x, fun i => hx (.inl i), ?_⟩
  intro i j hij
  by_contra hne
  have h := hx (.inr ⟨(i, j), hne⟩)
  apply h
  simp [q, hij]

/-- The affine avoiding tuple defines actual pairwise distinct projective points. -/
theorem exists_projective_affine_avoidance {r : ℕ} {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin r × Fin 2) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ (x : Fin r × Fin 2 → ℂ) (P : OrderedDistinctPoints r),
      (∀ i, P.val i = affinePlanePoint (fun j => x (i, j))) ∧
      (∀ i, MvPolynomial.eval x (p i) ≠ 0) := by
  obtain ⟨x, hx, hinj⟩ := exists_distinct_affine_avoidance p hp
  have hpoints : Function.Injective
      (fun i : Fin r => affinePlanePoint (fun j => x (i, j))) := by
    intro i j h
    apply hinj
    exact congrFun (affinePlanePoint_injective h) 0
  exact ⟨x, ⟨_, hpoints⟩, fun _ => rfl, hx⟩

end Nagata.Workers.W25

end
end

section

/-! Finite-variable polynomial function extensionality over actual C, derived
from the already-checked nonvanishing theorem. -/
namespace Nagata.Workers.W25

/-- Complex polynomials in finitely many variables agree if all evaluations agree. -/
theorem complex_polynomial_funext {σ : Type*} [Fintype σ]
    {p q : MvPolynomial σ ℂ}
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨x, hx⟩ := exists_complex_polynomial_avoidance_direct
    (fun _ : Unit => p - q) (fun _ => hne)
  apply hx ()
  rw [map_sub, h x, sub_self]

end Nagata.Workers.W25

end

end OAI
