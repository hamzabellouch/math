import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
import OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth

namespace OAI

namespace PiExponentJets.W29

open MvPolynomial Submodule
open scoped BigOperators

section CoefficientPieces

variable {k R τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype τ] {m : ℕ}

noncomputable def boundedCoefficientMap (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) :
    (Fin m → restrictTotalDegree τ k n) →ₗ[k] R where
  toFun p := ∑ j, g (p j) * e j
  map_add' p q := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by simp [map_smul, Finset.smul_sum]

noncomputable def generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) : Submodule k R :=
  LinearMap.range (boundedCoefficientMap g e n)

omit [Fintype τ] in
lemma mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R)
    (n : ℕ) (r : R) : r ∈ generatorPiece g e n ↔
      ∃ p : Fin m → MvPolynomial τ k,
        (∀ j, (p j).totalDegree ≤ n) ∧ (∑ j, g (p j) * e j) = r := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun j => p j, fun j => (mem_restrictTotalDegree τ _ _).mp (p j).property, rfl⟩
  · rintro ⟨p, hp, hpr⟩
    exact ⟨fun j => ⟨p j, (mem_restrictTotalDegree τ _ _).mpr (hp j)⟩, hpr⟩

omit [Fintype τ] in
lemma generatorPiece_mono (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R) :
    Monotone (generatorPiece g e) := by
  intro a b hab r hr
  obtain ⟨p, hp, hpr⟩ := (mem_generatorPiece g e a r).mp hr
  exact (mem_generatorPiece g e b r).mpr ⟨p, fun j => (hp j).trans hab, hpr⟩

noncomputable instance generatorPiece_finite (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) : Module.Finite k (generatorPiece g e n) := by
  unfold generatorPiece
  infer_instance

lemma finrank_generatorPiece_le (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) :
    Module.finrank k (generatorPiece g e n) ≤
      m * Module.finrank k (restrictTotalDegree τ k n) := by
  calc
    Module.finrank k (generatorPiece g e n) ≤
        Module.finrank k (Fin m → restrictTotalDegree τ k n) :=
      LinearMap.finrank_range_le (boundedCoefficientMap g e n)
    _ = m * Module.finrank k (restrictTotalDegree τ k n) := by
      rw [Module.finrank_pi_fintype]
      simp

omit [Fintype τ] in
lemma mul_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R)
    (x : R) (A : Fin m → Fin m → MvPolynomial τ k) (D : ℕ)
    (hA : ∀ j, x * e j = ∑ l, g (A j l) * e l)
    (hD : ∀ j l, (A j l).totalDegree ≤ D)
    {n : ℕ} {r : R} (hr : r ∈ generatorPiece g e n) :
    x * r ∈ generatorPiece g e (n + D) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (mem_generatorPiece g e n r).mp hr
  apply (mem_generatorPiece g e (n + D) _).mpr
  refine ⟨fun l => ∑ j, p j * A j l, ?_, ?_⟩
  · intro l
    exact totalDegree_finsetSum_le fun j _ =>
      (totalDegree_mul (p j) (A j l)).trans (Nat.add_le_add (hp j) (hD j l))
  · simp only [map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ l, g (p j) * g (A j l) * e l) =
          g (p j) * (∑ l, g (A j l) * e l) := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = x * (g (p j) * e j) := by rw [← hA j]; ring

end CoefficientPieces

section FiniteMatrices

variable {k R σ τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype σ]

theorem finite_multiplication_matrices (g : MvPolynomial τ k →ₐ[k] R)
    (hfin : g.Finite) (x : σ → R) :
    ∃ (m D E : ℕ) (e : Fin m → R)
      (A : σ → Fin m → Fin m → MvPolynomial τ k),
      (∀ i j, x i * e j = ∑ l, g (A i j l) * e l) ∧
      (∀ i j l, (A i j l).totalDegree ≤ D) ∧
      (1 : R) ∈ generatorPiece g e E := by
  classical
  let : Algebra (MvPolynomial τ k) R := g.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial τ k) R := hfin
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := MvPolynomial τ k) (M := R)
  have hex (r : R) : ∃ p : Fin m → MvPolynomial τ k, ∑ j, g (p j) * e j = r := by
    have hr : r ∈ Submodule.span (MvPolynomial τ k) (Set.range e) := by rw [he]; trivial
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hr
    refine ⟨p, ?_⟩
    change (∑ j, g (p j) * e j) = r at hp
    exact hp
  choose A hA using fun i j => hex (x i * e j)
  obtain ⟨p, hp⟩ := hex 1
  let D := Finset.univ.sup fun i => Finset.univ.sup fun j =>
    Finset.univ.sup fun l => (A i j l).totalDegree
  let E := Finset.univ.sup fun j => (p j).totalDegree
  refine ⟨m, D, E, e, A, fun i j => (hA i j).symm, ?_, ?_⟩
  · intro i j l
    calc
      (A i j l).totalDegree
          ≤ Finset.univ.sup (fun l => (A i j l).totalDegree) :=
            Finset.le_sup (f := fun l => (A i j l).totalDegree) (Finset.mem_univ l)
      _ ≤ Finset.univ.sup (fun j => Finset.univ.sup (fun l => (A i j l).totalDegree)) :=
            Finset.le_sup (f := fun j => Finset.univ.sup
              (fun l => (A i j l).totalDegree)) (Finset.mem_univ j)
      _ ≤ D := Finset.le_sup (f := fun i => Finset.univ.sup
          (fun j => Finset.univ.sup (fun l => (A i j l).totalDegree)))
          (Finset.mem_univ i)
  · exact (mem_generatorPiece g e E 1).mpr
      ⟨p, fun j => Finset.le_sup (f := fun j => (p j).totalDegree)
        (Finset.mem_univ j), hp⟩

end FiniteMatrices

section Propagation

variable {k R σ τ : Type*} [Field k] [CommRing R] [Algebra k R]
  {m D E : ℕ}

lemma variable_pow_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    {n : ℕ} {r : R} (hr : r ∈ generatorPiece g e n) (i : σ) (a : ℕ) :
    r * f (X i) ^ a ∈ generatorPiece g e (n + a * D) := by
  induction a with
  | zero => simpa using hr
  | succ a ih =>
    have h := mul_mem_generatorPiece g e (f (X i)) (A i) D (hA i) (hD i) ih
    have hdeg : n + (a + 1) * D = n + a * D + D := by ring
    rw [hdeg]
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

lemma monomial_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    (h1 : (1 : R) ∈ generatorPiece g e E) (a : σ →₀ ℕ) (c : k) :
    f (monomial a c) ∈ generatorPiece g e (E + (a.sum fun _ e => e) * D) := by
  classical
  induction a using Finsupp.induction with
  | zero =>
    have h := (generatorPiece g e E).smul_mem c h1
    simpa only [Finsupp.sum_zero_index, zero_mul, add_zero, ← C_apply,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.smul_def, mul_one] using h
  | single_add i a b hbi ha ih =>
    have h := variable_pow_mem_generatorPiece g e f A hA hD ih i a
    have hsum : (Finsupp.single i a + b).sum (fun _ e => e) =
        a + b.sum (fun _ e => e) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index (by rfl)]
    have hdeg : E + ((Finsupp.single i a + b).sum fun _ e => e) * D =
        E + (b.sum fun _ e => e) * D + a * D := by
      rw [hsum]
      ring
    rw [hdeg, monomial_single_add, map_mul, map_pow]
    simpa only [mul_comm] using h

lemma polynomial_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    (h1 : (1 : R) ∈ generatorPiece g e E) (p : MvPolynomial σ k) :
    f p ∈ generatorPiece g e (E + p.totalDegree * D) := by
  classical
  have he : f p = ∑ a ∈ p.support, f (monomial a (p.coeff a)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  exact generatorPiece_mono g e
    (Nat.add_le_add_left (Nat.mul_le_mul_right D (le_totalDegree ha)) E)
    (monomial_mem_generatorPiece g e f A hA hD h1 a (p.coeff a))

end Propagation

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem finite_normalization_upper_growth
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I)) (hfin : g.Finite) :
    ∃ C E : ℕ, 0 < C ∧ ∀ n : ℕ,
      Module.finrank k (W24.quotientDegreeFiltration I n) ≤
        C * Module.finrank k (restrictTotalDegree τ k (C * n + E)) := by
  classical
  let f := Ideal.Quotient.mkₐ k I
  obtain ⟨m, D, E, e, A, hA, hD, h1⟩ :=
    finite_multiplication_matrices g hfin (fun i : σ => f (X i))
  let C := max (max m D) 1
  have hmC : m ≤ C := (le_max_left m D).trans (le_max_left _ _)
  have hDC : D ≤ C := (le_max_right m D).trans (le_max_left _ _)
  refine ⟨C, E, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun n => ?_⟩
  have hle : W24.quotientDegreeFiltration I n ≤ generatorPiece g e (C * n + E) := by
    rintro r ⟨p, hp, rfl⟩
    have hpdeg := (mem_restrictTotalDegree σ n p).mp hp
    apply generatorPiece_mono g e
      (show E + p.totalDegree * D ≤ C * n + E by
        have hmul := Nat.mul_le_mul hpdeg hDC
        simpa only [Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left hmul E)
    exact polynomial_mem_generatorPiece g e f A hA hD h1 p
  calc
    Module.finrank k (W24.quotientDegreeFiltration I n)
        ≤ Module.finrank k (generatorPiece g e (C * n + E)) :=
          Submodule.finrank_mono hle
    _ ≤ m * Module.finrank k (restrictTotalDegree τ k (C * n + E)) :=
      finrank_generatorPiece_le g e _
    _ ≤ C * Module.finrank k (restrictTotalDegree τ k (C * n + E)) :=
      Nat.mul_le_mul_right _ hmC

end PiExponentJets.W29

end OAI
