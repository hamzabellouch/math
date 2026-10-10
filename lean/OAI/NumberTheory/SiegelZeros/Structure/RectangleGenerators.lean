import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.SiegelZeros.Selection.RowReplacement

namespace OAI

namespace SiegelZeros


noncomputable section
namespace Result.Workers.W57

open Finset Nat
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def iter (D : Derivation ℚ R R) (n : ℕ) : R →ₗ[ℚ] R := D.toLinearMap ^ n

@[simp] theorem iter_zero (D : Derivation ℚ R R) (a : R) : iter D 0 a = a := rfl
@[simp] theorem iter_succ (D : Derivation ℚ R R) (n : ℕ) (a : R) :
    iter D (n+1) a = D (iter D n a) := by
  change (D.toLinearMap ^ (n + 1)) a = D ((D.toLinearMap ^ n) a)
  calc
    (D.toLinearMap ^ (n + 1)) a = (D.toLinearMap * D.toLinearMap ^ n) a :=
      congrArg (fun f : Module.End ℚ R => f a) (_root_.pow_succ' D.toLinearMap n)
    _ = D.toLinearMap ((D.toLinearMap ^ n) a) :=
      Module.End.mul_apply D.toLinearMap (D.toLinearMap ^ n) a
    _ = D ((D.toLinearMap ^ n) a) :=
      congrFun (Derivation.coeFn_coe D) ((D.toLinearMap ^ n) a)

theorem iter_mul (D : Derivation ℚ R R) (n : ℕ) (a b : R) :
    iter D n (a*b) = ∑ ij ∈ antidiagonal n,
      n.choose ij.1 • (iter D ij.1 a * iter D ij.2 b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => iter D i a * iter D j b) n]
    simp only [iter_succ, ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, nsmul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
    rw [mul_comm]

private theorem factorial_normalize (i j : ℕ) :
    (1 / ((i+j).factorial : ℚ)) * ((i+j).choose i : ℚ) =
      (1 / (i.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by
  have h : (((i+j).choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ)) =
      ((i+j).factorial : ℚ) := by
    exact_mod_cast (by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j) :
        (i+j).choose i * i.factorial * j.factorial = (i+j).factorial)
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : ((i+j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i+j)
  field_simp
  nlinarith [h]

def taylorSeries (D : Derivation ℚ R R) (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => (1 / (n.factorial : ℚ)) • iter D n a

@[simp] theorem coeff_taylorSeries (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact PowerSeries.coeff_mk n _

theorem taylorSeries_mul (D : Derivation ℚ R R) (a b : R) :
    taylorSeries D (a*b) = taylorSeries D a * taylorSeries D b := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_taylorSeries, iter_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [coeff_taylorSeries, coeff_taylorSeries]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_mul_smul_comm]
  rw [← hn, factorial_normalize]

def taylorHom (D : Derivation ℚ R R) : R →+* PowerSeries R where
  toFun := taylorSeries D
  map_zero' := by ext n; simp [taylorSeries]
  map_one' := by
    ext n
    cases n with
    | zero => simp [taylorSeries]
    | succ n =>
      have h : iter D (n+1) (1:R) = 0 := by
        induction n with
        | zero => simp
        | succ n ih => simp [ih]
      simp [taylorSeries, h]
  map_add' a b := by ext n; simp [taylorSeries, smul_add]
  map_mul' := taylorSeries_mul D

@[simp] theorem coeff_taylorHom (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorHom D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact coeff_taylorSeries D a n

@[simp] theorem constantCoeff_taylorHom (D : Derivation ℚ R R) (a : R) :
    PowerSeries.constantCoeff (taylorHom D a) = a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorHom]
  simp

def taylorHom₃ (D₁ D₂ D₃ : Derivation ℚ R R) :
    R →+* PowerSeries (PowerSeries (PowerSeries R)) :=
  (PowerSeries.map (PowerSeries.map (taylorHom D₃))).comp
    ((PowerSeries.map (taylorHom D₂)).comp (taylorHom D₁))

theorem coeff_taylorHom₃ (D₁ D₂ D₃ : Derivation ℚ R R) (a : R) (i j k : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff j (PowerSeries.coeff i
      (taylorHom₃ D₁ D₂ D₃ a))) =
    (1 / (k.factorial : ℚ)) • ((1 / (j.factorial : ℚ)) •
      ((1 / (i.factorial : ℚ)) • iter D₃ k (iter D₂ j (iter D₁ i a)))) := by
  simp only [taylorHom₃, RingHom.comp_apply, PowerSeries.coeff_map, coeff_taylorHom,
    map_smul]

theorem iter_commute (D E : Derivation ℚ R R)
    (h : Commute D.toLinearMap E.toLinearMap) (i j : ℕ) (a : R) :
    iter D i (iter E j a) = iter E j (iter D i a) := by
  exact LinearMap.congr_fun ((h.pow_left i).pow_right j).eq a

abbrev Series₃ (K : Type*) := PowerSeries (PowerSeries (PowerSeries K))

variable (K : Type*) [CommRing K]

def coordinate : Fin 3 → Series₃ K
  | 0 => PowerSeries.X
  | 1 => PowerSeries.C PowerSeries.X
  | 2 => PowerSeries.C (PowerSeries.C PowerSeries.X)

def rectangleIdeal (t : Fin 3 → ℕ) : Ideal (Series₃ K) :=
  Ideal.span (Set.range fun j => coordinate K j ^ (t j + 1))

abbrev Rectangle (t : Fin 3 → ℕ) := Series₃ K ⧸ rectangleIdeal K t

def rectangleTaylor (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K)
    (t : Fin 3 → ℕ) : R →+* Rectangle K t :=
  (Ideal.Quotient.mk (rectangleIdeal K t)).comp
    ((PowerSeries.map (PowerSeries.map (PowerSeries.map ρ))).comp
      (taylorHom₃ D₁ D₂ D₃))

theorem coordinate_pow_eq_zero (t : Fin 3 → ℕ) (j : Fin 3) :
    Ideal.Quotient.mk (rectangleIdeal K t)
      (coordinate K j ^ (t j + 1)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  exact ⟨j, rfl⟩

def truncationIdeal (n : ℕ) : Ideal (PowerSeries K) :=
  Ideal.span {PowerSeries.X ^ n}

theorem truncation_eq_zero_iff (n : ℕ) (f : PowerSeries K) :
    Ideal.Quotient.mk (truncationIdeal K n) f = 0 ↔
      ∀ k < n, PowerSeries.coeff k f = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, truncationIdeal,
    Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

variable [Algebra ℚ K]

theorem taylor_truncation_eq_zero (D : Derivation ℚ R R) (ρ : R →+* K)
    (n : ℕ) (a : R) (ha : ∀ k < n, ρ (iter D k a) = 0) :
    Ideal.Quotient.mk (truncationIdeal K n)
      (PowerSeries.map ρ (taylorHom D a)) = 0 := by
  rw [truncation_eq_zero_iff]
  intro k hk
  rw [PowerSeries.coeff_map, coeff_taylorHom, map_rat_smul, ha k hk, smul_zero]

end Result.Workers.W57



namespace Result.Workers.W57

variable (K : Type*) [CommRing K]

abbrev Jet (n : ℕ) := PowerSeries K ⧸ truncationIdeal K n

instance jetCommRing (n : ℕ) : CommRing (Jet K n) :=
  Ideal.Quotient.commRing (truncationIdeal K n)

instance jetAlgebra {S : Type*} [CommRing S] [Algebra S K] (n : ℕ) :
    Algebra S (Jet K n) :=
  inferInstanceAs (Algebra S (PowerSeries K ⧸ truncationIdeal K n))

def jetProjection (n : ℕ) : PowerSeries K →+* Jet K n :=
  Ideal.Quotient.mk (truncationIdeal K n)

abbrev RectangleJet (a b c : ℕ) := Jet (Jet (Jet K c) b) a

instance rectangleJetCommRing (a b c : ℕ) : CommRing (RectangleJet K a b c) :=
  jetCommRing (Jet (Jet K c) b) a

instance rectangleJetAlgebra {S : Type*} [CommRing S] [Algebra S K] (a b c : ℕ) :
    Algebra S (RectangleJet K a b c) :=
  jetAlgebra (S := S) (Jet (Jet K c) b) a

def rectangleProjection (a b c : ℕ) : Series₃ K →+* RectangleJet K a b c :=
  (jetProjection (Jet (Jet K c) b) a).comp
    ((PowerSeries.map (jetProjection (Jet K c) b)).comp
      (PowerSeries.map (PowerSeries.map (jetProjection K c))))

theorem rectangleProjection_eq_zero_iff (a b c : ℕ) (f : Series₃ K) :
    rectangleProjection K a b c f = 0 ↔
    ∀ i < a, ∀ j < b, ∀ k < c,
      PowerSeries.coeff k (PowerSeries.coeff j (PowerSeries.coeff i f)) = 0 := by
  simp only [rectangleProjection, RingHom.comp_apply, jetProjection,
    truncation_eq_zero_iff, PowerSeries.coeff_map]

variable {R : Type*} [CommRing R] [Algebra ℚ R] [Algebra ℚ K]

def rectangularJetHom (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K)
    (a b c : ℕ) : R →+* RectangleJet K a b c :=
  (rectangleProjection K a b c).comp
    ((PowerSeries.map (PowerSeries.map (PowerSeries.map ρ))).comp
      (taylorHom₃ D₁ D₂ D₃))

theorem rectangularJetHom_eq_zero (D₁ D₂ D₃ : Derivation ℚ R R) (ρ : R →+* K)
    (a b c : ℕ) (f : R)
    (hf : ∀ i < a, ∀ j < b, ∀ k < c,
      ρ (iter D₃ k (iter D₂ j (iter D₁ i f))) = 0) :
    rectangularJetHom K D₁ D₂ D₃ ρ a b c f = 0 := by
  change rectangleProjection K a b c
    (PowerSeries.map (PowerSeries.map (PowerSeries.map ρ))
      (taylorHom₃ D₁ D₂ D₃ f)) = 0
  rw [rectangleProjection_eq_zero_iff]
  intro i hi j hj k hk
  simp only [PowerSeries.coeff_map, coeff_taylorHom₃, map_rat_smul]
  rw [hf i hi j hj k hk]
  simp

end Result.Workers.W57



namespace WeightedTorusJets.W19

open WeightedTorusJets.W18
open MvPolynomial

section Polynomial
variable {σ R : Type*} [CommSemiring R] [Fintype σ]

theorem mixedInvariant_comp (v : Fin 3 → σ → R) (α a : Fin 3 → ℕ)
    (p : MvPolynomial σ R) :
    mixedInvariant v α (mixedInvariant v a p) = mixedInvariant v (α + a) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n r =>
      simp only [mixedInvariant_monomial, Pi.add_apply, pow_add]
      congr 1
      ac_rfl
  | add p q hp hq => simp only [mixedInvariant_add, hp, hq]

end Polynomial

theorem rectangle_index_add_bound (b : ℕ) (t α a : Fin 3 → ℕ)
    (hα : ∀ j, α j ≤ t j) (ha : ∀ j, a j ≤ b * t j) :
    ∀ j, (α + a) j ≤ (b + 1) * t j := by
  intro j
  change α j + a j ≤ (b + 1) * t j
  calc
    α j + a j ≤ t j + b * t j := Nat.add_le_add (hα j) (ha j)
    _ = (b + 1) * t j := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

section Taylor
open Result.Workers.W57
variable {R K : Type*} [CommRing R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K]

def derivativeTriple (D : Fin 3 → Derivation ℚ R R) (a : Fin 3 → ℕ) (f : R) : R :=
  iter (D 2) (a 2) (iter (D 1) (a 1) (iter (D 0) (a 0) f))

theorem iter_add_apply (D : Derivation ℚ R R) (i j : ℕ) (f : R) :
    iter D i (iter D j f) = iter D (i+j) f := by
  simp only [iter, pow_add, Module.End.mul_apply]

theorem derivativeTriple_comp (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (α a : Fin 3 → ℕ) (f : R) :
    derivativeTriple D α (derivativeTriple D a f) = derivativeTriple D (α+a) f := by
  unfold derivativeTriple
  rw [iter_commute (D 0) (D 2) (hD 0 2) (α 0) (a 2)]
  rw [iter_commute (D 1) (D 2) (hD 1 2) (α 1) (a 2)]
  rw [iter_commute (D 0) (D 1) (hD 0 1) (α 0) (a 1)]
  simp only [iter_add_apply, Pi.add_apply]

def rectangleGenerators (D : Fin 3 → Derivation ℚ R R)
    (t : Fin 3 → ℕ) (b : ℕ) (f : R) : Set R :=
  {g | ∃ a : Fin 3 → ℕ, (∀ j, a j ≤ b * t j) ∧ g = derivativeTriple D a f}

theorem derivativeTriple_mem_next_rectangle (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (t : Fin 3 → ℕ) (b : ℕ) (f g : R) (α : Fin 3 → ℕ)
    (hg : g ∈ rectangleGenerators D t b f) (hα : ∀ j, α j ≤ t j) :
    derivativeTriple D α g ∈ rectangleGenerators D t (b+1) f := by
  rcases hg with ⟨a, ha, rfl⟩
  exact ⟨α+a, rectangle_index_add_bound b t α a hα ha,
    derivativeTriple_comp D hD α a f⟩

theorem rectangularJetHom_generator_eq_zero (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (ρ : R →+* K) (t : Fin 3 → ℕ) (b : ℕ) (f g : R)
    (hnext : ∀ u ∈ rectangleGenerators D t (b+1) f, ρ u = 0)
    (hg : g ∈ rectangleGenerators D t b f) :
    rectangularJetHom K (D 0) (D 1) (D 2) ρ (t 0+1) (t 1+1) (t 2+1) g = 0 := by
  apply rectangularJetHom_eq_zero
  intro i hi j hj k hk
  have hα : ∀ m : Fin 3, (![i,j,k] : Fin 3 → ℕ) m ≤ t m := by
    intro m
    fin_cases m
    · simpa using (Nat.le_of_lt_succ hi)
    · simpa using (Nat.le_of_lt_succ hj)
    · simpa using (Nat.le_of_lt_succ hk)
  exact hnext _ (derivativeTriple_mem_next_rectangle D hD t b f g ![i,j,k] hg hα)

theorem rectangle_span_le_jet_ker (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (ρ : R →+* K) (t : Fin 3 → ℕ) (b : ℕ) (f : R)
    (hnext : ∀ u ∈ rectangleGenerators D t (b+1) f, ρ u = 0) :
    Ideal.span (rectangleGenerators D t b f) ≤
      RingHom.ker (rectangularJetHom K (D 0) (D 1) (D 2) ρ
        (t 0+1) (t 1+1) (t 2+1)) := by
  apply Ideal.span_le.mpr
  intro g hg
  exact RingHom.mem_ker.mpr
    (rectangularJetHom_generator_eq_zero D hD ρ t b f g hnext hg)

end Taylor

open Result.Workers.W57
variable {σ R : Type*} [CommRing R] [Algebra ℚ R] [Fintype σ]

def rationalInvariant (v : σ → R) :
    Derivation ℚ (MvPolynomial σ R) (MvPolynomial σ R) :=
  (invariantDerivation v).restrictScalars ℚ

theorem rationalInvariant_commute (v w : σ → R) :
    Commute (rationalInvariant v).toLinearMap (rationalInvariant w).toLinearMap := by
  change (rationalInvariant v).toLinearMap * (rationalInvariant w).toLinearMap =
    (rationalInvariant w).toLinearMap * (rationalInvariant v).toLinearMap
  apply LinearMap.ext
  intro p
  exact invariantDerivation_commute v w p

theorem iter_rationalInvariant (v : σ → R) (a : ℕ) (p : MvPolynomial σ R) :
    iter (rationalInvariant v) a p = iteratedInvariant v a p := by
  induction a with
  | zero => rfl
  | succ a ha =>
      rw [iter_succ, ha]
      change invariantDerivation v (iteratedInvariant v a p) = _
      simp only [iteratedInvariant, Function.iterate_succ_apply']

theorem derivativeTriple_rationalInvariant (v : Fin 3 → σ → R)
    (a : Fin 3 → ℕ) (p : MvPolynomial σ R) :
    derivativeTriple (fun j => rationalInvariant (v j)) a p = mixedInvariant v a p := by
  simp only [derivativeTriple, iter_rationalInvariant, mixedInvariant]
  rw [iteratedInvariant_commute (v 1) (v 0) (a 1) (a 0)]
  rw [iteratedInvariant_commute (v 2) (v 0) (a 2) (a 0)]
  rw [iteratedInvariant_commute (v 2) (v 1) (a 2) (a 1)]

end WeightedTorusJets.W19

end

end SiegelZeros

end OAI
