import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace OAI

/-!
# Automorphic section spaces, Laurent recurrences, and period freeness
-/

section

/-!
Concrete holomorphic multiplier sections on the punctured complex plane.
The value at zero is fixed to zero, solely to represent functions on `ℂ*`
as ordinary functions `ℂ → ℂ` without introducing an extra free coefficient.
No dimension, spanning, existence, or Nagata conclusion is a structure field.
-/
namespace Nagata.W08

open Filter Topology

/-- Holomorphic functions on `ℂ*` with the multiplier of `D(n,γ)`.
The zero extension at the omitted point is part of the representation. -/
noncomputable def automorphicSections (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Submodule ℂ (ℂ → ℂ) where
  carrier := {f | f 0 = 0 ∧ (∀ z, z ≠ 0 → DifferentiableAt ℂ f z) ∧
    (∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z)}
  zero_mem' := by
    refine ⟨rfl, ?_, ?_⟩
    · intro z _
      exact differentiableAt_const 0
    · intro z _
      simp
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_, ?_⟩
    · change f 0 + g 0 = 0
      rw [hf.1, hg.1, add_zero]
    · intro z hz
      exact (hf.2.1 z hz).add (hg.2.1 z hz)
    · intro z hz
      change f (τ * z) + g (τ * z) = γ * z ^ (-n) * (f z + g z)
      rw [hf.2.2 z hz, hg.2.2 z hz, mul_add]
  smul_mem' := by
    intro a f hf
    refine ⟨?_, ?_, ?_⟩
    · change a * f 0 = 0
      rw [hf.1, mul_zero]
    · intro z hz
      exact (hf.2.1 z hz).const_smul a
    · intro z hz
      change a * f (τ * z) = γ * z ^ (-n) * (a * f z)
      rw [hf.2.2 z hz]
      ac_rfl

@[simp] theorem mem_automorphicSections_iff {τ γ : ℂ} {n : ℤ} {f : ℂ → ℂ} :
    f ∈ automorphicSections τ n γ ↔
      f 0 = 0 ∧ (∀ z, z ≠ 0 → DifferentiableAt ℂ f z) ∧
      (∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) := Iff.rfl

/-- Agreement on the genuine domain `ℂ*` determines the represented section. -/
theorem automorphicSections_ext {τ γ : ℂ} {n : ℤ}
    (f g : automorphicSections τ n γ)
    (h : ∀ z, z ≠ 0 → f.val z = g.val z) : f = g := by
  apply Subtype.ext
  funext z
  by_cases hz : z = 0
  · subst z
    exact f.property.1.trans g.property.1.symm
  · exact h z hz

/-- Forget the forced zero value and restrict to the actual punctured-plane domain. -/
def sectionRestriction (τ : ℂ) (n : ℤ) (γ : ℂ) :
    automorphicSections τ n γ →ₗ[ℂ] ({z : ℂ // z ≠ 0} → ℂ) where
  toFun f z := f.val z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The zero-extension representation adds no sections invisible on `ℂ*`. -/
theorem sectionRestriction_injective (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Function.Injective (sectionRestriction τ n γ) := by
  intro f g h
  apply automorphicSections_ext
  intro z hz
  exact congrFun h ⟨z, hz⟩

/-- Extend the values on `ℂ*` by zero at the omitted point. -/
noncomputable def normalizeAtZero (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else f z

@[simp] theorem normalizeAtZero_zero (f : ℂ → ℂ) : normalizeAtZero f 0 = 0 := by
  simp [normalizeAtZero]

@[simp] theorem normalizeAtZero_of_ne (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    normalizeAtZero f z = f z := by
  simp [normalizeAtZero, hz]

/-- Changing the value at zero changes no germ on the punctured plane. -/
theorem normalizeAtZero_eventuallyEq (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    normalizeAtZero f =ᶠ[𝓝 z] f :=
  (eventually_ne_nhds hz).mono fun point hpoint ↦ normalizeAtZero_of_ne f (z := point) hpoint

/-- The zero-extension representation preserves holomorphy at every genuine point. -/
theorem normalizeAtZero_differentiableAt_iff (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (normalizeAtZero f) z ↔ DifferentiableAt ℂ f z :=
  (normalizeAtZero_eventuallyEq f hz).differentiableAt_iff

/-- Construct a concrete section from an actual holomorphic automorphic function.
The assumptions state only holomorphy and the defining multiplier equation. -/
theorem normalizeAtZero_mem_automorphicSections {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) :
    normalizeAtZero f ∈ automorphicSections τ n γ := by
  refine ⟨normalizeAtZero_zero f, ?_, ?_⟩
  · intro z hz
    exact (normalizeAtZero_differentiableAt_iff f hz).mpr (hf z hz)
  · intro z hz
    rw [normalizeAtZero_of_ne f (mul_ne_zero hτ hz), normalizeAtZero_of_ne f hz]
    exact he z hz

/-- The resulting element of the genuine section space. -/
noncomputable def sectionOfFunction {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) :
    automorphicSections τ n γ :=
  ⟨normalizeAtZero f, normalizeAtZero_mem_automorphicSections hτ f hf he⟩

@[simp] theorem sectionOfFunction_apply {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z)
    {z : ℂ} (hz : z ≠ 0) :
    (sectionOfFunction hτ f hf he).val z = f z :=
  normalizeAtZero_of_ne f hz

end Nagata.W08

end

section

universe u

namespace Nagata.W08

/-- The integer-valued quadratic appearing in a bi-infinite Laurent orbit. -/
def triangular (p : Int) : Int := p * (p - 1) / 2

@[simp] theorem triangular_zero : triangular 0 = 0 := by decide

/-- This identity is valid also for negative `p`. -/
theorem triangular_add_one (p : Int) : triangular (p + 1) = triangular p + p := by
  unfold triangular
  have h : (p + 1) * (p + 1 - 1) = p * (p - 1) + 2 * p := by
    simp only [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
    omega
  rw [h]
  omega

theorem triangular_sub_one (p : Int) : triangular (p - 1) = triangular p - (p - 1) := by
  have h := triangular_add_one (p - 1)
  have he : p - 1 + 1 = p := by omega
  rw [he] at h
  omega

/-- The exact exponent, before distributing the factor `n` inside the quotient. -/
def laurentExponent (n K p : Int) : Int := p * K + n * triangular p

@[simp] theorem laurentExponent_zero (n K : Int) : laurentExponent n K 0 = 0 := by
  simp [laurentExponent]

theorem laurentExponent_add_one (n K p : Int) :
    laurentExponent n K (p + 1) = laurentExponent n K p + (K + n * p) := by
  simp only [laurentExponent, triangular_add_one, Int.add_mul, Int.one_mul, Int.mul_add]
  omega

theorem laurentExponent_sub_one (n K p : Int) :
    laurentExponent n K (p - 1) = laurentExponent n K p - (K + n * (p - 1)) := by
  have h := laurentExponent_add_one n K (p - 1)
  have he : p - 1 + 1 = p := by omega
  rw [he] at h
  omega

/-- A recurrence with reversible transitions is determined at every integer by its value at zero. -/
theorem biInfinite_unique {α : Type u} (step : Int → α → α)
    (injective_step : ∀ p x y, step p x = step p y → x = y)
    (a b : Int → α) (ha : ∀ p, a (p + 1) = step p (a p))
    (hb : ∀ p, b (p + 1) = step p (b p)) (hzero : a 0 = b 0) : a = b := by
  have hnat : ∀ k : Nat, a (k : Int) = b (k : Int) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      have hindex : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hindex, ha, hb, ih]
  have hneg : ∀ k : Nat, a (-(k : Int)) = b (-(k : Int)) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      apply injective_step (-((k + 1 : Nat) : Int))
      rw [← ha, ← hb]
      have hindex : -((k + 1 : Nat) : Int) + 1 = -(k : Int) := by omega
      rw [hindex]
      exact ih
  funext p
  cases p with
  | ofNat k => exact hnat k
  | negSucc k =>
    have hindex : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
    rw [hindex]
    exact hneg (k + 1)

/-- The division in the triangular exponent is exact, for every integer. -/
theorem two_mul_triangular (p : Int) : 2 * triangular p = p * (p - 1) := by
  have heq : (fun p : Int => 2 * triangular p) = (fun p : Int => p * (p - 1)) := by
    apply biInfinite_unique (fun p x => x + 2 * p)
    · intro p x y h
      omega
    · intro p
      rw [triangular_add_one, Int.mul_add]
    · intro p
      simp only [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
      omega
    · decide
  exact congrFun heq p

theorem two_dvd_mul_pred (p : Int) : (2 : Int) ∣ p * (p - 1) :=
  ⟨triangular p, (two_mul_triangular p).symm⟩

/-- Moves `n` through the exact integer quotient in the manuscript exponent. -/
theorem laurentExponent_eq_source (n K p : Int) :
    laurentExponent n K p = p * K + n * p * (p - 1) / 2 := by
  unfold laurentExponent triangular
  rw [← Int.mul_ediv_assoc n (two_dvd_mul_pred p), Int.mul_assoc]

end Nagata.W08

end

section

/-! Freeness of the source's multiplicative period action. -/
namespace Nagata.W08

/-- A complex period strictly inside the unit circle has no nontrivial integral period. -/
theorem period_zpow_eq_one {τ : ℂ} (hτ : ‖τ‖ < 1) {k : ℤ}
    (hk : τ ^ k = 1) : k = 0 := by
  have hnorm := congrArg norm hk
  rw [norm_zpow, norm_one] at hnorm
  exact (zpow_eq_one_iff_right₀ (norm_nonneg τ) (ne_of_lt hτ)).mp hnorm

/-- The period acts freely on every nonzero point. -/
theorem period_zpow_mul_eq_self {τ z : ℂ} (hτ : ‖τ‖ < 1) (hz : z ≠ 0)
    {k : ℤ} (hk : τ ^ k * z = z) : k = 0 := by
  apply period_zpow_eq_one hτ
  exact mul_right_cancel₀ hz (hk.trans (one_mul z).symm)

/-- The unit-valued form used by the genuine torus and multiplier quotients. -/
theorem unitPeriod_free (τ : ℂˣ) (hτ : ‖(τ : ℂ)‖ < 1) (k : ℤ)
    (hk : τ ^ k = 1) : k = 0 := by
  apply period_zpow_eq_one hτ
  simpa only [Units.val_zpow_eq_zpow_val, Units.val_one] using
    congrArg (fun u : ℂˣ ↦ (u : ℂ)) hk

end Nagata.W08

end

section

/-!
Global gluing across the principal-logarithm branch cut. An entire function
invariant under the actual exponential deck transformations descends to a
holomorphic function on all of the punctured complex plane.
-/
noncomputable section
namespace Nagata.W08

open Filter Topology

/-- Equality of exponential images identifies values of a deck-invariant function. -/
theorem periodic_eq_of_exp_eq (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {x y : ℂ} (hxy : Complex.exp x = Complex.exp y) : F x = F y := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  rw [hk, hperiod]

/-- Use any local logarithm about `z₀`; the value agrees with the principal-log formula. -/
theorem periodic_log_eq_localLog (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0) :
    F (Complex.log z) = F (Complex.log (z / z₀) + Complex.log z₀) := by
  apply periodic_eq_of_exp_eq F hperiod
  rw [Complex.exp_log hz, Complex.exp_add, Complex.exp_log (div_ne_zero hz hz₀),
    Complex.exp_log hz₀, div_mul_cancel₀ _ hz₀]

/-- The expression using principal log is holomorphic even at its branch cut,
because locally it agrees with a holomorphic choice centered at the point. -/
theorem periodic_log_differentiableAt (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    DifferentiableAt ℂ (fun z ↦ F (Complex.log z)) z₀ := by
  have hdiv : DifferentiableAt ℂ (fun z : ℂ ↦ z / z₀) z₀ := by
    simp only [div_eq_mul_inv]
    exact differentiableAt_id.mul_const _
  have hslit : z₀ / z₀ ∈ Complex.slitPlane := by
    simp [div_self hz₀]
  have hlocal : DifferentiableAt ℂ
      (fun z : ℂ ↦ Complex.log (z / z₀) + Complex.log z₀) z₀ :=
    ((Complex.differentiableAt_log hslit).comp z₀ (f := fun z : ℂ ↦ z / z₀) hdiv).add
      (differentiableAt_const (Complex.log z₀))
  have hg := (hF (Complex.log (z₀ / z₀) + Complex.log z₀)).comp z₀ hlocal
  apply hg.congr_of_eventuallyEq
  exact (eventually_ne_nhds hz₀).mono fun z hz ↦
    periodic_log_eq_localLog F hperiod hz hz₀

/-- A shift law on the exponential cover gives the actual multiplicative law on `ℂ*`. -/
theorem periodic_log_automorphy (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x)
    {z : ℂ} (hz : z ≠ 0) :
    F (Complex.log (τ * z)) = γ * z ^ (-n) * F (Complex.log z) := by
  have heq : F (Complex.log (τ * z)) = F (Complex.log z + Complex.log τ) := by
    apply periodic_eq_of_exp_eq F hperiod
    rw [Complex.exp_log (mul_ne_zero hτ hz), Complex.exp_add,
      Complex.exp_log hz, Complex.exp_log hτ, mul_comm]
  rw [heq, hshift, Complex.exp_int_mul, Complex.exp_log hz]

/-- Package the descended actual function as a genuine holomorphic multiplier section.
Entire holomorphy, deck invariance and the scalar shift law remain explicit inputs. -/
def automorphicSectionOfPeriodicFunction (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x) :
    automorphicSections τ n γ :=
  sectionOfFunction hτ (fun z ↦ F (Complex.log z))
    (fun _ hz ↦ periodic_log_differentiableAt F hF hperiod hz)
    (fun _ hz ↦ periodic_log_automorphy F hperiod hτ hshift hz)

/-- Every exponential-cover value is recovered exactly, independently of branch choices. -/
theorem automorphicSectionOfPeriodicFunction_exp (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x) (x : ℂ) :
    (automorphicSectionOfPeriodicFunction F hF hperiod hτ hshift).val (Complex.exp x) = F x := by
  change normalizeAtZero (fun z ↦ F (Complex.log z)) (Complex.exp x) = F x
  rw [normalizeAtZero_of_ne _ (Complex.exp_ne_zero x)]
  apply periodic_eq_of_exp_eq F hperiod
  exact Complex.exp_log (Complex.exp_ne_zero x)

end Nagata.W08

end
end

section

/-!
The algebraic iteration part of `lem:torus-sections`, equation
`eq:laurent-recurrence`. This does not assume or establish existence of a
holomorphic Laurent expansion, convergence, or the section-space dimension.
-/
namespace Nagata.W08

variable {F : Type*} [CommGroupWithZero F]

/-- Candidate values along one residue class. The starting coefficient can be zero. -/
def orbitValue (τ γ : F) (n K : ℤ) (c₀ : F) (p : ℤ) : F :=
  γ ^ (-p) * τ ^ (laurentExponent n K p) * c₀

@[simp] theorem orbitValue_zero (τ γ : F) (n K : ℤ) (c₀ : F) :
    orbitValue τ γ n K c₀ 0 = c₀ := by
  simp [orbitValue]

theorem orbitValue_add_one (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n K : ℤ) (c₀ : F) (p : ℤ) :
    orbitValue τ γ n K c₀ (p + 1) =
      (γ⁻¹ * τ ^ (K + n * p)) * orbitValue τ γ n K c₀ p := by
  unfold orbitValue
  rw [show -(p + 1) = -1 + -p by omega, zpow_add₀ hγ, zpow_neg_one,
    laurentExponent_add_one, zpow_add₀ hτ]
  ac_rfl

/-- The Laurent recurrence iterated through all integers, including negative ones. -/
theorem laurent_recurrence_all_int (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hc : ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K) (K p : ℤ) :
    c (K + n * p) = c K * γ ^ (-p) * τ ^ (p * K + n * (p * (p - 1) / 2)) := by
  have horbit : (fun p : ℤ => c (K + n * p)) = orbitValue τ γ n K (c K) := by
    apply biInfinite_unique (fun p x => (γ⁻¹ * τ ^ (K + n * p)) * x)
    · intro p
      exact fun _ _ h => mul_left_cancel₀
        (mul_ne_zero (inv_ne_zero hγ) (zpow_ne_zero _ hτ)) h
    · intro p
      have hindex : K + n * (p + 1) = K + n * p + n := by
        simp only [Int.mul_add, Int.mul_one]
        omega
      rw [hindex, hc]
    · exact orbitValue_add_one τ γ hτ hγ n K (c K)
    · simp
  have hvalue := congrFun horbit p
  simpa only [orbitValue, laurentExponent, triangular, mul_assoc, mul_comm, mul_left_comm]
    using hvalue

/-- The formula exactly as printed in `eq:laurent-recurrence`. -/
theorem laurent_recurrence_source_formula (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hc : ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K) (K p : ℤ) :
    c (K + n * p) = c K * γ ^ (-p) * τ ^ (p * K + n * p * (p - 1) / 2) := by
  have h := laurent_recurrence_all_int τ γ hτ hγ n c hc K p
  change c (K + n * p) = c K * γ ^ (-p) * τ ^ (laurentExponent n K p) at h
  rw [laurentExponent_eq_source] at h
  exact h

/-- Rearrangement of the coefficient equality obtained from the functional equation. -/
theorem recurrence_of_coefficient_balance (τ γ : F) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hbalance : ∀ K, τ ^ K * c K = γ * c (K + n)) :
    ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K := by
  intro K
  calc
    c (K + n) = γ⁻¹ * (γ * c (K + n)) := (inv_mul_cancel_left₀ hγ _).symm
    _ = γ⁻¹ * (τ ^ K * c K) := by rw [← hbalance]
    _ = γ⁻¹ * τ ^ K * c K := (mul_assoc _ _ _).symm

/-- The entire bi-infinite formula follows from the coefficient balance equation. -/
theorem laurent_formula_of_coefficient_balance (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hbalance : ∀ K, τ ^ K * c K = γ * c (K + n)) (K p : ℤ) :
    c (K + n * p) = c K * γ ^ (-p) * τ ^ (p * K + n * p * (p - 1) / 2) :=
  laurent_recurrence_source_formula τ γ hτ hγ n c
    (recurrence_of_coefficient_balance τ γ hγ n c hbalance) K p

end Nagata.W08

end

end OAI
