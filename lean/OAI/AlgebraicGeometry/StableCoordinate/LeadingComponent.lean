import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Leading components of locally nilpotent derivations

This module supplies the graded-algebra mechanism used in §5 of the
source.  Integer degrees are allowed, including negative degrees.
-/

noncomputable section

namespace StableCoordinate
namespace LeadingComponent

open DirectSum

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Projection to one homogeneous component, regarded as an endomorphism. -/
abbrev proj (i : ℤ) : A →ₗ[k] A := GradedAlgebra.proj 𝒜 i

@[simp] theorem proj_mem (i : ℤ) (x : A) : proj 𝒜 i x ∈ 𝒜 i :=
  (DirectSum.decompose 𝒜 x i).property

theorem proj_of_mem {x : A} {i : ℤ} (hx : x ∈ 𝒜 i) : proj 𝒜 i x = x :=
  DirectSum.decompose_of_mem_same 𝒜 hx

theorem proj_of_mem_ne {x : A} {i j : ℤ} (hx : x ∈ 𝒜 i) (hij : i ≠ j) :
    proj 𝒜 j x = 0 :=
  DirectSum.decompose_of_mem_ne 𝒜 hx hij

theorem proj_mul_left {x y : A} {i j : ℤ} (hx : x ∈ 𝒜 i) :
    proj 𝒜 (i + j) (x * y) = x * proj 𝒜 j y :=
  DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hx

/-- The part of a linear map that raises homogeneous degree by exactly `m`. -/
def componentLinear (D : A →ₗ[k] A) (m : ℤ) : A →ₗ[k] A :=
  (DirectSum.toModule k ℤ A fun i =>
    (proj 𝒜 (i + m)).comp (D.comp (𝒜 i).subtype)).comp
      (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem componentLinear_of_mem (D : A →ₗ[k] A) (m : ℤ)
    {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) :
    componentLinear 𝒜 D m x = proj 𝒜 (i + m) (D x) := by
  let x' : 𝒜 i := ⟨x, hx⟩
  change componentLinear 𝒜 D m (x' : A) = _
  simp only [componentLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof,
    Submodule.subtype_apply]
  rfl

theorem componentLinear_mem (D : A →ₗ[k] A) (m : ℤ)
    {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) :
    componentLinear 𝒜 D m x ∈ 𝒜 (i + m) := by
  rw [componentLinear_of_mem 𝒜 D m hx]
  exact proj_mem 𝒜 _ _

theorem componentLinear_one (D : Derivation k A A) (m : ℤ) :
    componentLinear 𝒜 D.toLinearMap m 1 = 0 := by
  rw [componentLinear_of_mem 𝒜 _ m (SetLike.GradedOne.one_mem (A := 𝒜))]
  change proj 𝒜 (0 + m) (D 1) = 0
  rw [Derivation.map_one_eq_zero, map_zero]

theorem componentLinear_mul (D : Derivation k A A) (m : ℤ) (x y : A) :
    componentLinear 𝒜 D.toLinearMap m (x * y) =
      x * componentLinear 𝒜 D.toLinearMap m y +
      y * componentLinear 𝒜 D.toLinearMap m x := by
  let E := componentLinear 𝒜 D.toLinearMap m
  change E (x * y) = x * E y + y * E x
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous x =>
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous y =>
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      dsimp only at *
      dsimp only [E]
      rw [componentLinear_of_mem 𝒜 _ m (SetLike.GradedMul.mul_mem hx hy),
        componentLinear_of_mem 𝒜 _ m hx, componentLinear_of_mem 𝒜 _ m hy]
      change proj 𝒜 _ (D (x * y)) = _
      rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add]
      have h₁ : ∀ i j : ℤ, i + j + m = i + (j + m) := by omega
      have h₂ : ∀ i j : ℤ, i + j + m = j + (i + m) := by omega
      rw [h₁, proj_mul_left 𝒜 hx]
      congr 1
      rw [← h₁, h₂, proj_mul_left 𝒜 hy]
      rfl
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]; ring
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]; ring

/-- Every homogeneous degree-shift component of a derivation is itself a derivation. -/
def component (D : Derivation k A A) (m : ℤ) : Derivation k A A where
  toLinearMap := componentLinear 𝒜 D.toLinearMap m
  map_one_eq_zero' := componentLinear_one 𝒜 D m
  leibniz' x y := by
    simpa only [smul_eq_mul] using componentLinear_mul 𝒜 D m x y

@[simp] theorem component_apply (D : Derivation k A A) (m : ℤ) (x : A) :
    component 𝒜 D m x = componentLinear 𝒜 D.toLinearMap m x := rfl

theorem component_of_mem (D : Derivation k A A) (m : ℤ)
    {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) :
    component 𝒜 D m x = proj 𝒜 (i + m) (D x) :=
  componentLinear_of_mem 𝒜 D.toLinearMap m hx

theorem component_mem (D : Derivation k A A) (m : ℤ)
    {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) :
    component 𝒜 D m x ∈ 𝒜 (i + m) :=
  componentLinear_mem 𝒜 D.toLinearMap m hx

/-- Every homogeneous component above degree `d` vanishes. -/
def DegreeLE (d : ℤ) (x : A) : Prop :=
  ∀ j : ℤ, d < j → proj 𝒜 j x = 0

theorem degreeLE_of_mem {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) :
    DegreeLE 𝒜 i x := by
  intro j hj
  exact proj_of_mem_ne 𝒜 hx (ne_of_lt hj)

theorem degreeLE_zero (i : ℤ) : DegreeLE 𝒜 i (0 : A) := by
  intro j _
  exact map_zero _

theorem le_of_proj_ne_zero_of_degreeLE {d : ℤ} {x : A}
    (hx : DegreeLE 𝒜 d x) {i : ℤ}
    (hi : proj 𝒜 i x ≠ 0) : i ≤ d := by
  by_contra h
  exact hi (hx i (lt_of_not_ge h))

/-- A map's degree shift is bounded above by `m`.  This does not require
lower bounds and therefore applies to the source's integer gradings. -/
def HasShiftLE (D : A →ₗ[k] A) (m : ℤ) : Prop :=
  ∀ (i : ℤ) (x : A), x ∈ 𝒜 i → DegreeLE 𝒜 (i + m) (D x)

theorem degreeLE_map (D : A →ₗ[k] A) {m d : ℤ}
    (hD : HasShiftLE 𝒜 D m) {x : A} (hx : DegreeLE 𝒜 d x) :
    DegreeLE 𝒜 (d + m) (D x) := by
  classical
  intro j hj
  have hsum : ∑ i ∈ (DirectSum.decompose 𝒜 x).support, proj 𝒜 i x = x :=
    DirectSum.sum_support_decompose 𝒜 x
  rw [← hsum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hid := le_of_proj_ne_zero_of_degreeLE 𝒜 hx ((GradedAlgebra.mem_support_iff 𝒜 x i).mp hi)
  exact hD i (proj 𝒜 i x) (proj_mem 𝒜 i x) j (by omega)

/-- At the degree bound, only the top input component can contribute to
the top output component. -/
theorem top_projection_map (D : A →ₗ[k] A) {m d : ℤ}
    (hD : HasShiftLE 𝒜 D m) {x : A} (hx : DegreeLE 𝒜 d x) :
    proj 𝒜 (d + m) (D x) = componentLinear 𝒜 D m (proj 𝒜 d x) := by
  classical
  rw [componentLinear_of_mem 𝒜 D m (proj_mem 𝒜 d x)]
  have hsum : ∑ i ∈ (DirectSum.decompose 𝒜 x).support, proj 𝒜 i x = x :=
    DirectSum.sum_support_decompose 𝒜 x
  conv_lhs => rw [← hsum, map_sum, map_sum]
  apply Finset.sum_eq_single d
  · intro i hi hid
    have hle := le_of_proj_ne_zero_of_degreeLE 𝒜 hx ((GradedAlgebra.mem_support_iff 𝒜 x i).mp hi)
    exact hD i (proj 𝒜 i x) (proj_mem 𝒜 i x) (d + m) (by omega)
  · intro hd
    have hzero : proj 𝒜 d x = 0 := by
      by_contra hne
      exact hd ((GradedAlgebra.mem_support_iff 𝒜 x d).mpr hne)
    simp only [hzero, map_zero]

theorem degreeLE_iterate (D : A →ₗ[k] A) {m i : ℤ}
    (hD : HasShiftLE 𝒜 D m) {x : A} (hx : x ∈ 𝒜 i) (n : ℕ) :
    DegreeLE 𝒜 (i + (n : ℤ) * m) ((D : A → A)^[n] x) := by
  induction n with
  | zero => simpa using degreeLE_of_mem 𝒜 hx
  | succ n hn =>
    rw [Function.iterate_succ_apply']
    convert degreeLE_map 𝒜 D hD hn using 1
    push_cast
    ring

/-- The highest possible homogeneous component of every iterate equals
the corresponding iterate of the leading component. -/
theorem top_projection_iterate (D : A →ₗ[k] A) {m i : ℤ}
    (hD : HasShiftLE 𝒜 D m) {x : A} (hx : x ∈ 𝒜 i) (n : ℕ) :
    proj 𝒜 (i + (n : ℤ) * m) ((D : A → A)^[n] x) =
      ((componentLinear 𝒜 D m : A → A)^[n] x) := by
  induction n with
  | zero => simpa using proj_of_mem 𝒜 hx
  | succ n hn =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hindex : i + ((n + 1 : ℕ) : ℤ) * m = (i + (n : ℤ) * m) + m := by
      push_cast
      ring
    rw [hindex, top_projection_map 𝒜 D hD (degreeLE_iterate 𝒜 D hD hx n), hn]

theorem iterate_linear_zero (D : A →ₗ[k] A) (n : ℕ) :
    (D : A → A)^[n] 0 = 0 := by
  rw [← Module.End.pow_apply]
  exact map_zero _

theorem iterate_linear_add (D : A →ₗ[k] A) (n : ℕ) (x y : A) :
    (D : A → A)^[n] (x + y) = (D : A → A)^[n] x + (D : A → A)^[n] y := by
  simp only [← Module.End.pow_apply, map_add]

theorem eventually_zero_add (D : A →ₗ[k] A) {x y : A}
    (hx : ∃ n : ℕ, (D : A → A)^[n] x = 0)
    (hy : ∃ n : ℕ, (D : A → A)^[n] y = 0) :
    ∃ n : ℕ, (D : A → A)^[n] (x + y) = 0 := by
  obtain ⟨nx, hx⟩ := hx
  obtain ⟨ny, hy⟩ := hy
  refine ⟨nx + ny, ?_⟩
  rw [iterate_linear_add]
  have hx' : (D : A → A)^[nx + ny] x = 0 := by
    rw [Nat.add_comm, Function.iterate_add_apply, hx, iterate_linear_zero]
  have hy' : (D : A → A)^[nx + ny] y = 0 := by
    rw [Function.iterate_add_apply, hy, iterate_linear_zero]
  rw [hx', hy', zero_add]

/-- Taking the highest allowed shift preserves local nilpotence.  No
sign assumption on `m`, no field hypothesis, and no characteristic
hypothesis are needed for this linear-algebra fact. -/
theorem locallyNilpotent_componentLinear (D : A →ₗ[k] A) {m : ℤ}
    (hD : HasShiftLE 𝒜 D m)
    (hln : ∀ x : A, ∃ n : ℕ, (D : A → A)^[n] x = 0) :
    ∀ x : A, ∃ n : ℕ, ((componentLinear 𝒜 D m : A → A)^[n] x) = 0 := by
  intro x
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, rfl⟩
  | homogeneous x =>
    obtain ⟨n, hn⟩ := hln x
    refine ⟨n, ?_⟩
    rw [← top_projection_iterate 𝒜 D hD x.property n, hn, map_zero]
  | add x y hx hy =>
    exact eventually_zero_add (componentLinear 𝒜 D m) hx hy

/-- The leading homogeneous component of a locally nilpotent derivation
is locally nilpotent, provided no component has larger degree shift. -/
theorem locallyNilpotent_component (D : Derivation k A A) {m : ℤ}
    (hD : HasShiftLE 𝒜 D.toLinearMap m)
    (hln : ∀ x : A, ∃ n : ℕ, (D : A → A)^[n] x = 0) :
    ∀ x : A, ∃ n : ℕ, ((component 𝒜 D m : A → A)^[n] x) = 0 :=
  locallyNilpotent_componentLinear 𝒜 D.toLinearMap hD hln

/-- A component is nonzero as soon as its value is nonzero on one
homogeneous element. -/
theorem component_ne_zero (D : Derivation k A A) (m : ℤ)
    {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) (hDx : proj 𝒜 (i + m) (D x) ≠ 0) :
    component 𝒜 D m ≠ 0 := by
  intro h
  have heq : component 𝒜 D m x = 0 := by rw [h]; rfl
  rw [component_of_mem 𝒜 D m hx] at heq
  exact hDx heq

/-- Every component annihilates any homogeneous element annihilated by
the original derivation. -/
theorem component_eq_zero_of_eq_zero (D : Derivation k A A) (m : ℤ)
    {i : ℤ} {x : A} (hx : x ∈ 𝒜 i) (hDx : D x = 0) :
    component 𝒜 D m x = 0 := by
  rw [component_of_mem 𝒜 D m hx, hDx, map_zero]

/-- If a derivation kills a sum with two distinct homogeneous degrees,
its leading component kills the higher-degree summand.  This is used with
`a³*b` of degree `-1` and `a²*u²-d²` of degree `2`. -/
theorem component_high_term_eq_zero (D : Derivation k A A) {m : ℤ}
    (hD : HasShiftLE 𝒜 D.toLinearMap m)
    {i j : ℤ} {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j)
    (hij : i < j) (hxy : D (x + y) = 0) : component 𝒜 D m y = 0 := by
  have hxzero : proj 𝒜 (j + m) (D x) = 0 :=
    hD i x hx (j + m) (by omega)
  have heq := congrArg (proj 𝒜 (j + m)) hxy
  rw [map_add, map_add, map_zero, hxzero, zero_add] at heq
  rw [component_of_mem 𝒜 D m hy]
  exact heq

theorem componentLinear_eq_sum [DecidableEq A] (D : A →ₗ[k] A) (m : ℤ) (x : A) :
    componentLinear 𝒜 D m x =
      ∑ i ∈ (DirectSum.decompose 𝒜 x).support, proj 𝒜 (i + m) (D (proj 𝒜 i x)) := by
  classical
  have hsum : ∑ i ∈ (DirectSum.decompose 𝒜 x).support, proj 𝒜 i x = x :=
    DirectSum.sum_support_decompose 𝒜 x
  conv_lhs => rw [← hsum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact componentLinear_of_mem 𝒜 D m (proj_mem 𝒜 i x)

/-- A homogeneous component preserves any submodule that is preserved
by the original map and by all grading projections. -/
theorem componentLinear_preserves (D : A →ₗ[k] A) (m : ℤ) (S : Submodule k A)
    (hS : ∀ (i : ℤ) (x : A), x ∈ S → proj 𝒜 i x ∈ S)
    (hD : ∀ x : A, x ∈ S → D x ∈ S) {x : A} (hx : x ∈ S) :
    componentLinear 𝒜 D m x ∈ S := by
  classical
  rw [componentLinear_eq_sum]
  apply Submodule.sum_mem
  intro i _
  exact hS (i + m) _ (hD _ (hS i x hx))

/-- Commuting gradings preserve one another's homogeneous submodules. -/
theorem projection_preserves_of_commute
    (ℬ : ℤ → Submodule k A) [GradedAlgebra ℬ]
    (hcomm : ∀ (i j : ℤ) (x : A),
      proj 𝒜 i (proj ℬ j x) = proj ℬ j (proj 𝒜 i x))
    {i j : ℤ} {x : A} (hx : x ∈ ℬ j) : proj 𝒜 i x ∈ ℬ j := by
  rw [← proj_of_mem ℬ hx, hcomm]
  exact proj_mem ℬ j _

/-- Taking an auxiliary-degree component preserves a compatible second
grading whenever the original derivation preserves that grading. -/
theorem component_preserves_compatible_grading
    (ℬ : ℤ → Submodule k A) [GradedAlgebra ℬ]
    (hcomm : ∀ (i j : ℤ) (x : A),
      proj 𝒜 i (proj ℬ j x) = proj ℬ j (proj 𝒜 i x))
    (D : Derivation k A A) (m : ℤ)
    (hD : ∀ (j : ℤ) (x : A), x ∈ ℬ j → D x ∈ ℬ j)
    {j : ℤ} {x : A} (hx : x ∈ ℬ j) : component 𝒜 D m x ∈ ℬ j := by
  apply componentLinear_preserves 𝒜 D.toLinearMap m (ℬ j)
  · intro i x hx
    exact projection_preserves_of_commute 𝒜 ℬ hcomm hx
  · exact hD j
  · exact hx

end LeadingComponent
end StableCoordinate

end

end OAI
