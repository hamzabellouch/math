import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

section

namespace PerfectCompleteness.DummyElimination

noncomputable section

variable {𝕜 C D V : Type*} [Field 𝕜]
  [AddCommGroup C] [Module 𝕜 C] [AddCommGroup D] [Module 𝕜 D]
  [AddCommGroup V] [Module 𝕜 V]

theorem exists_factor (d : C →ₗ[𝕜] D) (f : C →ₗ[𝕜] V)
    (h : LinearMap.ker d ≤ LinearMap.ker f) :
    ∃ g : D →ₗ[𝕜] V, g.comp d = f := by
  let f₀ : LinearMap.range d →ₗ[𝕜] V :=
    ((LinearMap.ker d).liftQ f h).comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := f₀.exists_extend
  refine ⟨g, ?_⟩
  ext c
  have hc := LinearMap.congr_fun hg (⟨d c, LinearMap.mem_range_self d c⟩ : LinearMap.range d)
  change g (d c) = (LinearMap.ker d).liftQ f h
    (d.quotKerEquivRange.symm ⟨d c, LinearMap.mem_range_self d c⟩) at hc
  rw [d.quotKerEquivRange_symm_apply_image] at hc
  exact hc

structure Slice (𝕜 H D K R C : Type*) [Field 𝕜]
    [AddCommGroup H] [Module 𝕜 H] [AddCommGroup D] [Module 𝕜 D]
    [AddCommGroup K] [Module 𝕜 K] [AddCommGroup R] [Module 𝕜 R]
    [AddCommGroup C] [Module 𝕜 C] where
  rowMap : K →ₗ[𝕜] R
  realTarget : H →ₗ[𝕜] R
  dummyTarget : D →ₗ[𝕜] R
  realColumns : C →ₗ[𝕜] H
  dummyColumns : C →ₗ[𝕜] D
  columnTarget : C →ₗ[𝕜] K

namespace Slice

variable {H K R : Type*}
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]
  [AddCommGroup R] [Module 𝕜 R]
  (S : Slice 𝕜 H D K R C)

def IsLift (X : H →ₗ[𝕜] K) (Y : D →ₗ[𝕜] K) : Prop :=
  S.rowMap.comp X = S.realTarget ∧
  S.rowMap.comp Y = S.dummyTarget ∧
  X.comp S.realColumns + Y.comp S.dummyColumns = S.columnTarget

def Projected (X : H →ₗ[𝕜] K) : Prop :=
  S.rowMap.comp X = S.realTarget ∧
  ∀ c, S.dummyColumns c = 0 → X (S.realColumns c) = S.columnTarget c

def Homogeneous (Z : D →ₗ[𝕜] K) : Prop :=
  S.rowMap.comp Z = 0 ∧ Z.comp S.dummyColumns = 0

theorem IsLift.projected {X : H →ₗ[𝕜] K} {Y : D →ₗ[𝕜] K}
    (h : S.IsLift X Y) : S.Projected X := by
  refine ⟨h.1, ?_⟩
  intro c hc
  have he := LinearMap.congr_fun h.2.2 c
  simpa [hc] using he

theorem exists_lift_iff (hne : ∃ X Y, S.IsLift X Y) (X : H →ₗ[𝕜] K) :
    (∃ Y, S.IsLift X Y) ↔ S.Projected X := by
  constructor
  · rintro ⟨Y, hY⟩
    exact IsLift.projected S hY
  · intro hX
    obtain ⟨X₀, Y₀, h₀⟩ := hne
    have hX₀ := IsLift.projected S h₀
    let f : C →ₗ[𝕜] LinearMap.ker S.rowMap :=
      LinearMap.codRestrict (LinearMap.ker S.rowMap) ((X₀ - X).comp S.realColumns)
        (by
          intro c
          change S.rowMap (X₀ (S.realColumns c) - X (S.realColumns c)) = 0
          rw [map_sub]
          have h₁ := LinearMap.congr_fun h₀.1 (S.realColumns c)
          have h₂ := LinearMap.congr_fun hX.1 (S.realColumns c)
          change S.rowMap (X₀ (S.realColumns c)) = S.realTarget (S.realColumns c) at h₁
          change S.rowMap (X (S.realColumns c)) = S.realTarget (S.realColumns c) at h₂
          rw [h₁, h₂, sub_self])
    have hf : LinearMap.ker S.dummyColumns ≤ LinearMap.ker f := by
      intro c hc
      apply Subtype.ext
      change X₀ (S.realColumns c) - X (S.realColumns c) = 0
      rw [hX₀.2 c hc, hX.2 c hc, sub_self]
    obtain ⟨L, hL⟩ := exists_factor S.dummyColumns f hf
    let Z : D →ₗ[𝕜] K := (LinearMap.ker S.rowMap).subtype.comp L
    have hZrow : S.rowMap.comp Z = 0 := by
      ext d
      exact (L d).property
    have hZcolumn (c : C) :
        Z (S.dummyColumns c) = X₀ (S.realColumns c) - X (S.realColumns c) := by
      have hc := congrArg Subtype.val (LinearMap.congr_fun hL c)
      exact hc
    refine ⟨Y₀ + Z, hX.1, ?_, ?_⟩
    · ext d
      change S.rowMap (Y₀ d + Z d) = S.dummyTarget d
      rw [map_add]
      have h₁ := LinearMap.congr_fun h₀.2.1 d
      have h₂ := LinearMap.congr_fun hZrow d
      change S.rowMap (Y₀ d) = S.dummyTarget d at h₁
      change S.rowMap (Z d) = 0 at h₂
      rw [h₁, h₂, add_zero]
    · ext c
      change X (S.realColumns c) + (Y₀ (S.dummyColumns c) + Z (S.dummyColumns c)) =
        S.columnTarget c
      rw [hZcolumn]
      have hc := LinearMap.congr_fun h₀.2.2 c
      change X₀ (S.realColumns c) + Y₀ (S.dummyColumns c) = S.columnTarget c at hc
      calc
        _ = X₀ (S.realColumns c) + Y₀ (S.dummyColumns c) := by abel
        _ = S.columnTarget c := hc

def fiberEquivHomogeneous {X : H →ₗ[𝕜] K} {Y₀ : D →ₗ[𝕜] K}
    (h₀ : S.IsLift X Y₀) :
    {Y : D →ₗ[𝕜] K // S.IsLift X Y} ≃
      {Z : D →ₗ[𝕜] K // S.Homogeneous Z} where
  toFun Y := ⟨Y.val - Y₀, by
    constructor
    · ext d
      change S.rowMap (Y.val d - Y₀ d) = 0
      rw [map_sub]
      have h₁ := LinearMap.congr_fun Y.property.2.1 d
      have h₂ := LinearMap.congr_fun h₀.2.1 d
      change S.rowMap (Y.val d) = S.dummyTarget d at h₁
      change S.rowMap (Y₀ d) = S.dummyTarget d at h₂
      rw [h₁, h₂, sub_self]
    · ext c
      change Y.val (S.dummyColumns c) - Y₀ (S.dummyColumns c) = 0
      have h₁ := LinearMap.congr_fun Y.property.2.2 c
      have h₂ := LinearMap.congr_fun h₀.2.2 c
      change X (S.realColumns c) + Y.val (S.dummyColumns c) = S.columnTarget c at h₁
      change X (S.realColumns c) + Y₀ (S.dummyColumns c) = S.columnTarget c at h₂
      exact sub_eq_zero.mpr (add_left_cancel (h₁.trans h₂.symm))⟩
  invFun Z := ⟨Y₀ + Z.val, h₀.1, by
    ext d
    change S.rowMap (Y₀ d + Z.val d) = S.dummyTarget d
    rw [map_add]
    have h₁ := LinearMap.congr_fun h₀.2.1 d
    have h₂ := LinearMap.congr_fun Z.property.1 d
    change S.rowMap (Y₀ d) = S.dummyTarget d at h₁
    change S.rowMap (Z.val d) = 0 at h₂
    rw [h₁, h₂, add_zero], by
    ext c
    change X (S.realColumns c) + (Y₀ (S.dummyColumns c) + Z.val (S.dummyColumns c)) =
      S.columnTarget c
    have h₁ := LinearMap.congr_fun h₀.2.2 c
    have h₂ := LinearMap.congr_fun Z.property.2 c
    change Z.val (S.dummyColumns c) = 0 at h₂
    rw [h₂, add_zero]
    exact h₁⟩
  left_inv Y := by
    apply Subtype.ext
    change Y₀ + (Y.val - Y₀) = Y.val
    abel
  right_inv Z := by
    apply Subtype.ext
    exact add_sub_cancel_left Y₀ Z.val

theorem fiber_card_eq {X : H →ₗ[𝕜] K} {Y₀ : D →ₗ[𝕜] K}
    (h₀ : S.IsLift X Y₀) :
    Nat.card {Y : D →ₗ[𝕜] K // S.IsLift X Y} =
      Nat.card {Z : D →ₗ[𝕜] K // S.Homogeneous Z} :=
  Nat.card_congr (S.fiberEquivHomogeneous h₀)

theorem projected_fibers_card_eq (hne : ∃ X Y, S.IsLift X Y)
    {X X' : H →ₗ[𝕜] K} (hX : S.Projected X) (hX' : S.Projected X') :
    Nat.card {Y : D →ₗ[𝕜] K // S.IsLift X Y} =
      Nat.card {Y : D →ₗ[𝕜] K // S.IsLift X' Y} := by
  obtain ⟨Y, hY⟩ := (S.exists_lift_iff hne X).mpr hX
  obtain ⟨Y', hY'⟩ := (S.exists_lift_iff hne X').mpr hX'
  exact (S.fiber_card_eq hY).trans (S.fiber_card_eq hY').symm

theorem projected_iff_basis {ι : Type*} (b : Module.Basis ι 𝕜 (LinearMap.ker S.dummyColumns))
    (X : H →ₗ[𝕜] K) :
    S.Projected X ↔ S.rowMap.comp X = S.realTarget ∧
      ∀ i, X (S.realColumns (b i)) = S.columnTarget (b i) := by
  constructor
  · intro h
    exact ⟨h.1, fun i => h.2 (b i) (b i).property⟩
  · rintro ⟨hrow, hcol⟩
    refine ⟨hrow, ?_⟩
    have he : (X.comp S.realColumns).domRestrict (LinearMap.ker S.dummyColumns) =
        S.columnTarget.domRestrict (LinearMap.ker S.dummyColumns) := b.ext hcol
    intro c hc
    exact LinearMap.congr_fun he ⟨c, hc⟩

theorem projected_equation_count_le [FiniteDimensional 𝕜 C] :
    Module.finrank 𝕜 (LinearMap.ker S.dummyColumns) ≤ Module.finrank 𝕜 C :=
  Submodule.finrank_le _

end Slice
end
end PerfectCompleteness.DummyElimination

end

section

namespace PerfectCompleteness.ExactRationalMultiplicity

open scoped BigOperators

noncomputable section

variable {S : Type*} {E : S → Type*} [Fintype S] [∀ s, Fintype (E s)]

def commonDenominator (w : ∀ s, E s → ℚ) : Nat :=
  ∏ x : Sigma E, (w x.1 x.2).den

def multiplicity (w : ∀ s, E s → ℚ) (s : S) (e : E s) : Nat :=
  (w s e).num.natAbs * (commonDenominator w / (w s e).den)

theorem commonDenominator_pos (w : ∀ s, E s → ℚ) : 0 < commonDenominator w := by
  apply Finset.prod_pos
  intro x _
  exact (w x.1 x.2).den_pos

theorem denominator_dvd (w : ∀ s, E s → ℚ) (s : S) (e : E s) :
    (w s e).den ∣ commonDenominator w :=
  Finset.dvd_prod_of_mem (fun x : Sigma E => (w x.1 x.2).den)
    (Finset.mem_univ (⟨s, e⟩ : Sigma E))

@[simp] theorem commonDenominator_of_isEmpty [IsEmpty S] (w : ∀ s, E s → ℚ) :
    commonDenominator w = 1 := by
  classical
  simp [commonDenominator]

theorem multiplicity_cast (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (s : S) (e : E s) :
    (multiplicity w s e : ℚ) = (commonDenominator w : ℚ) * w s e := by
  have habs : ((w s e).num.natAbs : ℚ) = ((w s e).num : ℚ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℚ))
        (Int.natAbs_of_nonneg (Rat.num_pos.mpr (positive s e)).le)
  rw [multiplicity, Nat.cast_mul, Nat.cast_div_charZero (denominator_dvd w s e), habs]
  calc
    ((w s e).num : ℚ) * ((commonDenominator w : ℚ) / (w s e).den) =
        (commonDenominator w : ℚ) * (((w s e).num : ℚ) / (w s e).den) := by ring
    _ = (commonDenominator w : ℚ) * w s e := by rw [Rat.num_div_den]

theorem multiplicity_pos (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (s : S) (e : E s) : 0 < multiplicity w s e := by
  have h : (0 : ℚ) < (multiplicity w s e : ℚ) := by
    rw [multiplicity_cast w positive]
    exact mul_pos (Nat.cast_pos.mpr (commonDenominator_pos w)) (positive s e)
  exact_mod_cast h

theorem multiplicity_sum (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) (s : S) :
    ∑ e, multiplicity w s e = commonDenominator w := by
  have h : ((∑ e, multiplicity w s e : Nat) : ℚ) = (commonDenominator w : ℚ) := by
    rw [Nat.cast_sum]
    simp_rw [multiplicity_cast w positive]
    rw [← Finset.mul_sum, normalized s, mul_one]
  exact_mod_cast h

theorem multiplicity_div (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (s : S) (e : E s) :
    (multiplicity w s e : ℚ) / (commonDenominator w : ℚ) = w s e := by
  have hD : (commonDenominator w : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (commonDenominator_pos w))
  apply (div_eq_iff hD).mpr
  rw [multiplicity_cast w positive, mul_comm]

theorem multiplicity_le_denominator (w : ∀ s, E s → ℚ)
    (positive : ∀ s e, 0 < w s e) (normalized : ∀ s, ∑ e, w s e = 1)
    (s : S) (e : E s) : multiplicity w s e ≤ commonDenominator w := by
  calc
    multiplicity w s e ≤ ∑ e', multiplicity w s e' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    _ = commonDenominator w := multiplicity_sum w positive normalized s

structure Uniformization (w : ∀ s, E s → ℚ) where
  denominator : Nat
  denominator_pos : 0 < denominator
  count : ∀ s, E s → Nat
  count_pos : ∀ s e, 0 < count s e
  count_total : ∀ s, ∑ e, count s e = denominator
  fraction : ∀ s e, (count s e : ℚ) / (denominator : ℚ) = w s e

def build (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) : Uniformization w where
  denominator := commonDenominator w
  denominator_pos := commonDenominator_pos w
  count := multiplicity w
  count_pos := multiplicity_pos w positive
  count_total := multiplicity_sum w positive normalized
  fraction := multiplicity_div w positive

@[simp] theorem build_denominator (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) :
    (build w positive normalized).denominator = commonDenominator w := rfl

@[simp] theorem build_count (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) (s : S) (e : E s) :
    (build w positive normalized).count s e = multiplicity w s e := rfl

end

end PerfectCompleteness.ExactRationalMultiplicity

end

section

namespace PerfectCompleteness.ExactSeedMultiplicity

open scoped BigOperators

def factor (M : Nat) : Nat := M.factorial

def denominator (D M : Nat) : Nat := D * factor M

def perSeed (M count copies : Nat) : Nat := copies * (factor M / count)

theorem factor_positive (M : Nat) : 0 < factor M := Nat.factorial_pos M

theorem denominator_positive {D : Nat} (hD : 0 < D) (M : Nat) :
    0 < denominator D M := Nat.mul_pos hD (factor_positive M)

theorem count_dvd_factor {M count : Nat} (positive : 0 < count) (bounded : count ≤ M) :
    count ∣ factor M := Nat.dvd_factorial positive bounded

theorem seed_total {M count : Nat} (positive : 0 < count) (bounded : count ≤ M)
    (copies : Nat) : count * perSeed M count copies = copies * factor M := by
  unfold perSeed
  calc
    count * (copies * (factor M / count)) = copies * (count * (factor M / count)) := by ring
    _ = copies * factor M := by rw [Nat.mul_div_cancel' (count_dvd_factor positive bounded)]

theorem perSeed_positive {M count copies : Nat}
    (positive : 0 < count) (bounded : count ≤ M) (hcopies : 0 < copies) :
    0 < perSeed M count copies :=
  Nat.mul_pos hcopies (Nat.div_pos
    (Nat.le_of_dvd (factor_positive M) (count_dvd_factor positive bounded)) positive)

theorem perSeed_cast {M count : Nat} (positive : 0 < count) (bounded : count ≤ M)
    (copies : Nat) :
    (perSeed M count copies : ℚ) = (copies : ℚ) * factor M / count := by
  have hn : (count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  apply (eq_div_iff hn).mpr
  have h := seed_total positive bounded copies
  have hc : (count : ℚ) * (perSeed M count copies : ℚ) =
      (copies : ℚ) * (factor M : ℚ) := by exact_mod_cast h
  simpa only [mul_comm] using hc

theorem perSeed_ratio {D M count : Nat} (hD : 0 < D)
    (positive : 0 < count) (bounded : count ≤ M) (copies : Nat) :
    (perSeed M count copies : ℚ) / denominator D M = ((copies : ℚ) / D) / count := by
  rw [perSeed_cast positive bounded copies]
  have hDc : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hnc : (count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  have hfactor : (factor M : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (factor_positive M))
  simp only [denominator, Nat.cast_mul]
  field_simp [hDc, hnc, hfactor]

abbrev Seeded {E : Type*} (count : E → Nat) := Σ e : E, Fin (count e)

section Family

variable {E : Type*} [Fintype E] {D M : Nat}
    (copies count : E → Nat) (positive : ∀ e, 0 < count e) (bounded : ∀ e, count e ≤ M)

def multiplicity (outcome : Seeded count) : Nat :=
  perSeed M (count outcome.1) (copies outcome.1)

include positive bounded

omit [Fintype E] in
theorem multiplicity_positive (hcopies : ∀ e, 0 < copies e) (outcome : Seeded count) :
    0 < multiplicity (M := M) copies count outcome :=
  perSeed_positive (positive outcome.1) (bounded outcome.1) (hcopies outcome.1)

theorem sum_multiplicity (total : ∑ e, copies e = D) :
    (∑ outcome : Seeded count, multiplicity (M := M) copies count outcome) = denominator D M := by
  rw [Fintype.sum_sigma]
  simp only [multiplicity, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = ∑ e, copies e * factor M := by
      apply Finset.sum_congr rfl
      intro e _
      exact seed_total (positive e) (bounded e) (copies e)
    _ = denominator D M := by
      rw [← Finset.sum_mul, total]
      rfl

omit [Fintype E] in
theorem multiplicity_ratio (hD : 0 < D) (outcome : Seeded count) :
    (multiplicity (M := M) copies count outcome : ℚ) / denominator D M =
      ((copies outcome.1 : ℚ) / D) / count outcome.1 :=
  perSeed_ratio hD (positive outcome.1) (bounded outcome.1) (copies outcome.1)

omit [Fintype E] in
theorem multiplicity_ratio_of_base (hD : 0 < D) (weights : E → ℚ)
    (represented : ∀ e, (copies e : ℚ) / D = weights e) (outcome : Seeded count) :
    (multiplicity (M := M) copies count outcome : ℚ) / denominator D M =
      weights outcome.1 / count outcome.1 := by
  rw [multiplicity_ratio copies count positive bounded hD, represented]

end Family
end PerfectCompleteness.ExactSeedMultiplicity

end

section

namespace PerfectCompleteness.NonzeroAverage

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem card_subtype_ne_real (a : A) :
    (Fintype.card {x : A // x ≠ a} : ℝ) = (Fintype.card A : ℝ) - 1 := by
  have h : (Fintype.card A : ℝ) =
      1 + (Fintype.card {x : A // x ≠ a} : ℝ) := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) a
  linarith

theorem card_mul_expect_eq (g : A → ℝ) (a : A) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g a + (Fintype.card {x : A // x ≠ a} : ℝ) *
        (𝔼 x : {x : A // x ≠ a}, g x.1) := by
  rw [Fintype.card_mul_expect, Fintype.card_mul_expect]
  exact Fintype.sum_eq_add_sum_subtype_ne g a

theorem card_mul_expect_eq_sub_one (g : A → ℝ) (a : A) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g a + ((Fintype.card A : ℝ) - 1) *
        (𝔼 x : {x : A // x ≠ a}, g x.1) := by
  rw [← card_subtype_ne_real a]
  exact card_mul_expect_eq g a

theorem expect_subtype_ne_le_expect_of_expect_le (g : A → ℝ) (a : A)
    (h : (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ g a) :
    (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ (𝔼 x, g x) := by
  let : Nonempty A := ⟨a⟩
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hcard).mp
  have hid := card_mul_expect_eq_sub_one g a
  nlinarith

theorem expect_subtype_ne_le_expect [Nontrivial A] (g : A → ℝ) (a : A)
    (h : ∀ x, g x ≤ g a) :
    (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ (𝔼 x, g x) := by
  obtain ⟨b, hb⟩ := exists_ne a
  let : Nonempty {x : A // x ≠ a} := ⟨⟨b, hb⟩⟩
  apply expect_subtype_ne_le_expect_of_expect_le g a
  exact Finset.expect_le Finset.univ_nonempty (fun x _ => h x.1)

theorem zero_card_mul_expect [Zero A] (g : A → ℝ) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g 0 + ((Fintype.card A : ℝ) - 1) *
        (𝔼 x : {x : A // x ≠ (0 : A)}, g x.1) :=
  card_mul_expect_eq_sub_one g 0

theorem nonzero_expect_le_expect [Zero A] [Nontrivial A] (g : A → ℝ)
    (h : ∀ x, g x ≤ g 0) :
    (𝔼 x : {x : A // x ≠ (0 : A)}, g x.1) ≤ (𝔼 x, g x) :=
  expect_subtype_ne_le_expect g 0 h

end PerfectCompleteness.NonzeroAverage

end

end OAI
