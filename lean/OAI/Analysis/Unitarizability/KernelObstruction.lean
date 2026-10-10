import OAI.Analysis.Unitarizability.KernelEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq K := Classical.decEq K

abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K
abbrev Space (G K : Type*) [Fintype K] := lp (fun _ : G => Fibre K) 2
abbrev Op (G K : Type*) [Fintype K] := Space G K →L[ℂ] Space G K

def inclusion (x : G) : Fibre K →L[ℂ] Space G K :=
  lp.singleContinuousLinearMap ℂ (fun _ : G => Fibre K) 2 x

def evaluation (x : G) : Space G K →L[ℂ] Fibre K :=
  lp.evalCLM ℂ (fun _ : G => Fibre K) 2 x

@[simp] theorem inclusion_apply (x : G) (v : Fibre K) :
    inclusion x v = lp.single 2 x v := rfl
@[simp] theorem evaluation_apply (x : G) (ξ : Space G K) :
    evaluation x ξ = ξ x := rfl

@[simp] theorem inclusion_norm (x : G) (v : Fibre K) : ‖inclusion x v‖ = ‖v‖ :=
  lp.norm_single (p := 2) (E := fun _ : G => Fibre K) (by norm_num) x v

theorem inclusion_opNorm_le (x : G) : ‖inclusion (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem evaluation_opNorm_le (x : G) : ‖evaluation (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ξ x

@[simp] theorem inclusion_adjoint (x : G) :
    (inclusion (K := K) x).adjoint = evaluation x := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 x v) ξ = inner ℂ v (ξ x)
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun _ : G => Fibre K) x v ξ

@[simp] theorem evaluation_inclusion (x : G) :
    (evaluation (K := K) x).comp (inclusion x) = ContinuousLinearMap.id ℂ (Fibre K) := by
  ext v a
  simp

def block (F : Op G K) (x y : G) : Fibre K →L[ℂ] Fibre K :=
  (evaluation x).comp (F.comp (inclusion y))

def row (F : Op G K) (x : G) : Space G K →L[ℂ] Fibre K :=
  (evaluation x).comp F

def col (F : Op G K) (y : G) : Fibre K →L[ℂ] Space G K :=
  F.comp (inclusion y)

def coefficients (B : Fibre K →L[ℂ] Fibre K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun ab => (B (EuclideanSpace.basisFun K ℂ ab.2)) ab.1)

@[simp] theorem coefficients_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B (a,b) = (B (EuclideanSpace.basisFun K ℂ b)) a := rfl

theorem coefficients_norm_sq (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B‖^2 = ∑ b : K, ‖B (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, coefficients_apply]
  exact Finset.sum_comm

theorem space_norm_sq (ξ : Space G K) : ‖ξ‖^2 = ∑' x, ‖ξ x‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem space_summable (ξ : Space G K) : Summable (fun x => ‖ξ x‖^2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem column_summable (L : Fibre K →L[ℂ] Space G K) :
    Summable (fun x => ‖coefficients ((evaluation x).comp L)‖^2) := by
  simp_rw [coefficients_norm_sq]
  exact summable_sum (fun b _ => space_summable (L (EuclideanSpace.basisFun K ℂ b)))

theorem column_energy (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 =
      ∑ b : K, ‖L (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp_rw [coefficients_norm_sq]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro b hb
    exact (space_norm_sq _).symm
  · intro b hb
    exact space_summable _

theorem column_energy_le (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 ≤
      (Fintype.card K : ℝ) * ‖L‖^2 := by
  rw [column_energy]
  calc
    _ ≤ ∑ b : K, ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have h := L.le_opNorm (EuclideanSpace.basisFun K ℂ b)
      simp only [(EuclideanSpace.basisFun K ℂ).norm_eq_one, mul_one] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by simp [nsmul_eq_mul]


theorem coefficients_adjoint_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B.adjoint (a,b) = conj (coefficients B (b,a)) := by
  simp only [coefficients_apply]
  rw [← EuclideanSpace.basisFun_inner, ← EuclideanSpace.basisFun_inner]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem coefficients_adjoint_norm (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B.adjoint‖ = ‖coefficients B‖ := by
  have h : ‖coefficients B.adjoint‖^2 = ‖coefficients B‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      coefficients_adjoint_apply, RCLike.norm_conj]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (coefficients B.adjoint), norm_nonneg (coefficients B)]

theorem row_block_norm (R : Space G K →L[ℂ] Fibre K) (x : G) :
    ‖coefficients (R.comp (inclusion x))‖ =
      ‖coefficients ((evaluation x).comp R.adjoint)‖ := by
  rw [← coefficients_adjoint_norm (R.comp (inclusion x)),
    ContinuousLinearMap.adjoint_comp, inclusion_adjoint]

theorem row_summable (R : Space G K →L[ℂ] Fibre K) :
    Summable (fun x => ‖coefficients (R.comp (inclusion x))‖^2) := by
  simp_rw [row_block_norm]
  exact column_summable R.adjoint

theorem row_energy_le (R : Space G K →L[ℂ] Fibre K) :
    ∑' x, ‖coefficients (R.comp (inclusion x))‖^2 ≤
      (Fintype.card K : ℝ) * ‖R‖^2 := by
  simp_rw [row_block_norm]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using column_energy_le R.adjoint

variable [Group G]

def reindex (e : G ≃ G) (ξ : Space G K) : Space G K :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

omit [Group G] in
theorem reindex_norm (e : G ≃ G) (ξ : Space G K) : ‖reindex e ξ‖ = ‖ξ‖ := by
  have h : ‖reindex e ξ‖^2 = ‖ξ‖^2 := by
    rw [space_norm_sq, space_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖^2)
  nlinarith [norm_nonneg (reindex e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : Space G K →ₗᵢ[ℂ] Space G K where
  toFun := reindex e
  map_add' ξ η := by ext x a; rfl
  map_smul' z ξ := by ext x a; rfl
  norm_map' := reindex_norm e

/-- The fibre-valued left regular representation. -/
def translation : G →* Op G K where
  toFun g := (reindexIsometry (K := K) (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x a; simp [reindexIsometry, reindex]
  map_mul' g h := by ext ξ x a; simp [reindexIsometry, reindex]

@[simp] theorem translation_apply (g : G) (ξ : Space G K) (x : G) :
    translation g ξ x = ξ (g⁻¹ * x) := rfl

@[simp] theorem translation_inclusion (g y : G) (v : Fibre K) :
    translation g (inclusion y v) = inclusion (g*y) v := by
  ext x a
  simp only [translation_apply, inclusion_apply, lp.single_apply]
  by_cases h : x = g*y
  · subst x
    simp
  · have h' : g⁻¹*x ≠ y := by intro he; apply h; rw [← he]; simp
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

def Commutant : Set (Op G K) := {F | ∀ g, Commute F (translation g)}

theorem block_invariant {F : Op G K} (hF : F ∈ Commutant) (g x y : G) :
    block F (g*x) (g*y) = block F x y := by
  ext v a
  have h := congrArg (fun B : Op G K => B (inclusion y v) (g*x)) (hF g).eq
  simp only [mul_apply_eq_comp, translation_inclusion, translation_apply,
    inv_mul_cancel_left] at h
  exact congrArg (fun v : Fibre K => v a) h

theorem block_kernel {F : Op G K} (hF : F ∈ Commutant) (x y : G) :
    block F x y = block F 1 (x⁻¹*y) := by
  simpa only [mul_one, mul_inv_cancel_left] using block_invariant hF x 1 (x⁻¹*y)



omit [Group G] in
@[simp] theorem block_sub (A C : Op G K) (x y : G) :
    block (A-C) x y = block A x y - block C x y := by
  ext v a
  rfl

@[simp] theorem coefficients_sub (A C : Fibre K →L[ℂ] Fibre K) :
    coefficients (A-C) = coefficients A - coefficients C := by ext ab; rfl

theorem commutant_sub {A C : Op G K} (hA : A ∈ Commutant) (hC : C ∈ Commutant) :
    A-C ∈ Commutant := by
  intro g
  change (A-C) * translation g = translation g * (A-C)
  simp only [sub_mul, mul_sub, (hA g).eq, (hC g).eq]

def energy (A : Op G K) : ℝ := ∑' s, ‖coefficients (block A 1 s)‖^2

theorem energy_summable (A : Op G K) :
    Summable (fun s => ‖coefficients (block A 1 s)‖^2) :=
  row_summable (row A 1)

theorem energy_nonneg (A : Op G K) : 0 ≤ energy A := tsum_nonneg (fun _ => sq_nonneg _)

theorem energy_le_row (A : Op G K) :
    energy A ≤ (Fintype.card K : ℝ) * ‖row A 1‖^2 :=
  row_energy_le (row A 1)

theorem energy_eq_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A = ∑' x, ‖coefficients ((evaluation x).comp (col A 1))‖^2 := by
  change (∑' s, ‖coefficients (block A 1 s)‖^2) = ∑' x, ‖coefficients (block A x 1)‖^2
  simp_rw [block_kernel hA _ 1, mul_one]
  exact ((Equiv.inv G).tsum_eq (fun s => ‖coefficients (block A 1 s)‖^2)).symm

theorem energy_le_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A ≤ (Fintype.card K : ℝ) * ‖col A 1‖^2 := by
  rw [energy_eq_column hA]
  exact column_energy_le _

omit [Group G] in
theorem row_norm_le (F : Op G K) (x : G) : ‖row F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (evaluation_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem col_norm_le (F : Op G K) (x : G) : ‖col F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (inclusion_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem row_difference_bound (T C : Op G K) (x : G) :
    ‖row C x‖ ≤ ‖row T x‖ + ‖T-C‖ := by
  have h : row C x = row T x - row (T-C) x := by ext v a; simp [row]
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) (row_norm_le _ _))

omit [Group G] in
theorem col_difference_bound (A T C : Op G K) (x : G) :
    ‖col (A-C) x‖ ≤ ‖col (A-T) x‖ + ‖T-C‖ := by
  have h : col (A-C) x = col (A-T) x + col (T-C) x := by
    ext v y a
    simp [col]
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (le_refl _) (col_norm_le _ _))

theorem energy_split_le (A C : Op G K) : energy A ≤ 2 * energy C + 2 * energy (A-C) := by
  have hp (s : G) : ‖coefficients (block A 1 s)‖^2 ≤
      2 * ‖coefficients (block C 1 s)‖^2 + 2 * ‖coefficients (block (A-C) 1 s)‖^2 := by
    rw [block_sub, coefficients_sub]
    have ht := norm_add_le (coefficients (block C 1 s))
      (coefficients (block A 1 s) - coefficients (block C 1 s))
    rw [add_sub_cancel] at ht
    nlinarith [norm_nonneg (coefficients (block A 1 s)),
      norm_nonneg (coefficients (block C 1 s)),
      norm_nonneg (coefficients (block A 1 s) - coefficients (block C 1 s)),
      sq_nonneg (‖coefficients (block C 1 s)‖ -
        ‖coefficients (block A 1 s) - coefficients (block C 1 s)‖)]
  have hs := ((energy_summable C).mul_left 2).add ((energy_summable (A-C)).mul_left 2)
  have h := (energy_summable A).tsum_le_tsum hp hs
  rw [((energy_summable C).mul_left 2).tsum_add ((energy_summable (A-C)).mul_left 2),
    tsum_mul_left, tsum_mul_left] at h
  exact h

/-- The kernel-energy obstruction, proved from coordinate estimates and commutation. -/
theorem kernel_obstruction {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (_hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ)
    {C : Op G K} (hC : C ∈ Commutant) :
    energy A ≤ 4 * (Fintype.card K : ℝ) * (κ + ‖T-C‖)^2 := by
  have hR : ‖row C 1‖ ≤ κ + ‖T-C‖ :=
    (row_difference_bound T C 1).trans (add_le_add hr (le_refl _))
  have hL : ‖col (A-C) 1‖ ≤ κ + ‖T-C‖ :=
    (col_difference_bound A T C 1).trans (add_le_add hc (le_refl _))
  have heC := (energy_le_row C).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hR 2) (Nat.cast_nonneg (Fintype.card K)))
  have heAC := (energy_le_column (commutant_sub hA hC)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hL 2) (Nat.cast_nonneg (Fintype.card K)))
  nlinarith [energy_split_le A C]

/-- Pointwise distance inequality for positive fibre dimension. -/
theorem kernel_distance_pointwise [Nonempty K] {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ)
    {C : Op G K} (hC : C ∈ Commutant) :
    (1/2 : ℝ) * Real.sqrt (energy A / Fintype.card K) - κ ≤ ‖T-C‖ := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have he := kernel_obstruction hA hκ hr hc hC
  have hdiv : energy A / Fintype.card K ≤ 4 * (κ + ‖T-C‖)^2 := by
    apply (div_le_iff₀ hk).mpr
    nlinarith [he]
  have hs := Real.sq_sqrt (div_nonneg (energy_nonneg A) hk.le)
  have hh : 0 ≤ κ + ‖T-C‖ := add_nonneg hκ (norm_nonneg _)
  have hsqrt : Real.sqrt (energy A / Fintype.card K) ≤ 2 * (κ + ‖T-C‖) := by
    nlinarith [Real.sqrt_nonneg (energy A / Fintype.card K)]
  linarith

/-- The distance obstruction for the metric distance to
all bounded translation-commuting operators. -/
theorem kernel_distance [Nonempty K] {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ) :
    (1/2 : ℝ) * Real.sqrt (energy A / Fintype.card K) - κ ≤ Metric.infDist T Commutant := by
  apply (Metric.le_infDist (s := Commutant) ⟨0, fun g => Commute.zero_left _⟩).mpr
  intro C hC
  simpa only [dist_eq_norm] using kernel_distance_pointwise hA hκ hr hc hC


end KernelObstruction
end Dixmier

end

end OAI
