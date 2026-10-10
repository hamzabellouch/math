import OAI.Analysis.Unitarizability.KernelObstruction
import OAI.Analysis.Unitarizability.HilbertSum
import OAI.Analysis.Unitarizability.FiniteSynthesis

namespace OAI

/-! Bounded masked operators. All labels remain separate, including
repeated values of the product list. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ
abbrev Space (G K : Type*) [Fintype K] : Type _ := KernelObstruction.Space G K
abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K

def shift (s : G) : Space G K →L[ℂ] Space G K :=
  (KernelObstruction.reindexIsometry (K := K) (Equiv.mulRight s)).toContinuousLinearMap

@[simp] theorem shift_apply (s : G) (ξ : Space G K) (x : G) : shift s ξ x = ξ (x*s) := rfl

def term (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (i : I) : Space G K →L[ℂ] Space G K :=
  (HilbertSum.boundedSum (κ := ‖v i‖ * ‖v i‖) (fun x => c x i • InnerProductSpace.rankOne ℂ (v i) (v i))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun x => by
      rw [norm_smul, InnerProductSpace.norm_rankOne]
      exact (mul_le_mul_of_nonneg_right (hc x i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (one_mul _))).comp
    (shift (s i))

def operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) : Space G K →L[ℂ] Space G K := ∑ i, term v s c hc i

omit [Fintype I] in
@[simp] theorem term_apply (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (i : I) (ξ : Space G K) (x : G) :
    term v s c hc i ξ x = (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
  change (c x i) • (InnerProductSpace.rankOne ℂ (v i) (v i) (ξ (x*s i))) = _
  rw [InnerProductSpace.rankOne_apply, smul_smul]

@[simp] theorem operator_apply (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (ξ : Space G K) (x : G) :
    operator v s c hc ξ x = ∑ i, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
  simp only [operator, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, term_apply]

def rowSet (c : G → I → ℂ) (x : G) : Finset I := univ.filter (fun i => c x i ≠ 0)
def columnSet (s : I → G) (c : G → I → ℂ) (y : G) : Finset I :=
  univ.filter (fun i => c (y*(s i)⁻¹) i ≠ 0)

def edgeEnergy (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (x : G) : ℝ :=
  ∑ i, if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0

omit [Fintype I] in
theorem edge_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (i : I) :
    Summable (fun x => if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) := by
  have hs := ((KernelObstruction.space_summable ξ).comp_injective
    (Equiv.mulRight (s i)).injective).mul_left (‖v i‖^2)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro x; split_ifs <;> positivity
  · intro x
    split_ifs
    · change ‖inner ℂ (v i) (ξ (x*s i))‖^2 ≤ ‖v i‖^2 * ‖ξ (x*s i)‖^2
      calc
        _ ≤ (‖v i‖ * ‖ξ (x*s i)‖)^2 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_inner_le_norm (𝕜 := ℂ) (v i) (ξ (x*s i))) 2
        _ = _ := mul_pow _ _ _
    · change 0 ≤ ‖v i‖^2 * ‖ξ (x*s i)‖^2
      positivity

theorem edgeEnergy_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) :
    Summable (edgeEnergy v s c ξ) := summable_sum (fun i _ => edge_summable v s c ξ i)

theorem sum_subfamily {R : Type*} [AddCommMonoid R] (c : I → ℂ) (f : I → R) :
    (∑ i : univ.filter (fun i => c i ≠ 0), f i) = ∑ i, if c i ≠ 0 then f i else 0 := by
  rw [Finset.sum_coe_sort, Finset.sum_filter]

theorem row_estimate (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (ξ : Space G K) (x : G) :
    ‖operator v s c hc ξ x‖^2 ≤ b^2 * edgeEnergy v s c ξ x := by
  let J := rowSet c x
  have hsum : operator v s c hc ξ x =
      ∑ i : J, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
    calc
      _ = ∑ i, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := operator_apply ..
      _ = ∑ i ∈ J, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i hi hn
        have hz : c x i = 0 := by simpa [J, rowSet] using hn
        simp [hz]
      _ = _ := (Finset.sum_coe_sort J (fun i => (c x i * inner ℂ (v i) (ξ (x*s i))) • v i)).symm
  rw [hsum]
  have h := FiniteSynthesis.synthesis_sq_le v J hb (hrow x)
    (fun i => c x i * inner ℂ (v i) (ξ (x*s i)))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
  have he : edgeEnergy v s c ξ x = ∑ i : J, ‖inner ℂ (v i) (ξ (x*s i))‖^2 := by
    exact (sum_subfamily (c x) (fun i => ‖inner ℂ (v i) (ξ (x*s i))‖^2)).symm
  rw [he]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, mul_pow]
  have hm : ‖c x i‖^2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) (hc x i) 2
  exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans_eq (one_mul _)

theorem edgeEnergy_reindex (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) :
    ∑' x, edgeEnergy v s c ξ x =
      ∑' y, ∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2 := by
  let f : G → I → ℝ := fun y i => if c (y*(s i)⁻¹) i ≠ 0 then ‖inner ℂ (v i) (ξ y)‖^2 else 0
  have he (i : I) : (fun y => f y i) =
      (fun y => if c y i ≠ 0 then ‖inner ℂ (v i) (ξ (y*s i))‖^2 else 0) ∘
        (Equiv.mulRight (s i)⁻¹) := by
    funext y
    simp [f, mul_assoc]
  have hs (i : I) : Summable (fun y => f y i) := by
    rw [he]
    exact (edge_summable v s c ξ i).comp_injective (Equiv.mulRight (s i)⁻¹).injective
  change (∑' x, ∑ i, _) = _
  rw [Summable.tsum_finsetSum (fun i _ => edge_summable v s c ξ i)]
  have ht (i : I) : (∑' x, if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) = ∑' y, f y i := by
    rw [he]
    exact ((Equiv.mulRight (s i)⁻¹).tsum_eq _).symm
  simp_rw [ht]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  apply tsum_congr
  intro y
  exact (sum_subfamily (fun i => c (y*(s i)⁻¹) i) (fun i => ‖inner ℂ (v i) (ξ y)‖^2)).symm

/-- Row and column synthesis bounds imply the masked operator bound,
without assuming that the product labels s_i are distinct. -/
theorem masked_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (hcol : ∀ y, ‖FiniteSynthesis.synthesis v (columnSet s c y)‖ ≤ b) :
    ‖operator v s c hc‖ ≤ b^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg b)
  intro ξ
  have hr := (KernelObstruction.space_summable (operator v s c hc ξ)).tsum_le_tsum
    (row_estimate v s c hc hb hrow ξ) ((edgeEnergy_summable v s c ξ).mul_left (b^2))
  rw [tsum_mul_left, ← KernelObstruction.space_norm_sq, edgeEnergy_reindex] at hr
  have hcs : Summable (fun y => ∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2) := by
    have h (y : G) : (∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2) =
        ∑ i : I, if c (y*(s i)⁻¹) i ≠ 0 then ‖inner ℂ (v i) (ξ y)‖^2 else 0 := by
      exact sum_subfamily (fun i => c (y*(s i)⁻¹) i) (fun i => ‖inner ℂ (v i) (ξ y)‖^2)
    simp_rw [h]
    apply summable_sum
    intro i hi
    have hs := (edge_summable v s c ξ i).comp_injective (Equiv.mulRight (s i)⁻¹).injective
    simpa [Function.comp_def, mul_assoc] using hs
  have hcol' := hcs.tsum_le_tsum (fun y => FiniteSynthesis.analysis_sq_le v _ hb (hcol y) (ξ y))
    ((KernelObstruction.space_summable ξ).mul_left (b^2))
  rw [tsum_mul_left, ← KernelObstruction.space_norm_sq] at hcol'
  have hh := hr.trans (mul_le_mul_of_nonneg_left hcol' (sq_nonneg b))
  have hpos : 0 ≤ b^2 * ‖ξ‖ := mul_nonneg (sq_nonneg b) (norm_nonneg ξ)
  nlinarith [norm_nonneg (operator v s c hc ξ)]

end Masked
end Dixmier

end

end OAI
