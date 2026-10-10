import OAI.Analysis.KadisonKastler.FiniteRowAverages
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! Convex combinations of row averages are again single row averages. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def convexRow (t : ℝ) (r : ι → A) (s : κ → A) : ι ⊕ κ → A :=
  Sum.elim (fun i => Real.sqrt t • r i) (fun j => Real.sqrt (1 - t) • s j)

theorem convexRow_normalized (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (r : ι → A) (s : κ → A)
    (hr : ∑ i, r i * star (r i) = 1) (hs : ∑ j, s j * star (s j) = 1) :
    ∑ k, convexRow t r s k * star (convexRow t r s k) = 1 := by
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hst : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
    Real.mul_self_sqrt (sub_nonneg.mpr ht1)
  simp only [Fintype.sum_sum_type, convexRow, Sum.elim_inl, Sum.elim_inr,
    star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, htt, hst,
    ← Finset.smul_sum, hr, hs]
  rw [← add_smul]
  simp

theorem finiteRightAverage_convexRow (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (r : ι → A) (s : κ → A) (F : A →ₗ[ℂ] A) :
    finiteRightAverage (convexRow t r s) F =
      t • finiteRightAverage r F + (1 - t) • finiteRightAverage s F := by
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hst : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
    Real.mul_self_sqrt (sub_nonneg.mpr ht1)
  apply LinearMap.ext
  intro x
  simp only [finiteRightAverage_apply, Fintype.sum_sum_type, convexRow,
    Sum.elim_inl, Sum.elim_inr, star_smul, star_trivial, mul_smul_comm,
    LinearMap.map_smul_of_tower, smul_mul_assoc, smul_smul, htt, hst, ← Finset.smul_sum,
    LinearMap.add_apply, LinearMap.smul_apply]

end

end KadisonKastler

end OAI
