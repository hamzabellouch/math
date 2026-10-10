import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Model.ProductCocycle

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.ProductModel

private theorem measurable_cocycle (θ c : ℕ → ℝ) (n : ℕ) :
    Measurable (ProductCocycle.cocycleVersion θ c n) := by
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Base => ProductCocycle.representative (x i)) :=
    (measurable_subtype_coe.comp
      (AddCircle.measurableEquivIco (T := (1 : ℝ)) 0).measurable).comp
        (measurable_pi_apply i)
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((hrep.add_const ((n : ℝ) * θ i)).floor))

private theorem cocycle_norm_le_one (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (n : ℕ) (x : Base) :
    ‖(ProductCocycle.cocycleVersion θ c n x : ℂ)‖ ≤ 1 := by
  unfold ProductCocycle.cocycleVersion
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  have hrep : 0 ≤ ProductCocycle.representative (x i) := by
    exact (AddCircle.equivIco (1 : ℝ) 0 (x i)).property.1
  have hf : (0 : ℤ) ≤ ⌊ProductCocycle.representative (x i) + (n : ℝ) * θ i⌋ :=
    Int.floor_nonneg.mpr (add_nonneg hrep (mul_nonneg (Nat.cast_nonneg n) (hθ0 i)))
  exact_mod_cast hf

def positiveCocycleMultiplier (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (n : ℕ) : Hilbert →L[ℂ] Hilbert :=
  multiplier θ (fun x => (ProductCocycle.cocycleVersion θ c n x : ℂ)) 1
    (by norm_num) (measurable_cocycle θ c n).complex_ofReal
    (cocycle_norm_le_one θ c hθ0 hc n)

end Invariant233.ProductModel

end

end OAI
