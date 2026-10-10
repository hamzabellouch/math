import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring

namespace OAI

/-! Positive rank-one kernel energy. Matrices are represented by their entries
with the unnormalized Hilbert–Schmidt (Euclidean coefficient) norm. -/
noncomputable section
namespace Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

def rankOneCoefficients (v : EuclideanSpace ℂ K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun p => v p.1 * conj (v p.2))

omit [Fintype K] in
@[simp] theorem rankOneCoefficients_apply (v : EuclideanSpace ℂ K) (a b : K) :
    rankOneCoefficients v (a, b) = v a * conj (v b) := rfl

theorem rankOne_inner (v w : EuclideanSpace ℂ K) :
    inner ℂ (rankOneCoefficients v) (rankOneCoefficients w) =
      inner ℂ v w * conj (inner ℂ v w) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    rankOneCoefficients, map_sum, map_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [← Complex.star_def, star_mul, star_star]
  ring

theorem rankOne_inner_re (v w : EuclideanSpace ℂ K) :
    (inner ℂ (rankOneCoefficients v) (rankOneCoefficients w)).re = ‖inner ℂ v w‖^2 := by
  rw [rankOne_inner, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_eq_norm_sq _

theorem rankOne_norm_sq (v : EuclideanSpace ℂ K) (hv : ‖v‖ = 1) :
    ‖rankOneCoefficients v‖^2 = 1 := by
  rw [← @inner_self_eq_norm_sq ℂ]
  change (inner ℂ (rankOneCoefficients v) (rankOneCoefficients v)).re = 1
  rw [rankOne_inner_re, inner_self_eq_norm_sq_to_K, hv]
  norm_num

/-- Collision blocks are sums of the rank-one matrices with that label value. -/
def kernelCoefficients (v : I → EuclideanSpace ℂ K) (s : I → G) (g : G) :
    EuclideanSpace ℂ (K × K) :=
  ∑ i ∈ (Finset.univ.filter fun i => s i = g), rankOneCoefficients (v i)

omit [Fintype I] in
/-- Positivity of every pairwise Hilbert–Schmidt inner product makes each
block’s energy at least the number of its unit rank-one summands. -/
theorem rankOne_sum_energy (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (J : Finset I) : (J.card : ℝ) ≤ ‖∑ i ∈ J, rankOneCoefficients (v i)‖^2 := by
  rw [← @inner_self_eq_norm_sq ℂ]
  simp only [sum_inner, inner_sum, map_sum]
  calc
    (J.card : ℝ) = ∑ i ∈ J, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ J, ∑ j ∈ J, (inner ℂ (rankOneCoefficients (v j)) (rankOneCoefficients (v i))).re := by
      apply Finset.sum_le_sum
      intro i hi
      have he : (inner ℂ (rankOneCoefficients (v i)) (rankOneCoefficients (v i))).re = 1 := by
        change RCLike.re (inner ℂ (rankOneCoefficients (v i)) (rankOneCoefficients (v i))) = 1
        rw [inner_self_eq_norm_sq, rankOne_norm_sq _ (hv i)]
      rw [← he]
      apply Finset.single_le_sum (f := fun j => (inner ℂ (rankOneCoefficients (v j)) (rankOneCoefficients (v i))).re) _ hi
      intro j hj
      rw [rankOne_inner_re]
      positivity

def coefficientMatrix (W : EuclideanSpace ℂ (K × K)) : Matrix K K ℂ :=
  fun a b => W (a,b)

/-- The coefficient norm is the unnormalized trace definition of
Hilbert–Schmidt squared norm. -/
theorem coefficient_norm_sq_eq_trace (W : EuclideanSpace ℂ (K × K)) :
    ‖W‖^2 = (Matrix.trace (Matrix.conjTranspose (coefficientMatrix W) * coefficientMatrix W)).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coefficientMatrix, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]
  simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.sum_comm (f := fun (a b : K) => ‖W (a,b)‖^2)

omit [Fintype K] in
theorem kernelCoefficients_offsupport (v : I → EuclideanSpace ℂ K) (s : I → G)
    {g : G} (hg : g ∉ Finset.univ.image s) : kernelCoefficients v s g = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  exact (hg (Finset.mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2⟩)).elim

theorem kernel_energy_summable (v : I → EuclideanSpace ℂ K) (s : I → G) :
    Summable (fun g => ‖kernelCoefficients v s g‖^2) := by
  classical
  apply summable_of_ne_finset_zero (s := Finset.univ.image s)
  intro g hg
  simp [kernelCoefficients_offsupport v s hg]

/-- The kernel-energy lower bound preserves every colliding product label. -/
theorem kernel_energy_ge_card (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (s : I → G) : (Fintype.card I : ℝ) ≤ ∑' g, ‖kernelCoefficients v s g‖^2 := by
  classical
  rw [tsum_eq_sum (s := Finset.univ.image s) (fun g hg => by
    simp [kernelCoefficients_offsupport v s hg])]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_eq_sum_card_image s Finset.univ)
  simp only [Finset.card_univ, Nat.cast_sum] at hc
  calc
    (Fintype.card I : ℝ) = ∑ g ∈ Finset.univ.image s, ((Finset.univ.filter fun i => s i = g).card : ℝ) := hc
    _ ≤ ∑ g ∈ Finset.univ.image s, ‖kernelCoefficients v s g‖^2 := by
      apply Finset.sum_le_sum
      intro g hg
      exact rankOne_sum_energy v hv _

end Dixmier

end

end OAI
