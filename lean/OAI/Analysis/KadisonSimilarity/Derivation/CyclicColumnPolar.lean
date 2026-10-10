import OAI.Analysis.KadisonSimilarity.Derivation.CStarRowSquare
import OAI.Analysis.KadisonSimilarity.Representation.RegularizedPolarFactor

namespace OAI

/-! Contractive regularized polar columns inside the source algebra. These
columns will supply dense cyclic vector tests with a varying unit vector. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder WithCStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A column is contractive when its positive column square is contractive. -/
theorem norm_column_le_of_starSquare {n : ℕ} (a : Fin n → A)
    (ha : ‖∑ i, star (a i) * a i‖ ≤ 1) :
    ‖CStarMatrix.ofMatrix (fun i (_ : Fin 1) => a i)‖ ≤ 1 := by
  let M := CStarMatrix.ofMatrix (fun i (_ : Fin 1) => a i)
  rw [← norm_cstarMatrix_conjTranspose M]
  change ‖CStarMatrix.toCLM M.conjTranspose‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hv : ‖v (0 : Fin 1)‖ ≤ ‖v‖ := WithCStarModule.norm_apply_le_norm _ _
  have hi : inner A (CStarMatrix.toCLM M.conjTranspose v)
      (CStarMatrix.toCLM M.conjTranspose v) =
      v 0 * (∑ i, star (a i) * a i) * star (v 0) := by
    rw [CStarMatrix.toCLM_apply_eq_sum]
    change (∑ i : Fin n, (∑ j : Fin 1, v j * star (a i)) *
      star (∑ j : Fin 1, v j * star (a i))) = _
    simp only [Fin.sum_univ_one, star_mul, star_star, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
  have hn : ‖CStarMatrix.toCLM M.conjTranspose v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    calc
      _ = ‖v 0 * (∑ i, star (a i) * a i) * star (v 0)‖ := by
        rw [CStarModule.norm_sq_eq A, hi]
      _ ≤ (‖v 0‖ * ‖∑ i, star (a i) * a i‖) * ‖v 0‖ :=
        (norm_mul_le _ _).trans (by
          rw [norm_star]
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖v‖ * 1) * ‖v‖ := by gcongr
      _ = ‖v‖ ^ 2 := by ring
  simpa only [one_mul] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg v)).mp hn

/-- The positive square root of a finite column square. -/
def cyclicColumnRoot {n : ℕ} (a : Fin n → A) : A :=
  CFC.sqrt (∑ i, star (a i) * a i)

theorem cyclicColumnRoot_nonneg {n : ℕ} (a : Fin n → A) : 0 ≤ cyclicColumnRoot a :=
  CFC.sqrt_nonneg _

theorem cyclicColumnRoot_sq {n : ℕ} (a : Fin n → A) :
    cyclicColumnRoot a * cyclicColumnRoot a = ∑ i, star (a i) * a i :=
  CFC.sqrt_mul_sqrt_self _ (Finset.sum_nonneg fun _ _ => star_mul_self_nonneg _)

/-- The regularized polar column stays in the original algebra. -/
def cyclicPolarColumn {n : ℕ} (a : Fin n → A) (ε : ℝ) : Matrix (Fin n) (Fin 1) A :=
  fun i _ => a i * positiveShiftReciprocal (cyclicColumnRoot a) ε

theorem cyclicPolarColumn_contract {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε) :
    ‖CStarMatrix.ofMatrix (cyclicPolarColumn a ε)‖ ≤ 1 := by
  let h := cyclicColumnRoot a
  let r := positiveShiftReciprocal h ε
  have hstar : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hc : r * h = h * r := (positiveShiftReciprocal_commute h ε).eq
  have he : (∑ i, star (a i * r) * (a i * r)) = (h * r) * (h * r) := by
    calc
      _ = r * (∑ i, star (a i) * a i) * r := by
        simp only [star_mul, hstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = r * (h * h) * r := by rw [← cyclicColumnRoot_sq a]
      _ = (r * h) * (h * r) := by noncomm_ring
      _ = (h * r) * (h * r) := by rw [hc]
  apply norm_column_le_of_starSquare
  change ‖∑ i, star (a i * r) * (a i * r)‖ ≤ 1
  rw [he]
  have hn := positiveShiftReciprocal_mul_norm_le h (cyclicColumnRoot_nonneg a) hε
  exact (norm_mul_le _ _).trans <| (mul_le_mul hn hn (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- Multiplication by the shifted root recovers every original column entry. -/
theorem cyclicPolarColumn_recover {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε)
    (i : Fin n) : cyclicPolarColumn a ε i 0 * (cyclicColumnRoot a + ε • (1 : A)) = a i := by
  let h := cyclicColumnRoot a
  let r := positiveShiftReciprocal h ε
  have hr : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hi := congrArg star (positiveShiftReciprocal_inverse h (cyclicColumnRoot_nonneg a) hε)
  have hrev : r * (h + ε • (1 : A)) = 1 := by
    simp only [star_mul, star_add, star_smul, star_trivial, star_one] at hi
    change star r * (star h + ε • (1 : A)) = 1 at hi
    have hh : star h = h := (cyclicColumnRoot_nonneg a).star_eq
    rwa [hr, hh] at hi
  change (a i * r) * (h + ε • (1 : A)) = a i
  rw [mul_assoc, hrev, mul_one]

end KadisonSimilarity

end

end OAI
