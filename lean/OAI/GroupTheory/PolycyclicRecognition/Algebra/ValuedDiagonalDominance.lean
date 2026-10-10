import OAI.GroupTheory.PolycyclicRecognition.Algebra.DiagonalDominantElement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ValuedIrreducibleFreePair

namespace OAI

/-! # Diagonal spectral gaps after a coefficient-field change -/

noncomputable section
namespace PolycyclicRecognition

theorem valued_diagonal_coordinate_kernel_bound {K I : Type*}
    [NormedField K] [Fintype I] (T : (I → K) →ₗ[K] (I → K)) (d : I → K)
    (hT : ∀ x i, T x i = d i * x i) (k : I) (b : ℝ) (hb : 0 ≤ b)
    (hd : ∀ j, j ≠ k → ‖d j‖ ≤ b) (x : I → K) (hx : x k = 0) :
    ‖T x‖ ≤ b * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg _))).mpr
  intro j
  rw [hT, norm_mul]
  by_cases hj : j = k
  · rw [hj, hx, norm_zero, mul_zero]
    exact mul_nonneg hb (norm_nonneg _)
  · exact mul_le_mul (hd j hj) (norm_le_pi_norm x j) (norm_nonneg _) hb

namespace PolynomialMatrixGroup

variable {K G : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [Group G] [TopologicalSpace G] [PreirreducibleSpace G] [ContinuousInv G] {n : ℕ}

theorem free_conjugate_powers_of_valued_diagonal_gaps
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))]
    (hn : 2 ≤ n) (a : G) (d : Bool → Fin n → K) (k : Bool → Fin n)
    (hdiag : ∀ s x i, linearAction (ι (if s then a⁻¹ else a)) x i = d s i * x i)
    (hgap : ∀ s j, j ≠ k s → ‖d s j‖ < ‖d s (k s)‖) :
    ∃ h : G, ∃ N : ℕ, 0 < N ∧ Function.Injective
      (FreeGroup.lift (fun i : Bool => if i then h * a ^ N * h⁻¹ else a ^ N)) := by
  classical
  have hk (s : Bool) : d s (k s) ≠ 0 :=
    diagonal_entry_ne_zero (linearAction (ι (if s then a⁻¹ else a))) (d s) (hdiag s) (k s)
  have hg (s : Bool) : ∃ b : ℝ, 0 ≤ b ∧ b < ‖d s (k s)‖ ∧
      ∀ j, j ≠ k s → ‖d s j‖ ≤ b := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      finite_diagonal_gap (fun j => ‖d s j‖) (k s) (norm_ne_zero_iff.mpr (hk s))
        (fun j hj => by simpa only [abs_of_nonneg (norm_nonneg _)] using hgap s j hj)
  choose b hb hbgap hbb using hg
  let v (s : Bool) : Fin n → K := Pi.single (k s) 1
  let φ (s : Bool) : (Fin n → K) →L[K] K := ContinuousLinearMap.proj (k s)
  apply free_conjugate_powers_of_irreducible_valued_dominant_element ι hι hn a φ v
    (fun s => d s (k s)) b
  · intro s
    ext j
    rw [hdiag]
    by_cases hj : j = k s
    · simp [v, hj]
    · simp [v, hj]
  · intro s
    simp [φ, v]
  · intro s x
    exact hdiag s x (k s)
  · exact hb
  · exact hbgap
  · intro s x hx
    exact valued_diagonal_coordinate_kernel_bound _ (d s) (hdiag s) (k s)
      (b s) (hb s) (hbb s) x hx

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
