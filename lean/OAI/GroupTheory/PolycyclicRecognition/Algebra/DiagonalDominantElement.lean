import OAI.GroupTheory.PolycyclicRecognition.Algebra.IrreducibleDominantFreePair

namespace OAI

/-! # Spectral gaps for actual diagonal matrix actions

For the coordinate supremum norm, the restriction to a coordinate kernel
is bounded by the largest remaining diagonal entry. Strict spectral gaps
therefore supply all analytic estimates in the free-conjugate theorem.
-/

noncomputable section
namespace PolycyclicRecognition

theorem finite_diagonal_gap {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℝ) (k : I) (hk : d k ≠ 0)
    (hgap : ∀ j, j ≠ k → |d j| < |d k|) :
    ∃ b : ℝ, 0 ≤ b ∧ b < |d k| ∧ ∀ j, j ≠ k → |d j| ≤ b := by
  classical
  let f (j : I) := if j = k then (0 : ℝ) else |d j|
  let b := Finset.univ.sup' ⟨k, Finset.mem_univ k⟩ f
  have hb : 0 ≤ b := by
    have hh := Finset.le_sup' f (Finset.mem_univ k)
    simpa [f] using hh
  refine ⟨b, hb, (Finset.sup'_lt_iff _).mpr ?_, ?_⟩
  · intro j _
    by_cases hj : j = k
    · simpa [f, hj] using abs_pos.mpr hk
    · simpa [f, hj] using hgap j hj
  · intro j hj
    have hh := Finset.le_sup' f (Finset.mem_univ j)
    simpa [f, hj] using hh

theorem diagonal_coordinate_kernel_bound {I : Type*} [Fintype I]
    (T : (I → ℝ) →ₗ[ℝ] (I → ℝ)) (d : I → ℝ)
    (hT : ∀ x i, T x i = d i * x i) (k : I) (b : ℝ) (hb : 0 ≤ b)
    (hd : ∀ j, j ≠ k → |d j| ≤ b) (x : I → ℝ) (hx : x k = 0) :
    ‖T x‖ ≤ b * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg _))).mpr
  intro j
  rw [hT, Real.norm_eq_abs, abs_mul]
  by_cases hj : j = k
  · rw [hj, hx, abs_zero, mul_zero]
    exact mul_nonneg hb (norm_nonneg _)
  · exact mul_le_mul (hd j hj) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
      (abs_nonneg _) hb

theorem diagonal_entry_ne_zero {K I : Type*} [Field K] [DecidableEq I]
    (T : (I → K) ≃ₗ[K] (I → K)) (d : I → K)
    (hT : ∀ x i, T x i = d i * x i) (i : I) : d i ≠ 0 := by
  intro hi
  let v : I → K := Pi.single i 1
  have hv : T v = 0 := by
    ext j
    rw [hT]
    by_cases hj : j = i
    · simp [hj, hi]
    · simp [v, hj]
  have hz : v = 0 := T.injective (by simpa only [map_zero] using hv)
  have he := congrFun hz i
  simp [v] at he

namespace PolynomialMatrixGroup

variable {G : Type} [Group G] [TopologicalSpace G] [PreirreducibleSpace G]
    [ContinuousInv G] {n : ℕ}

theorem free_conjugate_powers_of_diagonal_gaps
    (ι : G →* PolynomialMatrixGroup ℝ n) (hι : Continuous ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))]
    (hn : 2 ≤ n) (a : G) (d : Bool → Fin n → ℝ) (k : Bool → Fin n)
    (hdiag : ∀ s x i, linearAction (ι (if s then a⁻¹ else a)) x i = d s i * x i)
    (hgap : ∀ s j, j ≠ k s → |d s j| < |d s (k s)|) :
    ∃ h : G, ∃ N : ℕ, 0 < N ∧ Function.Injective
      (FreeGroup.lift (fun i : Bool => if i then h * a ^ N * h⁻¹ else a ^ N)) := by
  classical
  have hk (s : Bool) : d s (k s) ≠ 0 :=
    diagonal_entry_ne_zero (linearAction (ι (if s then a⁻¹ else a))) (d s) (hdiag s) (k s)
  choose b hb hbgap hbb using fun s => finite_diagonal_gap (d s) (k s) (hk s) (hgap s)
  let v (s : Bool) : Fin n → ℝ := Pi.single (k s) 1
  let φ (s : Bool) : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (k s)
  apply free_conjugate_powers_of_irreducible_dominant_element ι hι hn a φ v
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
    exact diagonal_coordinate_kernel_bound _ (d s) (hdiag s) (k s) (b s) (hb s) (hbb s) x hx

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
