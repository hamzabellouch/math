import OAI.Analysis.KadisonKastler.PreparedPairIrreducibility
import OAI.Analysis.KadisonKastler.PreparedPairState

namespace OAI

/-! # Matrix averages in the centralizer of a vector state

Finite signed-permutation averages preserve a vector state centralizing
the matrix stages. Their bounded weak cluster points are scalar by
relative irreducibility. State preservation identifies each scalar, and
the ultrafilter criterion then gives actual weak convergence of the whole
sequence. No traciality of the ambient algebra is required.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def ambientVectorFunctional (Ω : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun x := inner ℂ Ω (x Ω)
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

/-- Each finite average preserves the vector state when its unitary
matrix group lies in the state's centralizer. -/
theorem matrixUnitAverage_preserves_vectorFunctional
    (M : VonNeumannAlgebra H) (Ω : H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hcentral : ∀ a ∈ E.algebra, ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    inner ℂ Ω (matrixUnitAverage E x Ω) = inner ℂ Ω (x Ω) := by
  let φ := ambientVectorFunctional Ω
  have hconj (g : SignedPermutation (Fin d)) :
      φ (unitaryConj (matrixUnitSignedRepresentation E g) x) = φ x := by
    let u := matrixUnitSignedRepresentation E g
    have hu : (u : H →L[ℂ] H) ∈ E.algebra := matrixUnitSignedRepresentation_mem E g
    have hc := hcentral u hu (x * star (u : H →L[ℂ] H))
      (M.mul_mem hx (M.toStarSubalgebra.star_mem' (hEM hu)))
    change inner ℂ Ω (((u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) Ω) =
      inner ℂ Ω (x Ω)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using hc
  change φ (finiteAverage (fun g => unitaryConj (matrixUnitSignedRepresentation E g) x)) = φ x
  have hmap : φ (finiteAverage (fun g => unitaryConj (matrixUnitSignedRepresentation E g) x)) =
      finiteAverage (fun g : SignedPermutation (Fin d) =>
        φ (unitaryConj (matrixUnitSignedRepresentation E g) x)) := by
    simp only [finiteAverage, map_smul, map_sum]
  rw [hmap]
  simpa only [hconj] using (finiteAverage_const (G := SignedPermutation (Fin d)) (φ x))

private theorem stateAverage_norm_le {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖matrixUnitAverage E x‖ ≤ ‖x‖ := by
  apply norm_finiteAverage_le
  intro g
  exact (norm_unitaryConj (matrixUnitSignedRepresentation E g) x).le

theorem matrixUnitAverage_mem_algebra {d : ℕ} (M : VonNeumannAlgebra H)
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (x : H →L[ℂ] H) (hx : x ∈ M) : matrixUnitAverage E x ∈ M := by
  change (Fintype.card (SignedPermutation (Fin d)) : ℂ)⁻¹ •
    ∑ g : SignedPermutation (Fin d),
      ((matrixUnitSignedRepresentation E g : H →L[ℂ] H) * x *
        star (matrixUnitSignedRepresentation E g : H →L[ℂ] H)) ∈ M
  apply M.toStarSubalgebra.smul_mem
  apply M.toStarSubalgebra.sum_mem
  intro g _
  exact M.mul_mem (M.mul_mem (hEM (matrixUnitSignedRepresentation_mem E g)) hx)
    (M.toStarSubalgebra.star_mem' (hEM (matrixUnitSignedRepresentation_mem E g)))

/-- The entire sequence of concrete matrix averages converges weakly to
the scalar determined by the normalized vector state. -/
theorem matrixUnitAverage_tendsto_vectorState
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (ξ η : H) :
    Tendsto (fun n => inner ℂ η (matrixUnitAverage (E n) x ξ)) atTop
      (𝓝 (inner ℂ η (((inner ℂ Ω (x Ω)) • (1 : H →L[ℂ] H)) ξ))) := by
  apply (tendsto_iff_ultrafilter _ _ _).mpr
  intro ω hω
  let f : ℕ → H →L[ℂ] H := fun n => matrixUnitAverage (E n) x
  obtain ⟨T, _, hlim⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω f ‖x‖
    (norm_nonneg x) (fun n => stateAverage_norm_le (E n) x)
  have hTM : T ∈ M := Generator.Tracial.weak_operator_limit_mem M
    (fun n => ⟨f n, matrixUnitAverage_mem_algebra M (E n) (hEM n) x hx⟩) T hlim
  obtain ⟨z, hz⟩ := hirr T hTM
    (matrixUnitAverage_weak_limit_commutes d E hmono x T hω hlim)
  have hpreserve (n : ℕ) : inner ℂ Ω (f n Ω) = inner ℂ Ω (x Ω) :=
    matrixUnitAverage_preserves_vectorFunctional M Ω (E n) (hEM n) (hcentral n) x hx
  have hstate : inner ℂ Ω (T Ω) = inner ℂ Ω (x Ω) := by
    apply tendsto_nhds_unique (hlim Ω Ω)
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ Ω (x Ω))
      (ω : Filter ℕ) (𝓝 (inner ℂ Ω (x Ω)))).congr'
        (Eventually.of_forall fun n => (hpreserve n).symm)
  have hzstate : z = inner ℂ Ω (x Ω) := by
    rw [hz] at hstate
    simpa [smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ] using hstate
  simpa only [hz, hzstate] using hlim ξ η

/-- Weak coefficient convergence gives the corresponding sandwiched
vector-state limit, the form used for mixed fourth moments. -/
theorem vectorState_sandwich_tendsto
    {I : Type*} {l : Filter I} (F : I → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hlim : ∀ ξ η, Tendsto (fun i => inner ℂ η (F i ξ)) l (𝓝 (inner ℂ η (T ξ))))
    (Ω : H) (a b : H →L[ℂ] H) :
    Tendsto (fun i => inner ℂ Ω ((a * F i * b) Ω)) l
      (𝓝 (inner ℂ Ω ((a * T * b) Ω))) := by
  simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using hlim (b Ω) (star a Ω)

end

end KadisonKastler

end OAI
