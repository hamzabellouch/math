import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicMetricRemainder
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFiniteAnsatz
import OAI.Geometry.SurfaceImmersion.Geometry.FlatExtension

namespace OAI

/-! Support preservation for the actual finite periodic expansion. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma periodic_family_flat_on_closure (F : Family A E) {O : Set A} (hO : IsOpen O)
    (hz : ∀ p ∈ O, F.val p = 0) (n : ℕ) {p : A} (hp : p ∈ closure O) (t : ℝ) :
    iteratedFDeriv ℝ n (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) = 0 := by
  apply iteratedFDeriv_zero_on_closure F.smooth (hO.prod isOpen_univ)
    (O := O ×ˢ (Set.univ : Set ℝ))
  · intro z hz'
    rw [hz z.1 hz'.1]
    rfl
  · simpa only [closure_prod_eq, closure_univ, Set.mem_prod, Set.mem_univ, and_true] using hp

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_eq_base_of_zero (F : A → E) (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {p : A} (hU : ∀ i, (U i).val p = 0) :
    finiteAnsatz F U ℓ L z p = F p := by
  simp only [finiteAnsatz, Family.fastValue, hU, ContinuousMap.zero_apply,
    smul_zero, Finset.sum_const_zero, add_zero]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma metricCoefficientFamily_zero_of_positive_coefficients (n r : ℕ) (hr : 0 < r)
    (a b : ℕ → Family A E) {p : A}
    (ha : ∀ i, 0 < i → (a i).val p = 0)
    (hb : ∀ i, 0 < i → (b i).val p = 0) :
    (metricCoefficientFamily n r a b).val p = 0 := by
  ext t
  simp only [metricCoefficientFamily, Family.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : i + j = r
  · simp only [hij, ite_true, Family.inner_apply]
    by_cases hip : 0 < i
    · rw [ha i hip]
      exact inner_zero_left _
    · rw [hb j (by omega)]
      exact inner_zero_right _
  · simp only [hij, ite_false, Family.zero_apply]

namespace Geometry

variable {dy : A} (g : Geometry (E := E) dy)

omit [FiniteDimensional ℝ E] in
lemma initial_zero_of_constant {p : A} {w : E}
    (hV : g.V.val p = ContinuousMap.const Period w) : g.initial.val p = 0 := by
  have hw : (g.V - g.V.vectorMean).val p = 0 := by
    ext t
    change g.V.val p t - average (g.V.val p) = 0
    rw [hV]
    change w - average (fun _ => w) = 0
    rw [average_const, sub_self]
  exact primitiveFamily_zero_at (g.V - g.V.vectorMean).val
    (g.V - g.V.vectorMean).smooth g.V.centered_mean_zero hw

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xTangent_zero_on {O : Set A} (hO : IsOpen O) (U : ℕ → Family A E)
    (hU : ∀ i p, p ∈ O → (U i).val p = 0) (dx : A) (L i : ℕ)
    (hi : 0 < i) {p : A} (hp : p ∈ O) : (g.xTangent dx U L i).val p = 0 := by
  unfold xTangent
  rw [ite_eq_right (ne_of_gt hi)]
  split_ifs
  · exact (U (i - 1)).slow_zero_on hO (hU (i - 1)) dx hp
  · exact xCoefficient_zero_on hO U hU dx i hp

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yTangent_zero_on {O : Set A} (hO : IsOpen O) (U : ℕ → Family A E)
    (hU : ∀ i p, p ∈ O → (U i).val p = 0) (i : ℕ)
    (hi : 0 < i) {p : A} (hp : p ∈ O) : (g.yTangent U i).val p = 0 := by
  rw [g.yTangent_pos U hi]
  exact yCoefficient_zero_on hO U hU dy i hp

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma remainders_zero_on {O : Set A} (hO : IsOpen O) (U : ℕ → Family A E)
    (hU : ∀ i p, p ∈ O → (U i).val p = 0) (dx : A) (L r : ℕ)
    (hr : 0 < r) {p : A} (hp : p ∈ O) :
    (g.xxRemainder dx U L r).val p = 0 ∧
    (g.xyRemainder dx U L r).val p = 0 ∧
    (g.yyRemainder U L r).val p = 0 := by
  have hx := fun i hi => g.xTangent_zero_on hO U hU dx L i hi hp
  have hy := fun i hi => g.yTangent_zero_on hO U hU i hi hp
  exact ⟨metricCoefficientFamily_zero_of_positive_coefficients L r hr _ _ hx hx,
    metricCoefficientFamily_zero_of_positive_coefficients L r hr _ _ hx hy,
    metricCoefficientFamily_zero_of_positive_coefficients L r hr _ _ hy hy⟩

end Geometry
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
