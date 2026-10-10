import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockSpinIdentity
import OAI.Probability.InvariantIsing.Cavity.CavityFullTail

namespace OAI

/-! Cutoff control in the full perturbed model. The bad compression
event is paid for only by its probability, never by an inverse moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma restrictedCavityFullDisorderTest_sub {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F G : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F)) (hmG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) (hG : ∀ U σ, |G U σ| ≤ B) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => F U σ - G U σ) =
      restrictedCavityFullDisorderTest S hS μ T eig I u F - restrictedCavityFullDisorderTest S hS μ T eig I u G := by
  let H : Fin 2 → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ :=
    ![F, fun U σ => (-1 : ℝ) * G U σ]
  have hmH : ∀ i, Measurable (Function.uncurry (H i)) := by
    intro i
    fin_cases i
    · exact hmF
    · exact hmG.const_mul (-1)
  have hH : ∀ i U σ, |H i U σ| ≤ B := by
    intro i U σ
    fin_cases i
    · exact hF U σ
    · change |(-1 : ℝ) * G U σ| ≤ B
      simpa only [neg_one_mul, abs_neg] using hG U σ
  have hs := restrictedCavityFullDisorderTest_sum S hS μ T eig I u H hmH hB hH
  simp only [Fin.sum_univ_two] at hs
  change restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => F U σ + (-1 : ℝ) * G U σ) =
    restrictedCavityFullDisorderTest S hS μ T eig I u F +
      restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => (-1 : ℝ) * G U σ) at hs
  rw [restrictedCavityFullDisorderTest_const_mul] at hs
  simpa only [neg_one_mul, sub_eq_add_neg] using hs

lemma restrictedCavityFullDisorderTest_le_envelope {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B)
    (c : SpecialOrthogonal N → ℝ) (hc : Integrable c μ)
    (hc0 : ∀ U, 0 ≤ c U) (hFc : ∀ U σ, F U σ ≤ c U) :
    restrictedCavityFullDisorderTest S hS μ T eig I u F ≤ ∫ U, c U ∂μ := by
  exact cavity_nested_disorder_upper μ gaussianCoordinates
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _)
    (measurable_restrictedCavityFullDisorderInner S hS T eig I u F hmF) hB hF c hc hc0 hFc

theorem restricted_full_radial_cutoff {N m k d depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (axes : Fin k → Fin N) {M₀ : ℝ}
    (hmean : restrictedCavityFullDisorderTest S hS μ T eig I u (cavityProjectionAxesTest I axes) ≤ M₀)
    (good : Set (SpecialOrthogonal N))
    (hgood : MeasurableSet good)
    (y : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) →
      EuclideanSpace ℝ (Fin d))
    (φ : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmφ : Measurable (Function.uncurry φ)) (hφ : ∀ U σ, 0 ≤ φ U σ ∧ φ U σ ≤ 1)
    {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hzero : ∀ U σ, ‖y U σ‖ ≤ B → φ U σ = 0)
    (hgeometry : ∀ U ∈ good, ∀ σ,
      c * ‖y U σ‖ ^ 2 ≤ cavityProjectionAxesTest I axes U σ) :
    restrictedCavityFullDisorderTest S hS μ T eig I u φ ≤
      μ.real goodᶜ + M₀ / (c * B ^ 2) := by
  let R := cavityProjectionAxesTest (depth := depth) I axes
  let C := (c * B ^ 2)⁻¹
  have hden : 0 < c * B ^ 2 := mul_pos hc (sq_pos_of_pos hB)
  have hC : 0 ≤ C := inv_nonneg.mpr hden.le
  have hmR : Measurable (Function.uncurry R) := measurable_cavityProjectionAxesTest I axes
  have hR0 : ∀ U σ, 0 ≤ R U σ := cavityProjectionAxesTest_nonneg I axes
  have hRb : ∀ U σ, |R U σ| ≤ (m : ℝ) * k * N := cavityProjectionAxesTest_bound I axes
  have hφb : ∀ U σ, |φ U σ| ≤ 1 := fun U σ => by
    rw [abs_of_nonneg (hφ U σ).1]
    exact (hφ U σ).2
  have hdom : ∀ U ∈ good, ∀ σ, φ U σ ≤ C * R U σ := by
    intro U hU σ
    by_cases hy : ‖y U σ‖ ≤ B
    · rw [hzero U σ hy]
      exact mul_nonneg hC (hR0 U σ)
    · have hsq : B ^ 2 ≤ ‖y U σ‖ ^ 2 :=
        (sq_le_sq₀ hB.le (norm_nonneg _)).mpr (le_of_not_ge hy)
      have hprod : c * B ^ 2 ≤ R U σ :=
        (mul_le_mul_of_nonneg_left hsq hc.le).trans (hgeometry U hU σ)
      apply (hφ U σ).2.trans
      dsimp only [C]
      rw [← div_eq_inv_mul, le_div_iff₀ hden, one_mul]
      exact hprod
  let M := 1 + C * ((m : ℝ) * k * N)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hφM : ∀ U σ, |φ U σ| ≤ M := by
    intro U σ
    apply (hφb U σ).trans
    dsimp only [M]
    exact le_add_of_nonneg_right (mul_nonneg hC (by positivity))
  have hCRM : ∀ U σ, |C * R U σ| ≤ M := by
    intro U σ
    rw [abs_mul, abs_of_nonneg hC]
    exact (mul_le_mul_of_nonneg_left (hRb U σ) hC).trans (by dsimp [M]; linarith)
  have hDb : ∀ U σ, |φ U σ - C * R U σ| ≤ 1 + C * ((m : ℝ) * k * N) := by
    intro U σ
    calc
      _ ≤ |φ U σ| + |C * R U σ| := abs_sub _ _
      _ ≤ 1 + C * ((m : ℝ) * k * N) := by
        rw [abs_mul, abs_of_nonneg hC]
        exact add_le_add (hφb U σ) (mul_le_mul_of_nonneg_left (hRb U σ) hC)
  have hbad : Integrable (goodᶜ.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hgood.compl
  have hpoint : ∀ U σ, φ U σ - C * R U σ ≤ goodᶜ.indicator (fun _ => (1 : ℝ)) U := by
    intro U σ
    by_cases hU : U ∈ good
    · simpa only [Set.indicator_of_notMem (show U ∉ goodᶜ from fun hn => hn hU)] using
        sub_nonpos.mpr (hdom U hU σ)
    · rw [Set.indicator_of_mem hU]
      exact sub_le_iff_le_add.mpr ((hφ U σ).2.trans (le_add_of_nonneg_right (mul_nonneg hC (hR0 U σ))))
  have ht := restrictedCavityFullDisorderTest_le_envelope S hS μ T eig I u
    (fun U σ => φ U σ - C * R U σ) (hmφ.sub (hmR.const_mul C))
    hM hDb (goodᶜ.indicator (fun _ => (1 : ℝ))) hbad
    (fun U => Set.indicator_nonneg (fun _ _ => zero_le_one) U) hpoint
  rw [restrictedCavityFullDisorderTest_sub S hS μ T eig I u φ (fun U σ => C * R U σ)
    hmφ (hmR.const_mul C) hM hφM hCRM, restrictedCavityFullDisorderTest_const_mul,
    integral_indicator hgood.compl, setIntegral_const, smul_eq_mul, mul_one] at ht
  have hscale := mul_le_mul_of_nonneg_left hmean hC
  have he : C * M₀ = M₀ / (c * B ^ 2) := by
    simp only [C, div_eq_mul_inv, mul_comm]
  rw [he] at hscale
  dsimp only [R] at ht
  linarith

theorem restricted_full_tail_probability {N m k d depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (axes : Fin k → Fin N) {M₀ : ℝ}
    (hmean : restrictedCavityFullDisorderTest S hS μ T eig I u (cavityProjectionAxesTest I axes) ≤ M₀)
    (good : Set (SpecialOrthogonal N))
    (hgood : MeasurableSet good)
    (y : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) →
      EuclideanSpace ℝ (Fin d)) (hmy : Measurable (Function.uncurry y))
    {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hgeometry : ∀ U ∈ good, ∀ σ,
      c * ‖y U σ‖ ^ 2 ≤ cavityProjectionAxesTest I axes U σ) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => if B < ‖y U σ‖ then 1 else 0) ≤
      μ.real goodᶜ + M₀ / (c * B ^ 2) := by
  apply restricted_full_radial_cutoff S hS μ T eig I u axes hmean good hgood y
  · exact Measurable.ite (measurableSet_lt measurable_const hmy.norm)
      measurable_const measurable_const
  · intro U σ
    split_ifs <;> norm_num
  · exact hc
  · exact hB
  · intro U σ hy
    simp only [not_lt.mpr hy, ite_false]
  · exact hgeometry

end InvariantIsing

end

end OAI
