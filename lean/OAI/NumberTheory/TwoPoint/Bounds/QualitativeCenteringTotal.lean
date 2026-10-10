import OAI.NumberTheory.TwoPoint.Bounds.QualitativeCanonicalCentering
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeCenteringRate

namespace OAI

/-! Sum every actual logarithmic bin, retaining arbitrary unit-disk phase
weights and the exact padding and tuple normalizers. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem qualitative_canonical_nonraw_total (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTShortExponentialInput)
    {F G : ℕ → ℂ} (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      ∀ R : Finset ℕ, R ⊆ retainedPrimeDivisors Q →
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ᶠ X : ℝ in atTop, ∀ (eligible : ℤ → ℕ → ℕ → Prop) (v : ℤ → ℂ),
      (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      ‖∑ j ∈ bins, v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ ≤
        C * L ^ (-3 / 40 : ℝ) * paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hb⟩ := qualitative_canonical_nonraw_bin hP hM hMRT hFm hGm hF hG hnp
    h hh E W hW
  refine ⟨101 * C, by positivity, ?_⟩
  filter_upwards [hb, eventually_primeSupplyCount_two W (by linarith),
    eventually_ge_atTop (1 : ℝ)] with L hb hJ hL
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  intro R hR
  let η := Real.exp (-(J : ℝ))
  let bins := paddingBinIndices L η
  let V := paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i)
  have hη : 0 < η := Real.exp_pos _
  have hV : 0 ≤ V := mul_nonneg (paddingTiltNormalizer_pos Q).le
    (prod_nonneg (fun i _ => by unfold primeHarmonicMass; positivity))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hb R hR η hη (exp_double_neg_nat_lt_two J hJ))
  filter_upwards [eventually_ge_atTop (max T₀ 1)] with X hX
  intro eligible v hel hv
  have hXp : 0 ≤ X := by linarith [le_max_right T₀ (1 : ℝ)]
  have hterm (j : ℤ) (hj : j ∈ bins) :
      ‖v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ ≤
      C * canonicalRoughParameter L ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J * V := by
    have hgeom := (mem_paddingBinIndices_iff L η j hη).mp hj
    have ht : X ≤ X * Real.exp ((j : ℝ) * η) := by
      have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast hgeom.1
      exact le_mul_of_one_le_right hXp (Real.one_le_exp (mul_nonneg hj0 hη.le))
    have hb' := hT₀ (X * Real.exp ((j : ℝ) * η))
      ((le_max_left T₀ (1 : ℝ)).trans (hX.trans ht)) j hj (eligible j) (hel j hj)
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖nonrawComplexBin P R (eligible j) F G h
          (X * Real.exp ((j : ℝ) * η))‖ :=
        mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul, V, mul_assoc] using hb'
  have hcount := canonical_centering_bin_count_rate L J hL (primeSupplyCount_small_log W L hW hL)
  calc
    _ ≤ ∑ j ∈ bins, ‖v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ bins, C * canonicalRoughParameter L ^ (-11 / 10 : ℝ) * (2 : ℝ) ^ J * V :=
      sum_le_sum hterm
    _ = C * (((bins.card : ℝ) * (2 : ℝ) ^ J *
        canonicalRoughParameter L ^ (-11 / 10 : ℝ))) * V := by
      rw [sum_const, nsmul_eq_mul]
      ring
    _ ≤ C * (101 * L ^ (-3 / 40 : ℝ)) * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hC.le) hV
    _ = _ := by dsimp only [V]; ring

end TwoPointCorrelations

end OAI
