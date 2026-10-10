import OAI.MeasureTheory.Falconer.Recursion.ProjectionProfileMean
import OAI.MeasureTheory.Falconer.Geometry.ProjectionRescaling

namespace OAI

/-! # Exceptional mass for the original conditional-class projection tests -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_projection_exceptional {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ sig*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^sig →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p t : ℕ, p ≤ t → t ≤ N →
      ∀ P : CellPath d, P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      ∀ ν : Measure (Sphere d), ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ν (projectionGoodSet
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
        (2*((2:ℝ)^N)^(500*sig)/(2:ℝ)^t)
        ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
          profileDrop (sourceProfile Q μ N B p₀) N ((d:ℝ)/2) p t+
          1000*((d:ℝ)+1)*sig)))ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  let s : ℝ := (d:ℝ)/2
  let A : ℝ := (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hA : 1 ≤ A := by
    apply one_le_mul_of_one_le_of_one_le
    · exact_mod_cast one_le_pow₀ (show (1:ℕ) ≤ 2*Nat.ceil (2+4*Real.sqrt d)+1 by omega)
    · exact Real.one_le_rpow (by norm_num) hs
  obtain ⟨N₁,hmean⟩ := uniform_projection_profile_mean (d := d) hsig
    (Real.sqrt_nonneg d) hA (show 0 ≤ 2*((d:ℝ)+1) by positivity)
  refine ⟨max 1 N₁,?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ p t hpt htN P hP hocc ν hmass hball
  have hNp : 0 < N := lt_of_lt_of_le (by omega : 0 < 1) ((le_max_left _ _).trans hN)
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let ρ := ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
  let α := Measure.map (cellScaleMap p (Q.descendant P).center) ρ
  have : IsProbabilityMeasure ρ := sourceClass_conditional_probability Q hside μ N B hp₀ P hocc
  have : IsProbabilityMeasure α := by dsimp [α]; infer_instance
  have : IsFiniteMeasure ν := ⟨hmass.trans_lt (by norm_num)⟩
  let R : ℝ := (2:ℝ)^N
  let H : ℝ := (2:ℝ)^(t-p)
  let k := profileDrop (sourceProfile Q μ N B p₀) N s p t
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hHp : 0 < H := by positivity
  have hsupport : ∀ᵐ z ∂α, ‖z‖ ≤ Real.sqrt d := by
    simpa only [hP] using rescaled_conditional_support Q hQ (sourceClass Q μ N B p₀) P
  have hν : ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (R^sig*r^((d:ℝ)/2)) := by
    intro x r hr hr₁
    apply hball x r _ hr₁
    simpa only [Real.rpow_neg_one,one_div] using hr
  have hm := hmean N ((le_max_right _ _).trans hN) (t-p) (by omega) k
    (profileDrop_nonneg _ _ _ hpt) α ν hsupport hmass
    (sourceClass_conditional_frostman Q hQ μ hNp hB hs hwidth hlarge hp₀ hpt htN hP hocc) hν
  have hpow : (2:ℝ)^t = (2:ℝ)^p*(2:ℝ)^(t-p) := by
    rw [← pow_add]
    congr 1
    omega
  have hscale : (2:ℝ)^p*(2*R^(500*sig)/(2:ℝ)^t) = 2*R^(500*sig)/H := by
    rw [hpow]
    dsimp [H]
    field_simp
  have hgood : projectionGoodSet α (2*R^(500*sig)/H)
      ((1/H)*R^(k+1000*((d:ℝ)+1)*sig)) =
      projectionGoodSet ρ (2*R^(500*sig)/(2:ℝ)^t)
      ((1/H)*R^(k+1000*((d:ℝ)+1)*sig)) := by
    rw [← hscale]
    ext w
    simp only [projectionGoodSet,mem_ofPred_eq,α,
      projectionCollision_cellScaleMap]
  change ν (projectionGoodSet ρ _ _)ᶜ ≤ _
  rw [← hgood]
  apply (projectionGoodSet_exceptional α ν _ (by positivity :
    0 < (1/H)*R^(k+1000*((d:ℝ)+1)*sig))).trans
  apply (ENNReal.div_le_div_right hm _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  have he : ((1/H)*R^(k+(2*((d:ℝ)+1)+502)*sig))/
      ((1/H)*R^(k+1000*((d:ℝ)+1)*sig)) =
      R^((k+(2*((d:ℝ)+1)+502)*sig)-(k+1000*((d:ℝ)+1)*sig)) := by
    rw [mul_div_mul_left _ _ (by positivity : (1/H) ≠ 0),← Real.rpow_sub hRp]
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  nlinarith

end Falconer.Regularization

end OAI
