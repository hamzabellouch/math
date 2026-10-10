import OAI.Geometry.RCD.Coordinates.UnitCoordinateDirections
import OAI.Geometry.RCD.Harmonic.FiniteMeasuredHarmonicSequence

namespace OAI

/-! # The normalized sums of the actual harmonic coordinate components -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.harmonic_coordinate_pair_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (p : ℕ → X) (r : ℕ → ℝ)
    (V : ℕ → X → Euclidean n) (w : Fin n → ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w i k))
    (hnorm : ∀ i k, harmonicTargetNorm hX (p k) (5*r k) (w i k)≤7)
    (hconv : ∀ i W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x-V k x i|≤δ)
    (i j : Fin n) :
    let q := fun k => (Real.sqrt 2)⁻¹ • (w i k+w j k)
    let L := (Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)+EuclideanSpace.proj j)
    (∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (q k)) ∧
    (∀ k, harmonicTargetNorm hX (p k) (5*r k) (q k)≤14) ∧
    (∀ W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-L (V k x)|≤δ) := by
  dsimp only
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1≤Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hc : (Real.sqrt 2)⁻¹≤1 := (inv_le_one₀ hs).mpr hs1
  refine ⟨fun k => ((hw i k).add _ _ (hw j k)).smul _ _ _,?_,?_⟩
  · intro k
    rw [harmonicTargetNorm_smul,abs_of_pos (inv_pos.mpr hs)]
    have hh := harmonicTargetNorm_add_le hX (p k) (5*r k) (w i k) (w j k)
    have hsum : harmonicTargetNorm hX (p k) (5*r k) (w i k+w j k)≤14 := by
      linarith [hnorm i k,hnorm j k]
    calc
      _ ≤ (Real.sqrt 2)⁻¹*14 := mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hs).le
      _ ≤ 14 := by nlinarith
  · intro W hW hW5 δ hδ
    filter_upwards [hconv i W hW hW5 (δ/2) (half_pos hδ),
      hconv j W hW hW5 (δ/2) (half_pos hδ)] with k hi hj
    have hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic
        ((Real.sqrt 2)⁻¹ • (w i k+w j k)) =ᵐ[hausdorff n X]
        fun x => (Real.sqrt 2)⁻¹*(SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x+
          SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j k) x) := by
      rw [map_smul,map_add]
      filter_upwards [Lp.coeFn_smul (Real.sqrt 2)⁻¹
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k)+
          SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j k)),
        Lp.coeFn_add (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k))
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j k))] with x hsx hax
      simpa only [Pi.smul_apply,smul_eq_mul,hax,Pi.add_apply] using hsx
    filter_upwards [hi,hj,ae_restrict_of_ae hrep] with x hix hjx hx
    rw [hx]
    change |(Real.sqrt 2)⁻¹*(_+_)-(Real.sqrt 2)⁻¹*(V k x i+V k x j)|≤δ
    have he : (Real.sqrt 2)⁻¹*(SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x+
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j k) x)-(Real.sqrt 2)⁻¹*(V k x i+V k x j)=
        (Real.sqrt 2)⁻¹*((SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x-V k x i)+
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j k) x-V k x j)) := by ring
    rw [he,abs_mul,abs_of_pos (inv_pos.mpr hs)]
    calc
      _ ≤ (Real.sqrt 2)⁻¹*(|SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x-V k x i|+
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j k) x-V k x j|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_pos.mpr hs).le
      _ ≤ (Real.sqrt 2)⁻¹*δ := mul_le_mul_of_nonneg_left (by linarith) (inv_pos.mpr hs).le
      _ ≤ δ := by nlinarith

end RegularPointCoordinates

end

end OAI
