import OAI.Probability.InvariantIsing.Cavity.CavityValuePrimitive
import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerIntegral

namespace OAI

/-! The deterministic cavity value in the variational normalization.
The field pairing and spectral term arise from the weighted layer cake
and the spectral integration-by-parts identity. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_value_pairing_identity {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath) :
    finiteR rho lam hrho hsum 0 + cavityFieldDiagonal rho lam hrho hsum p -
      (∫ r in 0..1, cavityNormalizerDensity rho lam hrho hsum p r) =
        (∫ s, p s * cavityFieldPrimitive rho lam hrho hsum p (p s) ∂pathMeasure) +
          ∫ r, finiteR rho lam hrho hsum (deficit p r) ∂pathMeasure := by
  let f := cavityFieldDensity rho lam hrho hsum p
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hlam (a : Fin m) : |lam a| ≤ K :=
    Finset.single_le_sum (f := fun a => |lam a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hf : Continuous f := continuous_cavityFieldDensity rho lam hrho hsum p
  have hb (r : ℝ) : |f r| ≤ 4 * K ^ 2 := by
    change |cavityRDerivative rho lam hrho hsum (deficit p r)| ≤ 4 * K ^ 2
    rw [abs_of_nonneg (cavityRDerivative_nonneg rho lam hrho hsum (deficit p r))]
    exact cavityRDerivative_le rho lam hrho hsum hK hlam _
  have hp := cavity_weighted_primitive_fubini p f hf (by positivity : 0 ≤ 4 * K ^ 2) hb
  have hiD : IntervalIntegrable (fun r => deficit p r * f r) volume 0 1 :=
    ((continuous_deficit p).mul hf).intervalIntegrable 0 1
  have hiF : IntervalIntegrable (fun r => r * f r * pathMeasure.real {s | p s ≤ r}) volume 0 1 :=
    (pathCDF_monotone p).intervalIntegrable.continuousOn_mul (continuous_id.mul hf).continuousOn
  have he (r : ℝ) : f r * cavityTailMoment p r =
      f r - deficit p r * f r - r * f r * pathMeasure.real {s | p s ≤ r} := by
    rw [cavityTailMoment_eq_deficit]
    ring
  simp_rw [he] at hp
  rw [intervalIntegral.integral_sub ((hf.intervalIntegrable 0 1).sub hiD) hiF,
    intervalIntegral.integral_sub (hf.intervalIntegrable 0 1) hiD] at hp
  have hparts := cavity_spectral_integration_by_parts rho lam hrho hsum p
  rw [integral_pathMeasure_eq_interval (fun r => finiteR rho lam hrho hsum (deficit p r))]
  change finiteR rho lam hrho hsum 0 + (∫ r in 0..1, f r) -
      (∫ r in 0..1, deficit p r * f r) =
        (∫ s, p s * (∫ r in 0..p s, f r) ∂pathMeasure) +
          ∫ r in 0..1, finiteR rho lam hrho hsum (deficit p r)
  change (∫ r in 0..1, finiteR rho lam hrho hsum (deficit p r)) -
      (∫ r in 0..1, r * f r * pathMeasure.real {s | p s ≤ r}) = _ at hparts
  linarith

lemma cavityFieldStep_pairing {m n : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    fieldPairing p (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq hq0) =
      ∫ s, p s * cavityFieldPrimitive rho lam hrho hsum p (p s) ∂pathMeasure := by
  unfold fieldPairing
  apply integral_congr_ae
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [cavityFieldStep_on_cell rho lam hrho hsum p cut hcut hfirst hlast q hq hq0 hp j hj]

/-- The scalar Gaussian spin term plus the quadratic normalizer is
exactly the field value, field pairing, and spectral functional. -/
theorem cavity_finite_value_identity {m n : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq hq0
    fieldValue h 0 + (finiteR rho lam hrho hsum 0 + cavityFieldDiagonal rho lam hrho hsum p -
      (∫ r in 0..1, cavityNormalizerDensity rho lam hrho hsum p r)) / 2 =
        fieldValue h 0 + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p := by
  dsimp only
  rw [cavity_value_pairing_identity, cavityFieldStep_pairing rho lam hrho hsum p cut hcut
    hfirst hlast q hq hq0 hp, spectralFunctional]
  ring

end InvariantIsing

end

end OAI
