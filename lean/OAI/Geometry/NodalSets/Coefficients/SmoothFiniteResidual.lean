import OAI.Geometry.NodalSets.Elliptic.UniformTransportPolynomial
import OAI.Geometry.NodalSets.Waves.SmoothWaveOperator

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def revalLinear (x : Coord) : CPoly →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval (fun i ↦ (x i : ℂ))).toLinearMap

lemma revalLinear_apply (x : Coord) (p : CPoly) : revalLinear x p = reval p x := by
  simp [revalLinear, reval, aeval_def]

def secondOrderAt (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (x : Coord) : CPoly →ₗ[ℂ] ℂ :=
  (∑ i, ∑ j, g i j x • ((revalLinear x).comp
    ((pderiv i).toLinearMap.comp (pderiv j).toLinearMap))) +
    ∑ i, b i x • ((revalLinear x).comp (pderiv i).toLinearMap)

def transportAt (W : Fin 4 → Coord → ℂ) (c : Coord → ℂ)
    (x : Coord) : CPoly →ₗ[ℂ] ℂ :=
  (∑ i, W i x • ((revalLinear x).comp (pderiv i).toLinearMap)) + c x • revalLinear x

lemma secondOrderAt_apply (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (x : Coord) (p : CPoly) : secondOrderAt g b x p = smoothSecondOrder g b (reval p) x := by
  simp [secondOrderAt, smoothSecondOrder, coordPartial_reval, revalLinear_apply, smul_eq_mul]

lemma transportAt_apply (W : Fin 4 → Coord → ℂ) (c : Coord → ℂ) (x : Coord) (p : CPoly) :
    transportAt W c x p = smoothTransport W c (fun _ ↦ 0) (reval p) x := by
  simp [transportAt, smoothTransport, coordPartial_reval, revalLinear_apply, smul_eq_mul]

theorem evaluated_transport_telescope (B L : CPoly →ₗ[ℂ] ℂ) (a : ℕ → CPoly)
    (N : ℂ) (hN : N ≠ 0) (J : ℕ) :
    N * B (∑ j ∈ Finset.range (J + 1), (N⁻¹ ^ j) • a j) +
      L (∑ j ∈ Finset.range (J + 1), (N⁻¹ ^ j) • a j) =
    N * B (a 0) +
      (∑ j ∈ Finset.range J, (N⁻¹ ^ j) * (B (a (j + 1)) + L (a j))) +
      (N⁻¹ ^ J) * L (a J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ (n := J + 1), map_add, map_add, map_smul, map_smul]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [smul_eq_mul]
    have hpow : N * N⁻¹ ^ (J + 1) = N⁻¹ ^ J := by
      rw [pow_succ]
      field_simp
    calc
      _ = (N * B (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j) +
        L (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j)) +
        (N * N⁻¹ ^ (J + 1)) * B (a (J + 1)) + N⁻¹ ^ (J + 1) * L (a (J + 1)) := by ring
      _ = _ := by rw [ih, hpow]; ring

lemma finiteAmplitude_range_reval (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    reval (∑ j ∈ Finset.range (J + 1), ((N : ℂ)⁻¹ ^ j) • A j) = finiteAmplitude A J N := by
  funext x
  simp [finiteAmplitude, polynomialFamily, reval, Algebra.smul_def]
  exact (Fin.sum_univ_eq_sum_range (fun j ↦ ((N : ℂ)^j)⁻¹ *
    eval (fun i ↦ (x i : ℂ)) (A j)) (J + 1)).symm

theorem smooth_finite_transport_telescope
    (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (phi : Coord → ℂ) (A : ℕ → CPoly) (J : ℕ) {N : ℝ} (hN : N ≠ 0) (x : Coord) :
    (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
      (fun _ ↦ 0) (finiteAmplitude A J N) x + smoothSecondOrder g b (finiteAmplitude A J N) x =
    (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
      (fun _ ↦ 0) (reval (A 0)) x +
      (∑ j ∈ Finset.range J, ((N : ℂ)⁻¹ ^ j) *
        (smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
          (fun _ ↦ 0) (reval (A (j + 1))) x + smoothSecondOrder g b (reval (A j)) x)) +
      ((N : ℂ)⁻¹ ^ J) * smoothSecondOrder g b (reval (A J)) x := by
  have h := evaluated_transport_telescope
    (transportAt (smoothBeamVector g phi) (smoothBeamScalar g b phi) x)
    (secondOrderAt g b x) A (N : ℂ) (by exact_mod_cast hN) J
  simpa only [transportAt_apply, secondOrderAt_apply, finiteAmplitude_range_reval] using h

theorem smooth_finite_wave_residual
    (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (hg : ∀ i j x, g i j x = g j i x)
    (phi : Coord → ℂ) (hp : ContDiff ℝ ∞ phi) (A : ℕ → CPoly) (J : ℕ)
    {N : ℝ} (hN : N ≠ 0) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ finiteAmplitude A J N z * waveExp phi N z) x +
      ((4 : ℂ) * (N : ℂ)^2 + 6 * (N : ℂ)) *
        (finiteAmplitude A J N x * waveExp phi N x) =
    waveExp phi N x *
      ((N : ℂ)^2 * smoothEikonal g phi x * finiteAmplitude A J N x +
        (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
          (fun _ ↦ 0) (reval (A 0)) x +
        (∑ j ∈ Finset.range J, ((N : ℂ)⁻¹ ^ j) *
          (smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
            (fun _ ↦ 0) (reval (A (j + 1))) x + smoothSecondOrder g b (reval (A j)) x)) +
        ((N : ℂ)⁻¹ ^ J) * smoothSecondOrder g b (reval (A J)) x) := by
  rw [smooth_wave_residual_identity g b hg hp (finiteAmplitude_contDiff A J N)]
  have h := smooth_finite_transport_telescope g b phi A J hN x
  congr 1
  linear_combination h

end
end Yau.Jets

end OAI
