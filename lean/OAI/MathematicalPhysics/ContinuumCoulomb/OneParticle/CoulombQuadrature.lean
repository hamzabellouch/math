import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawCoulombSampleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombCubeModulus

namespace OAI

/-! Actual six-coordinate cubature of the finite Coulomb integral. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RawCoulombSample
open UniformQuadrature

def quadratureInput (R P b : ℕ) (ε : ℚ) (s : CappedKernelProgram.Triple) (N : ℕ) :
    RationalSixQuadrature.Input Settings :=
  (N, (((R, P), ((b, ε), s)), (-(R : ℚ), 2 * (R : ℚ) / (N : ℚ))))

def sampled (rho R P b : ℕ) (ε : ℚ) (s : CappedKernelProgram.Triple)
    (a h : ℚ) (w : Fin 6 → ℕ) : ℝ :=
  value rho R P b ε s
    (RationalQuadratureProgram.node a h (w 0),
      RationalQuadratureProgram.node a h (w 1),
      RationalQuadratureProgram.node a h (w 2))
    (RationalQuadratureProgram.node a h (w 3),
      RationalQuadratureProgram.node a h (w 4),
      RationalQuadratureProgram.node a h (w 5))

theorem quadrature_cast (rho R P b : ℕ) (ε : ℚ) (s : CappedKernelProgram.Triple) (N : ℕ) :
    (RationalSixQuadrature.value (sixEvaluator rho) (quadratureInput R P b ε s N) : ℝ) =
      cubeSample (2 * (R : ℝ) / (N : ℝ)) N 6
        (sampled rho R P b ε s (-(R : ℚ)) (2 * (R : ℚ) / (N : ℚ))) := by
  rw [RationalSixQuadrature.value_cast]
  simp only [quadratureInput, sixEvaluator, evaluate, sampled, cubeSample, rectangleSum,
    Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Fin.cons_zero]
  rfl

theorem position_sampled (a h : ℚ) (w : Fin 6 → ℕ) :
    (CappedKernelProgram.position
      (RationalQuadratureProgram.node a h (w 0),
        RationalQuadratureProgram.node a h (w 1),
        RationalQuadratureProgram.node a h (w 2)),
     CappedKernelProgram.position
      (RationalQuadratureProgram.node a h (w 3),
        RationalQuadratureProgram.node a h (w 4),
        RationalQuadratureProgram.node a h (w 5))) =
      twoParticleCoordinates (fun i => node (a : ℝ) (h : ℝ) (w i)) := by
  apply Prod.ext
  · ext i
    rw [twoParticleCoordinates_fst]
    fin_cases i <;> simp [CappedKernelProgram.position, RationalQuadratureProgram.node_cast]
  · ext i
    rw [twoParticleCoordinates_snd]
    fin_cases i <;> simp [CappedKernelProgram.position, RationalQuadratureProgram.node_cast]

theorem quadrature_error (rho R P b N : ℕ) {ε : ℚ} (hε : 0 < ε)
    (hN : 0 < N) (s : CappedKernelProgram.Triple) :
    |(RationalSixQuadrature.value (sixEvaluator rho) (quadratureInput R P b ε s N) : ℝ) -
      cubeIntegral (-(R : ℝ)) (R : ℝ) 6
        (rawCoulombSix (GaussianFrequency.frequency rho) (ε : ℝ) (CappedKernelProgram.position s))| ≤
      (2 * (R : ℝ)) ^ 6 *
        (6 * ((64 + 2 * GaussianFrequency.frequency rho * R) * (ε : ℝ)⁻¹ + (ε : ℝ)⁻¹ ^ 2) *
          (2 * (R : ℝ) / N) +
          (8 * (ε : ℝ)⁻¹ * ((P : ℝ) + 1)⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b)) := by
  let h : ℚ := 2 * (R : ℚ) / (N : ℚ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfreq : 0 ≤ GaussianFrequency.frequency rho := Real.sqrt_nonneg _
  have hh : (0 : ℝ) ≤ h := by dsimp only [h]; push_cast; positivity
  have he : node (-(R : ℝ)) (h : ℝ) N = R := by
    dsimp only [node, h]
    push_cast
    field_simp [hNr.ne']
    ring
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hmod := rawCoulombSix_modulus hfreq hεr
    (Nat.cast_nonneg R) (CappedKernelProgram.position s)
  have hsamp : ∀ w : Fin 6 → ℕ, (∀ i, w i < N) →
      |sampled rho R P b ε s (-(R : ℚ)) h w -
        rawCoulombSix (GaussianFrequency.frequency rho) (ε : ℝ) (CappedKernelProgram.position s)
          (fun i => node (-(R : ℝ)) (h : ℝ) (w i))| ≤
        8 * (ε : ℝ)⁻¹ * ((P : ℝ) + 1)⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b := by
    intro w hw
    have hbnd (i : Fin 6) : |(RationalQuadratureProgram.node (-(R : ℚ)) h (w i) : ℝ)| ≤ R := by
      rw [RationalQuadratureProgram.node_cast]
      have hi := node_mem (a := -(R : ℝ)) hh (hw i).le
      rw [he] at hi
      simpa only [Rat.cast_neg, Rat.cast_natCast] using abs_le.mpr hi
    have ht := value_error rho R P b hε s
      (RationalQuadratureProgram.node (-(R : ℚ)) h (w 0),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 1),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 2))
      (RationalQuadratureProgram.node (-(R : ℚ)) h (w 3),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 4),
        RationalQuadratureProgram.node (-(R : ℚ)) h (w 5))
      ⟨hbnd 0, hbnd 1, hbnd 2⟩ ⟨hbnd 3, hbnd 4, hbnd 5⟩
    rw [position_sampled] at ht
    simpa only [sampled, rawCoulombSix, Rat.cast_neg, Rat.cast_natCast] using ht
  have ht := cube_quadrature_error 6
    (L := (64 + 2 * GaussianFrequency.frequency rho * R) * (ε : ℝ)⁻¹ + (ε : ℝ)⁻¹ ^ 2)
    hh (by positivity) (by positivity) (by simpa only [he] using hmod) hsamp
  rw [he] at ht
  rw [quadrature_cast]
  have hlen : (N : ℝ) * (h : ℝ) = 2 * R := by
    dsimp only [h]
    push_cast
    field_simp [hNr.ne']
  rw [hlen] at ht
  simpa only [Nat.cast_ofNat, h, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using ht

end ContinuumCoulomb.RawCoulombSample

end

end OAI
