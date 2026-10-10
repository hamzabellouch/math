import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalCutoff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace OAI

/-! Compact cutoff densities for compressed nuclear matrix elements. The
fourth-order source bounds grow only cubically in the cutoff radius. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def compactOrbitalDensity (freq R : ℝ) (u v : PlanarPosition) (x : Position) : ℝ :=
  orbitalCutoff R u x*(continuumLocalizedMode freq u x*continuumLocalizedMode freq v x)

theorem compactOrbitalDensity_nonnegative {freq : ℝ} (hfreq : 0 < freq)
    (R : ℝ) (u v : PlanarPosition) (x : Position) :
    0 ≤ compactOrbitalDensity freq R u v x :=
  mul_nonneg (orbitalCutoff_nonnegative R u x)
    (mul_nonneg (continuumLocalizedMode_positive hfreq u x).le
      (continuumLocalizedMode_positive hfreq v x).le)

theorem compactOrbitalDensity_C4 (freq R : ℝ) (u v : PlanarPosition) :
    ContDiff ℝ 4 (compactOrbitalDensity freq R u v) :=
  ((orbitalCutoff_smooth R u).of_le (by simp)).mul
    (((continuumLocalizedMode_C7 freq u).of_le (by norm_num)).mul
      ((continuumLocalizedMode_C7 freq v).of_le (by norm_num)))

theorem compactOrbitalDensity_support (freq : ℝ) {R : ℝ} (hR : 0 < R) (u v : PlanarPosition) :
    tsupport (compactOrbitalDensity freq R u v) ⊆ Metric.closedBall (planarCenter u) (2*R) :=
  tsupport_mul_subset_left.trans (orbitalCutoff_support hR u)

theorem compactOrbitalDensity_hasCompactSupport (freq : ℝ) {R : ℝ} (hR : 0 < R)
    (u v : PlanarPosition) : HasCompactSupport (compactOrbitalDensity freq R u v) :=
  (orbitalCutoff_hasCompactSupport hR u).mul_right

private theorem ball_supported_jet_integral {F : Type*} [NormedAddCommGroup F]
    {q : Position → F} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (u : PlanarPosition)
    (hs : tsupport q ⊆ Metric.closedBall (planarCenter u) (2*R))
    (hb : ∀ x, ‖q x‖ ≤ B) : (∫ x, ‖q x‖) ≤ 64*B*R^3 := by
  let S := Metric.closedBall (planarCenter u) (2*R)
  have he : (∫ x in S, ‖q x‖) = ∫ x, ‖q x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hsx => hx (hs hsx)),norm_zero])
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun x => ‖q x‖)
    (s := S) (isCompact_closedBall _ _).measure_lt_top (fun x _ => by simpa using hb x)
  rw [he] at h
  have hvol : volume.real S = (2*R)^3*(Real.pi*4/3) := by
    simp only [S,Measure.real,EuclideanSpace.volume_closedBall_fin_three,
      ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*R),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  rw [hvol] at h
  have hpi : Real.pi*4/3 ≤ 8 := by linarith [Real.pi_lt_four]
  calc
    _ ≤ ‖∫ x, ‖q x‖‖ := le_abs_self _
    _ ≤ B*((2*R)^3*(Real.pi*4/3)) := h
    _ ≤ B*((2*R)^3*8) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpi (by positivity)) hB
    _ = _ := by ring

theorem compactOrbitalDensity_jets_bounded {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ u v k, k ≤ 4 →
      (∀ x, ‖iteratedFDeriv ℝ k (compactOrbitalDensity freq R u v) x‖ ≤ B) ∧
      (∫ x, ‖iteratedFDeriv ℝ k (compactOrbitalDensity freq R u v) x‖) ≤ 64*B*R^3 := by
  obtain ⟨A,hA,ha⟩ := continuumLocalizedMode_jets_bounded hfreq
  obtain ⟨C,hC,hc⟩ := orbitalCutoff_jets_bounded
  let B := 16*C*(16*A*A)+1
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hB : 1 ≤ B := by
    dsimp [B]
    have hn : 0 ≤ 16*C*(16*A*A) := by positivity
    linarith
  refine ⟨B,hB,fun R hR u v k hk => ?_⟩
  have hpair (j : ℕ) (hj : j ≤ 4) (x : Position) :
      ‖iteratedFDeriv ℝ j (fun y => continuumLocalizedMode freq u y*continuumLocalizedMode freq v y) x‖ ≤
        16*A*A :=
    fourJet_mul ((continuumLocalizedMode_C7 freq u).of_le (by norm_num))
      ((continuumLocalizedMode_C7 freq v).of_le (by norm_num)) hA0 hA0 (ha u) (ha v) hj x
  have hb (x : Position) : ‖iteratedFDeriv ℝ k (compactOrbitalDensity freq R u v) x‖ ≤ B := by
    exact (fourJet_mul ((orbitalCutoff_smooth R u).of_le (by simp))
      (((continuumLocalizedMode_C7 freq u).of_le (by norm_num)).mul
        ((continuumLocalizedMode_C7 freq v).of_le (by norm_num))) hC0 (by positivity)
      (hc R hR u) hpair hk x).trans (by dsimp [B]; linarith)
  refine ⟨hb,?_⟩
  apply ball_supported_jet_integral (by linarith) (by linarith) u _ hb
  exact (tsupport_iteratedFDeriv_subset k).trans
    (compactOrbitalDensity_support freq (by linarith) u v)

end ContinuumCoulomb

end

end OAI
