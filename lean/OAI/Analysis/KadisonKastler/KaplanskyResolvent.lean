import OAI.Analysis.KadisonKastler.KaplanskySelfAdjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Complex.Spectrum

namespace OAI

/-! # Bounded resolvents for the Kaplansky argument

Off-real resolvents are uniformly bounded on all self-adjoint operators.
Their strong continuity therefore does not require a norm bound on the
approximating self-adjoint net. This is the bounded-transform step used in
Kaplansky's proof (Pacific J. Math. 1 (1951), Lemma 4, pp.229--230).
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem spectral_im_eq_zero {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {w : ℂ} (hw : w ∈ spectrum ℂ a) : w.im = 0 := by
  have h := SpectrumRestricts.real_iff.mp ha.spectrumRestricts w hw
  simpa using congrArg Complex.im h

/-- Every nonreal point belongs to the resolvent set of a self-adjoint operator. -/
theorem nonreal_mem_resolventSet {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet ℂ a := by
  classical
  change IsUnit (algebraMap ℂ (H →L[ℂ] H) z - a)
  by_contra hs
  exact hz (spectral_im_eq_zero ha hs)

theorem resolvent_eq_cfc_of_selfAdjoint {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) :
    resolvent a z = cfc (fun w : ℂ => (z - w)⁻¹) a := by
  have hn : ∀ w ∈ spectrum ℂ a, z - w ≠ 0 := by
    intro w hw he
    have he' : z = w := sub_eq_zero.mp he
    apply hz
    rw [he']
    exact spectral_im_eq_zero ha hw
  rw [cfc_inv (fun w : ℂ => z - w) a hn
    ((continuous_const.sub continuous_id).continuousOn) ha.isStarNormal]
  rw [cfc_sub (fun _ : ℂ => z) (fun w : ℂ => w) a,
    cfc_const z a ha.isStarNormal, cfc_id' ℂ a ha.isStarNormal]
  rfl

/-- The resolvent norm bound is independent of the self-adjoint operator. -/
theorem norm_resolvent_le_inv_abs_im {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) : ‖resolvent a z‖ ≤ |z.im|⁻¹ := by
  rw [resolvent_eq_cfc_of_selfAdjoint ha hz]
  apply norm_cfc_le (inv_nonneg.mpr (abs_nonneg _))
  intro w hw
  have hdist : |z.im| ≤ ‖z - w‖ := by
    simpa only [Complex.sub_im, spectral_im_eq_zero ha hw, sub_zero]
      using Complex.abs_im_le_norm (z - w)
  rw [norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le (abs_pos.mpr hz) hdist) (abs_pos.mpr hz)).mpr hdist

/-- Strong continuity of off-real resolvents, including unbounded nets. -/
theorem tendsto_resolvent_of_selfAdjoint_strong
    {ι : Type*} {l : Filter ι} {a : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (ha : ∀ i, IsSelfAdjoint (a i)) (hT : IsSelfAdjoint T)
    (hlim : ∀ x, Tendsto (fun i => a i x) l (𝓝 (T x)))
    {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    Tendsto (fun i => resolvent (a i) z x) l (𝓝 (resolvent T z x)) := by
  have hbound (i) : ‖resolvent (a i) z x - resolvent T z x‖ ≤
      |z.im|⁻¹ * ‖a i (resolvent T z x) - T (resolvent T z x)‖ := by
    have he := spectrum.resolvent_sub_resolvent
      (nonreal_mem_resolventSet (ha i) hz) (nonreal_mem_resolventSet hT hz)
    have hev := congrArg (fun b : H →L[ℂ] H => b x) he
    simp only [sub_apply, mul_apply_eq_comp] at hev
    rw [hev]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_resolvent_le_inv_abs_im (ha i) hz) (norm_nonneg _))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa using ((hlim (resolvent T z x)).sub_const (T (resolvent T z x))).norm.const_mul
    (|z.im|⁻¹)

end

end KadisonKastler

end OAI
