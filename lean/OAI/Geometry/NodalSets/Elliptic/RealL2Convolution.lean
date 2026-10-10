import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import OAI.Geometry.NodalSets.Elliptic.RealL2PairingRepresentatives
import OAI.Geometry.NodalSets.Elliptic.RealL2SmoothTesting
import OAI.Geometry.NodalSets.Elliptic.RealL2TranslationContinuity
import OAI.Geometry.NodalSets.Elliptic.RealWeakConvolution

namespace OAI

namespace Yau
open MeasureTheory Set Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology
noncomputable section

def realL2Convolution {n : ℕ} (k : Coord n → ℝ) (U : RealEuclideanL2 n) :
    RealEuclideanL2 n := ∫ t, k t • realL2Translate (-t) U

theorem realL2Convolution_integrable {n : ℕ} (k : Coord n → ℝ)
    (hk : Continuous k) (hc : HasCompactSupport k) (U : RealEuclideanL2 n) :
    Integrable (fun t ↦ k t • realL2Translate (-t) U) :=
  (hk.smul ((realL2Translate_continuous U).comp continuous_neg)).integrable_of_hasCompactSupport
    (hc.smul_right)

theorem real_convolution_test_pairing {n : ℕ} (u k phi : Coord n → ℝ)
    (hu : Integrable u) (hk : Integrable k) (hp : Continuous phi)
    (hc : HasCompactSupport phi) :
    (∫ x, (u ⋆ k) x * phi x) = ∫ t, k t * ∫ x, u (x-t)*phi x := by
  obtain ⟨B,_,hb⟩ := (hc.isCompact_range hp).isBounded.exists_pos_norm_le
  have hi : Integrable (fun z : Coord n × Coord n ↦ (k z.2 * u (z.1-z.2))*phi z.1)
      (volume.prod volume) :=
    (hk.convolution_integrand (lsmul ℝ ℝ) hu).mul_bdd
      (hp.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z ↦ hb _ (mem_range_self z.1)))
  calc
    _ = ∫ x, ∫ t, (k t*u (x-t))*phi x := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [convolution_lsmul_swap, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t ↦ by ring)
    _ = ∫ t, ∫ x, (k t*u (x-t))*phi x := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x ↦ by ring)

theorem realL2Convolution_smooth_pairing {n : ℕ} (u k phi : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hk : Continuous k)
    (hkc : HasCompactSupport k) (hp : ContDiff ℝ ∞ phi) (hpc : HasCompactSupport phi) :
    inner ℝ (realL2Convolution k (hum.toLp u))
      ((real_compact_continuous_memLp phi hp.continuous hpc).toLp phi) =
      ∫ x, (u ⋆ k) x * phi x := by
  let P := (real_compact_continuous_memLp phi hp.continuous hpc).toLp phi
  rw [real_convolution_test_pairing u k phi hu
    (hk.integrable_of_hasCompactSupport hkc) hp.continuous hpc]
  change inner ℝ (∫ t, k t • realL2Translate (-t) (hum.toLp u)) P = _
  rw [real_inner_comm, ← integral_inner (realL2Convolution_integrable k hk hkc _)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [inner_smul_right, real_inner_comm]
  have ht : (realL2Translate (-t) (hum.toLp u) : Coord n → ℝ) =ᵐ[volume]
      (fun x ↦ u (x-t)) := by
    have he := (measurePreserving_add_right (G := Coord n) volume (-t)).quasiMeasurePreserving.ae_eq_comp
      hum.coeFn_toLp
    simpa only [sub_eq_add_neg, Function.comp_def] using (realL2Translate_ae (-t) (hum.toLp u)).trans he
  rw [(real_L2_inner_reps _ P _ phi ht
    (real_compact_continuous_memLp phi hp.continuous hpc).coeFn_toLp).2]

theorem real_L2_eq_of_smooth_pairings {n : ℕ} (U V : RealEuclideanL2 n)
    (he : ∀ phi : Coord n → ℝ, ∀ hp : ContDiff ℝ ∞ phi, ∀ hc : HasCompactSupport phi,
      inner ℝ U ((real_compact_continuous_memLp phi hp.continuous hc).toLp phi) =
      inner ℝ V ((real_compact_continuous_memLp phi hp.continuous hc).toLp phi)) : U=V := by
  have hclosed : IsClosed {W : RealEuclideanL2 n | inner ℝ U W=inner ℝ V W} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hsub : {W : RealEuclideanL2 n | ∃ phi : Coord n → ℝ,
      (W : Coord n → ℝ) =ᵐ[volume] phi ∧ HasCompactSupport phi ∧ ContDiff ℝ ∞ phi} ⊆
      {W : RealEuclideanL2 n | inner ℝ U W=inner ℝ V W} := by
    rintro W ⟨phi,hw,hc,hp⟩
    have hm := real_compact_continuous_memLp phi hp.continuous hc
    have hW : W=hm.toLp phi := Lp.ext (hw.trans hm.coeFn_toLp.symm)
    change inner ℝ U W=inner ℝ V W
    simpa only [hW] using he phi hp hc
  apply ext_inner_right ℝ
  intro W
  apply closure_minimal hsub hclosed
  exact (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Coord n))) (F := ℝ)
    (by norm_num : (2:ENNReal) ≠ ⊤)) W

theorem realL2Convolution_eq_toLp {n : ℕ} (u k : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hm : MemLp (u ⋆ k) 2 volume) :
    realL2Convolution k (hum.toLp u) = hm.toLp (u ⋆ k) := by
  apply real_L2_eq_of_smooth_pairings
  intro phi hp hc
  rw [realL2Convolution_smooth_pairing u k phi hu hum hk.continuous hkc hp hc,
    real_toLp_inner]

theorem realL2Convolution_normed_tendsto {n : ℕ}
    (b : ℕ → ContDiffBump (0 : Coord n))
    (hb : Tendsto (fun m ↦ (b m).rOut) atTop (𝓝 0)) (U : RealEuclideanL2 n) :
    Tendsto (fun m ↦ realL2Convolution ((b m).normed volume) U) atTop (𝓝 U) := by
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Coord n))) hb (realL2Translate_continuous U) (0 : Coord n)
  simpa only [convolution_def, lsmul_apply, zero_sub, realL2Translate_zero,
    realL2Convolution] using ht

end
end Yau

end OAI
