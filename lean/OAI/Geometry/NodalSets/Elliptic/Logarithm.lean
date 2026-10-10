import OAI.Geometry.NodalSets.Elliptic.AmplitudeBounds
import OAI.Geometry.NodalSets.Waves.WaveGerm

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

def normalizedLogJet (N : ℝ) (V : Coord → ℂ) (x v : Coord) : ℂ :=
  (N:ℂ)⁻¹ * (fderiv ℝ V x v / V x)

lemma amplitude_exp_log_jet (a phi V : Coord → ℂ) (N : ℝ) (hN : N ≠ 0)
    (x : Coord) (ha : DifferentiableAt ℝ a x) (hp : DifferentiableAt ℝ phi x)
    (hn : a x ≠ 0)
    (he : V =ᶠ[𝓝 x] (fun z ↦ a z * Complex.exp ((N:ℂ)*phi z))) (v : Coord) :
    normalizedLogJet N V x v = fderiv ℝ phi x v + (N:ℂ)⁻¹*(fderiv ℝ a x v/a x) := by
  have hd := ha.hasFDerivAt.mul ((hp.hasFDerivAt.const_mul (N:ℂ)).cexp)
  change HasFDerivAt (fun z ↦ a z * Complex.exp ((N:ℂ)*phi z)) _ x at hd
  have hnc : (N:ℂ) ≠ 0 := by exact_mod_cast hN
  unfold normalizedLogJet
  rw [he.fderiv_eq,he.self_of_nhds,hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  field_simp [hn,Complex.exp_ne_zero,hnc]

lemma log_amplitude_correction_bound (a da : ℂ) (N C : ℝ) (hN : 0 < N)
    (hC : 0 ≤ C) (ha : (1/2:ℝ) ≤ ‖a‖) (hd : ‖da‖ ≤ C) :
    ‖(N:ℂ)⁻¹*(da/a)‖ ≤ 2*C/N := by
  rw [norm_mul,norm_inv,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  have hb : ‖da‖ / ‖a‖ ≤ 2*C := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  calc
    N⁻¹*(‖da‖/‖a‖) ≤ N⁻¹*(2*C) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hN.le)
    _ = _ := by ring

variable {T : Type*} [TopologicalSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma wave_germ_of_small_inverse (N : ℝ) (hN : 0 < N) (t : T × Fin 3)
    (x : Coord) (hx : x ∈ (b.F t).target)
    (hsmall : ‖(b.F t).symm x‖ < N^(-1/3:ℝ)) :
    b.wave N t =ᶠ[𝓝 x]
      (fun z ↦ b.amplitude N t z * Complex.exp ((N:ℂ)*b.phase t z)) := by
  have hInv := ((b.chart_domain t).2.2.contDiffAt ((b.F t).open_target.mem_nhds hx)).continuousAt
  have hnear : ∀ᶠ z in 𝓝 x, ‖(b.F t).symm z‖ < N^(-1/3:ℝ) :=
    hInv.norm.eventually (gt_mem_nhds hsmall)
  filter_upwards [chartPushforward_eventually (b.F t) (coordinateWave b.phi b.A J N t) x hx,hnear] with z hz hs
  change chartPushforward (b.F t) (coordinateWave b.phi b.A J N t) z = _
  rw [hz]
  have hc := Yau.Waves.scaledCutoff_eq_one hN (0:Coord) ((b.F t).symm z) (by simpa using hs.le)
  change Yau.Waves.scaledCutoff N (0:Coord) ((b.F t).symm z) • _ = _
  rw [hc,one_smul]
  rfl

lemma wave_log_jet (N : ℝ) (hN : 0 < N) (t : T × Fin 3) (x v : Coord)
    (hx : x ∈ (b.F t).target) (hsmall : ‖(b.F t).symm x‖ < N^(-1/3:ℝ))
    (ha : b.amplitude N t x ≠ 0) :
    b.wave N t x ≠ 0 ∧ normalizedLogJet N (b.wave N t) x v =
      fderiv ℝ (b.phase t) x v + (N:ℂ)⁻¹*(fderiv ℝ (b.amplitude N t) x v/b.amplitude N t x) := by
  have hInv := (b.chart_domain t).2.2.contDiffAt ((b.F t).open_target.mem_nhds hx)
  have hag := (finiteAmplitude_contDiff (fun j ↦ b.A j t) J N).contDiffAt.comp x hInv
  have hpg := (reval_contDiff (b.phi t)).contDiffAt.comp x hInv
  have he := b.wave_germ_of_small_inverse N hN t x hx hsmall
  refine ⟨?_,amplitude_exp_log_jet _ _ _ N hN.ne' x
    (hag.differentiableAt (by simp)) (hpg.differentiableAt (by simp)) ha he v⟩
  rw [he.self_of_nhds]
  exact mul_ne_zero ha (Complex.exp_ne_zero _)

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
