import OAI.Geometry.NodalSets.Elliptic.PhaseActualJet
import OAI.Geometry.NodalSets.Waves.TripleSourceWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

def phase (t : T × Fin 3) : Coord → ℂ := reval (b.phi t) ∘ (b.F t).symm

def amplitude (N : ℝ) (t : T × Fin 3) : Coord → ℂ :=
  finiteAmplitude (fun j ↦ b.A j t) J N ∘ (b.F t).symm

def wave (N : ℝ) (t : T × Fin 3) : Coord → ℂ :=
  chartPushforward (b.F t) (coordinateWave b.phi b.A J N t)

lemma zero_mem_source (t : T × Fin 3) : (0:Coord) ∈ (b.F t).source := by
  rw [(b.chart_domain t).1]
  simpa using b.sourceRadius_pos

lemma chart_zero (t : T × Fin 3) : b.F t 0 = y t.1 := by
  rw [b.chart_eq]
  exact quadraticChartMap_zero _ _ _

lemma center_mem_target (t : T × Fin 3) : y t.1 ∈ (b.F t).target := by
  rw [← b.chart_zero t]
  exact (b.F t).map_source (b.zero_mem_source t)

lemma inverse_center (t : T × Fin 3) : (b.F t).symm (y t.1) = 0 := by
  rw [← b.chart_zero t]
  exact (b.F t).left_inv (b.zero_mem_source t)

lemma inverse_derivative (t : T × Fin 3) :
    HasFDerivAt ((b.F t).symm : Coord → Coord) (d.frame t).symm.toContinuousLinearMap (y t.1) := by
  apply (b.F t).hasFDerivAt_symm (b.center_mem_target t)
  rw [b.inverse_center,b.chart_eq]
  exact quadraticChartMap_deriv_zero _ _ _

lemma phase_smooth_at_center (t : T × Fin 3) : ContDiffAt ℝ ∞ (b.phase t) (y t.1) :=
  (reval_contDiff _).contDiffAt.comp _ ((b.chart_domain t).2.2.contDiffAt
    ((b.F t).open_target.mem_nhds (b.center_mem_target t)))

lemma phase_center (t : T × Fin 3) : b.phase t (y t.1) = (S (y t.1):ℂ) := by
  unfold phase
  simp only [Function.comp_apply,b.inverse_center]
  exact retained_phase_value _ _ _ _ (b.jets.phase_retained t 0 (by omega))

lemma amplitude_center (N : ℝ) (t : T × Fin 3) : b.amplitude N t (y t.1) = 1 := by
  unfold amplitude
  simp only [Function.comp_apply,b.inverse_center]
  exact finiteAmplitude_center _ _ _ (fun j ↦ b.jets.amplitude_value j t)

lemma wave_center (N : ℝ) (hN : 0 < N) (t : T × Fin 3) :
    b.wave N t (y t.1) = Complex.exp ((N:ℂ)*(S (y t.1):ℂ)) := by
  rw [wave,← b.chart_zero t,chartPushforward_pullback _ _ _ (b.zero_mem_source t)]
  have hc : Yau.Waves.scaledCutoff N (0:Coord) 0 = 1 :=
    Yau.Waves.scaledCutoff_eq_one hN 0 0 (by simp; positivity)
  have hphi := retained_phase_value _ _ _ _ (b.jets.phase_retained t 0 (by omega))
  simp only [coordinateWave,hc,one_smul,waveExp,hphi,
    finiteAmplitude_center _ J N (fun j ↦ b.jets.amplitude_value j t),one_mul]
  rw [b.chart_zero]

lemma wave_ne_zero (N : ℝ) (hN : 0 < N) (t : T × Fin 3) : b.wave N t ≠ 0 := by
  intro h
  have hh := congrFun h (y t.1)
  rw [b.wave_center N hN t] at hh
  exact Complex.exp_ne_zero _ hh

lemma phase_first (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : Coord) :
    fderiv ℝ (b.phase t) (y t.1) v =
      (g (y t.1) (metricGradient g S (y t.1)) v:ℂ) +
        Complex.I * (g (y t.1) (d.q t.1 t.2) v:ℂ) := by
  have hder := ((reval_contDiff (b.phi t)).differentiable (by simp) 0).hasFDerivAt
  have he := (b.inverse_derivative t)
  have hf : fderiv ℝ (b.phase t) (y t.1) v =
      fderiv ℝ (reval (b.phi t)) 0 ((d.frame t).symm v) := by
    unfold phase
    rw [fderiv_comp _ (by rw [b.inverse_center]; exact hder.differentiableAt) he.differentiableAt,
      he.fderiv,b.inverse_center]
    rfl
  rw [hf,fderiv_reval]
  simp_rw [retained_phase_first _ _ _ _ (b.jets.phase_retained t 1 (by omega))]
  have hpair0 : g (y t.1) (metricGradient g S (y t.1)) v =
      sourceTripleAlpha g S y t * (d.frame t).symm v 0 := by
    have hframe : sourceTripleAlpha g S y t • d.frame t (Pi.single 0 1) = metricGradient g S (y t.1) :=
      d.frame_first (fun t ↦ hpos (y t)) hp0 t
    rw [← hframe]
    simp only [map_smul,smul_apply,smul_eq_mul]
    rw [frame_pair_coordinate (g (y t.1)) (d.frame t) (d.frame_orthonormal t)]
  have hpair1 : g (y t.1) (d.q t.1 t.2) v =
      sourceTripleBeta g S y t * (d.frame t).symm v 1 := by
    have hframe : sourceTripleBeta g S y t • d.frame t (Pi.single 1 1) = d.q t.1 t.2 :=
      d.frame_second (fun t ↦ hpos (y t)) hp0 t
    rw [← hframe]
    simp only [map_smul,smul_apply,smul_eq_mul]
    rw [frame_pair_coordinate (g (y t.1)) (d.frame t) (d.frame_orthonormal t)]
  rw [hpair0,hpair1]
  simp [normalFrameVector,Fin.sum_univ_succ]
  ring

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
