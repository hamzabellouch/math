import OAI.Geometry.NodalSets.Elliptic.QuadraticTaylorBound
import OAI.Geometry.NodalSets.Waves.WaveHessian

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma realPart_fderiv (f : Coord → ℂ) (x : Coord) (hf : DifferentiableAt ℝ f x) (v : Coord) :
    fderiv ℝ (fun z ↦ (f z).re) x v = (fderiv ℝ f x v).re := by
  change fderiv ℝ (Complex.reCLM ∘ f) x v = _
  rw [(Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

lemma realPart_iterated_norm_le (f : Coord → ℂ) (x : Coord)
    (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ (f z).re) x‖ ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  have he := Complex.reCLM.iteratedFDeriv_comp_left hf
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
  change iteratedFDeriv ℝ k (fun z ↦ (f z).re) x = _ at he
  rw [he]
  have hr : ‖Complex.reCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z ↦ by simpa using Complex.abs_re_le_norm z)
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hr (norm_nonneg (iteratedFDeriv ℝ k f x)))

variable {T : Type*} [TopologicalSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

def realDefect (t : T × Fin 3) (x : Coord) : ℝ := (b.phase t x).re-S x

def eta (_b : TripleSourceWaveData g w S y d m J K k0) (t : T × Fin 3) : ℝ := sourceDirectionEta (g (y t.1))
  (sourceHessian g S (y t.1)) (metricGradient g S (y t.1)) (d.q t.1 t.2)

lemma real_phase_first (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : Coord) :
    fderiv ℝ (fun z ↦ (b.phase t z).re) (y t.1) v = fderiv ℝ S (y t.1) v := by
  rw [realPart_fderiv _ _ ((b.phase_smooth_at_center t).differentiableAt (by simp)),
    b.phase_first hp hp0,metricGradient_pair g S _ (hp _) v]
  simp

lemma real_defect_first (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hS : ContDiff ℝ ∞ S) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) :
    fderiv ℝ (b.realDefect t) (y t.1) = 0 := by
  have hs : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) (y t.1) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (b.phase_smooth_at_center t)
  unfold realDefect
  rw [fderiv_fun_sub (hs.differentiableAt (by simp)) (hS.differentiable (by simp) _)]
  ext v
  simp only [sub_apply,zero_apply]
  rw [b.real_phase_first hp hp0]
  ring

lemma real_defect_second (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (u v : Coord) :
    fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) u v = -b.eta t*g (y t.1) u v := by
  have hphi : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) (y t.1) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (b.phase_smooth_at_center t)
  have hh := b.phase_hessian hg hs hp hS hp0 t u v
  simp only [sourceHessian_apply] at hh
  rw [b.real_phase_first hp hp0] at hh
  have hsub := iteratedFDeriv_sub_apply (i := 2)
    (hphi.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
    (hS.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
  have hv := congrArg (fun L : Coord [×2]→L[ℝ] ℝ ↦ L ![u,v]) hsub
  simp only [sub_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] at hv
  change fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) u v = _ at hv
  rw [hv]
  dsimp [eta]
  linarith

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
