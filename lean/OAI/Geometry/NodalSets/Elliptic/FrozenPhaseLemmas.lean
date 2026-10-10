import OAI.Geometry.NodalSets.Elliptic.PhaseBounds

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set Metric
open scoped ContDiff

def frozenPhaseCovector (l k : Coord →L[ℝ] ℝ) : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp l + Complex.I • Complex.ofRealCLM.comp k

lemma frozenPhaseCovector_apply (l k : Coord →L[ℝ] ℝ) (v : Coord) :
    frozenPhaseCovector l k v = (l v:ℂ)+Complex.I*(k v:ℂ) := rfl

lemma frozenPhaseCovector_sub_le (l l' k : Coord →L[ℝ] ℝ) :
    ‖frozenPhaseCovector l k-frozenPhaseCovector l' k‖ ≤ ‖l-l'‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simp only [sub_apply,frozenPhaseCovector_apply]
  rw [show (l v:ℂ)+Complex.I*(k v:ℂ)-((l' v:ℂ)+Complex.I*(k v:ℂ)) =
    ((l-l') v:ℂ) by simp]
  rw [Complex.norm_real]
  exact (l-l').le_opNorm v

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_frozen_phase_gradient (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) :
    ∃ delta > 0, ∃ C > 0, ∀ t x z,
      ‖x-y t.1‖ ≤ delta → ‖z-y t.1‖ ≤ delta →
      ‖fderiv ℝ (b.phase t) z -
        frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))‖ ≤
        C*(‖z-y t.1‖+‖x-y t.1‖) := by
  obtain ⟨delta,hd,Cp,hCp,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy 2
  obtain ⟨Cs,hCs,hSb⟩ := compact_moving_derivative_bound S hS y hy delta 2
  refine ⟨delta,hd,Cp+Cs,by positivity,?_⟩
  intro t x z hx hz
  have hphi := norm_sub_le_on_closedBall (fderiv ℝ (b.phase t)) (y t.1) delta Cp hCp.le
    (fun v hv ↦ (((hb t v hv).2.1.fderiv_right (by simp)) :
      ContDiffAt ℝ ∞ (fderiv ℝ (b.phase t)) v).differentiableAt (by simp))
    (fun v hv ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact (hb t v hv).2.2.2.1 2 le_rfl) hd.le z hz
  have henv := norm_sub_le_on_closedBall (fderiv ℝ S) (y t.1) delta Cs hCs.le
    (fun _ _ ↦ ((hS.fderiv_right (by simp)) : ContDiff ℝ ∞ (fderiv ℝ S)).differentiable (by simp) _)
    (fun v hv ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact hSb t.1 v hv) hd.le x hx
  have he : fderiv ℝ (b.phase t) (y t.1) =
      frozenPhaseCovector (fderiv ℝ S (y t.1)) (g (y t.1) (d.q t.1 t.2)) := by
    ext v
    rw [b.phase_first hp hp0,metricGradient_pair g S _ (hp _) v]
    rfl
  have hc := frozenPhaseCovector_sub_le (fderiv ℝ S (y t.1)) (fderiv ℝ S x)
    (g (y t.1) (d.q t.1 t.2))
  rw [norm_sub_rev] at henv
  rw [← he] at hc
  exact (norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ (b.phase t) (y t.1)) _).trans
    ((add_le_add hphi (hc.trans henv)).trans (by nlinarith [norm_nonneg (z-y t.1),norm_nonneg (x-y t.1)]))

theorem uniform_real_phase_value_bound (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) :
    ∃ delta > 0, ∃ C > 0, ∀ t x, ‖x-y t.1‖ ≤ delta →
      |(b.phase t x).re-S x| ≤ C*‖x-y t.1‖^2 := by
  obtain ⟨delta,hd,Cp,hCp,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy 2
  obtain ⟨Cs,hCs,hSb⟩ := compact_moving_derivative_bound S hS y hy delta 2
  have hrp (t : T × Fin 3) (x : Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (hb t x hx).2.1
  have hsecond (t : T × Fin 3) (x : Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ‖iteratedFDeriv ℝ 2 (b.realDefect t) x‖ ≤ Cp+Cs := by
    change ‖iteratedFDeriv ℝ 2 ((fun z ↦ (b.phase t z).re)-S) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply
      ((hrp t x hx).of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (hS.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))]
    exact (norm_sub_le _ _).trans (add_le_add
      ((realPart_iterated_norm_le _ _ (hb t x hx).2.1 2).trans ((hb t x hx).2.2.2.1 2 le_rfl)) (hSb t.1 x hx))
  refine ⟨delta,hd,Cp+Cs,by positivity,?_⟩
  intro t x hx
  have hq := first_order_remainder_bound (b.realDefect t) (y t.1) delta (Cp+Cs)
    (by positivity) (fun z hz ↦ (hrp t z hz).sub hS.contDiffAt)
    (fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact hsecond t z hz) x hx
  rw [b.real_defect_first hp hS hp0] at hq
  have hc : b.realDefect t (y t.1) = 0 := by simp [realDefect,b.phase_center]
  rw [hc] at hq
  simpa [realDefect] using hq

end TripleSourceWaveData

end Yau.Geometry

end

end OAI
