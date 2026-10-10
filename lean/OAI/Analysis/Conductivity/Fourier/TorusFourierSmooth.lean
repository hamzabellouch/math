import Mathlib
import OAI.Analysis.Conductivity.Variational.LocalSmoothSeries
import OAI.Analysis.Conductivity.Fourier.TorusFlatMode

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def flatFourier (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑' h, a h*flatPhaseMode s h (phase h) x

lemma axial_halfspace_open (δ : ℝ) : IsOpen {x : Fin 3 → ℝ | δ<x 0} :=
  isOpen_lt continuous_const (continuous_apply 0)

lemma axial_halfspace_connected (δ : ℝ) : IsPreconnected {x : Fin 3 → ℝ | δ<x 0} :=
  (convex_halfSpace_gt (𝕜 := ℝ) (f := fun x : Fin 3 → ℝ => x 0)
    ⟨fun _ _ => rfl,fun _ _ => rfl⟩ δ).isPreconnected

lemma weighted_phase_halfspace_bound {s : Fin 3 → ℝ} {a phase : (Fin 2 → ℤ) → ℝ}
    {B δ : ℝ} (ha : ∀ h, |a h|≤B) (n : ℕ) (h : Fin 2 → ℤ)
    {x : Fin 3 → ℝ} (hx : δ≤x 0) :
    ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x‖≤
      B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) := by
  apply (weighted_phase_iterated_bound (phase h) (a h) n x).trans
  have hrate : 0≤torusRate s h := sqrt_nonneg _
  have hexp : exp (-torusRate s h*x 0)≤exp (-δ*torusRate s h) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx hrate]
  have hsize := torusSize_nonneg h
  exact mul_le_mul (ha h) (mul_le_mul_of_nonneg_left hexp (by positivity))
    (by positivity) ((abs_nonneg _).trans (ha h))

lemma flatFourier_smooth_halfspace {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B δ : ℝ} (ha : ∀ h, |a h|≤B) (hδ : 0<δ) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatFourier s a phase) {x | δ<x 0} := by
  apply local_smooth_tsum (axial_halfspace_open δ) (axial_halfspace_connected δ)
    (fun h => contDiff_const.mul (flatPhaseMode_smooth s h (phase h)))
    (fun n h => B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)))
  · intro n
    exact (flatMode_derivative_summable hs n hδ).mul_left B
  · intro n h x hx
    exact weighted_phase_halfspace_bound ha n h hx.le

lemma flatFourier_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h, |a h|≤B) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatFourier s a phase) {x | 0<x 0} := by
  apply (axial_halfspace_open 0).contDiffOn_iff.mpr
  intro x hx
  change 0<x 0 at hx
  exact (flatFourier_smooth_halfspace hs ha (show 0<x 0/2 by linarith)).contDiffAt
    ((axial_halfspace_open (x 0/2)).mem_nhds (show x 0/2<x 0 by linarith))

lemma flatFourier_iterated {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h, |a h|≤B)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    iteratedFDeriv ℝ n (flatFourier s a phase) x =
      ∑' h, iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x := by
  apply local_iteratedFDeriv_tsum (axial_halfspace_open (x 0/2)) (axial_halfspace_connected (x 0/2))
    (fun h => contDiff_const.mul (flatPhaseMode_smooth s h (phase h)))
    (fun n h => B*((torusRate s h+torusSize h)^n*exp (-(x 0/2)*torusRate s h)))
  · intro n
    exact (flatMode_derivative_summable hs n (by linarith)).mul_left B
  · intro n h y hy
    exact weighted_phase_halfspace_bound ha n h hy.le
  · change x 0/2<x 0
    linarith

lemma flatFourier_iterated_norm {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B δ : ℝ} (ha : ∀ h, |a h|≤B) (hδ : 0<δ)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : δ≤x 0) :
    ‖iteratedFDeriv ℝ n (flatFourier s a phase) x‖≤
      ∑' h, B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) := by
  rw [flatFourier_iterated hs ha n (hδ.trans_le hx)]
  have hb := (flatMode_derivative_summable hs n hδ).mul_left B
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x‖) := Summable.of_nonneg_of_le (fun h => norm_nonneg _)
    (fun h => weighted_phase_halfspace_bound ha n h hx) hb
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun h => weighted_phase_halfspace_bound ha n h hx) hb)

end ScalarConductivity

end

end OAI
