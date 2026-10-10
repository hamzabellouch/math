import OAI.Geometry.RCD.Heat.HeatDaviesKernel
import OAI.Geometry.RCD.Coordinates.HeatNormalizationVolume
import OAI.Geometry.RCD.Heat.GaussianUpperAlgebra

namespace OAI

/-! # The sharp Gaussian upper bound for the canonical kernel

This proves the upper half of Jiang--Li--Zhang (2016), Theorem 1.2 and
Corollary 1.2, for the actual RCD heat kernel. The constants depend on
dimension, curvature and epsilon. No Gaussian assumption is used.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_gaussian_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 ≤ C₂ ∧ ∀ (t : ℝ), 0 < t → ∀ x y : X,
      hX.canonicalHeatKernel hn p t x y ≤
        C₁/(hausdorff n X).real (ball y (Real.sqrt t))*
          Real.exp (-(dist x y)^2/((4+ε)*t)+C₂*t) := by
  obtain ⟨C,hC,hbound⟩ := hX.canonicalHeatKernel_davies_bound hn p
  let N : ℝ := n
  let B₀ := 2*(N+1)^2*((4+ε)/ε)+25*N^2/4
  let B₁ := 32*N^2*((4+ε)/ε)+1
  let C₁ := C^2*4^n*Real.exp B₀
  let C₂ := B₁*|K|
  have hCpos : 0 < C := by linarith
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂,B₁]; positivity
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro t ht x y
  let μ := hausdorff n X
  let d := dist x y
  let T := Real.sqrt t
  let r := gaussianRadius K t
  let z := d/T
  let u := Real.sqrt (|K| *t)
  let L := N*z+5*N*u+4*N*Real.sqrt |K| *d
  let A := 4^n*Real.exp L
  let E := -(d/t)*d/2+(d/t)*r+(d/t)^2*t/4
  have hd : 0 ≤ d := dist_nonneg
  have hT : 0 < T := Real.sqrt_pos.mpr ht
  have hTsq : T^2 = t := Real.sq_sqrt ht.le
  have hr : 0 < r := gaussianRadius_pos K ht
  have hA : 0 < A := by dsimp only [A]; positivity
  have hvol (q : X) (hq : dist q y ≤ d) : μ.real (ball y T) ≤ A*μ.real (ball q r) :=
    hX.gaussian_normalization_volume hn y q ht hd hq
  have hVpos (q : X) {s : ℝ} (hs : 0 < s) : 0 < μ.real (ball q s) :=
    ENNReal.toReal_pos (hX.fullSupport q s hs).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hnorm := inv_sqrt_product_le_of_volume (hVpos y hT) (hVpos x hr) (hVpos y hr)
    hA.le (hvol x le_rfl) (hvol y (by simpa only [dist_self] using hd))
  have hk := hbound x y (d/t) r t (div_nonneg hd ht.le) hr
    (gaussianRadius_curvature K ht) (gaussianRadius_sq_lt K ht)
  have hcoef : C^2/(Real.sqrt (μ.real (ball x r))*Real.sqrt (μ.real (ball y r))) ≤
      C^2*(A/μ.real (ball y T)) := by
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hnorm (sq_nonneg C)
  have hraw : hX.canonicalHeatKernel hn p t x y ≤
      (C^2*4^n/μ.real (ball y T))*Real.exp (L+E) := by
    calc
      _ ≤ C^2*(A/μ.real (ball y T))*Real.exp E :=
        hk.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos E).le)
      _ = _ := by dsimp only [A]; rw [Real.exp_add L E]; ring
  have hz2 : z^2 = d^2/t := by dsimp only [z]; rw [div_pow,hTsq]
  have hu2 : u^2 = |K| *t := Real.sq_sqrt (mul_nonneg (abs_nonneg K) ht.le)
  have huz : Real.sqrt |K| *d = u*z := by
    dsimp only [u,z,T]
    rw [Real.sqrt_mul (abs_nonneg K)]
    field_simp
  have hdr : (d/t)*r ≤ z := by
    calc
      _ ≤ (d/t)*T := mul_le_mul_of_nonneg_left
        ((gaussianRadius_le K ht).trans (by dsimp only [T]; linarith [Real.sqrt_nonneg t]))
        (div_nonneg hd ht.le)
      _ = z := by dsimp only [z]; rw [← hTsq]; field_simp
  have hE : E = -z^2/4+(d/t)*r := by
    dsimp only [E]
    rw [hz2]
    field_simp
    ring
  have hL : 4*N*Real.sqrt |K| *d = 4*N*u*z := by
    rw [mul_assoc (4*N),huz]
    ring
  have hexp : L+E ≤ -d^2/((4+ε)*t)+B₀+C₂*t := by
    calc
      _ ≤ -z^2/4+(N+1+4*N*u)*z+5*N*u := by
        dsimp only [L]
        rw [hL,hE]
        nlinarith only [hdr]
      _ ≤ -z^2/(4+ε)+(2*(N+1)^2*((4+ε)/ε)+25*N^2/4)+
          (32*N^2*((4+ε)/ε)+1)*u^2 := gaussian_upper_absorb N u z hε
      _ = _ := by
        rw [hz2,hu2]
        dsimp only [B₀,C₂,B₁]
        rw [← neg_div,div_div,mul_comm t (4+ε)]
        ring
  calc
    _ ≤ (C^2*4^n/μ.real (ball y T))*Real.exp (-d^2/((4+ε)*t)+B₀+C₂*t) :=
      hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
    _ = _ := by
      change _ = (C^2*4^n*Real.exp B₀)/μ.real (ball y T)*Real.exp (-d^2/((4+ε)*t)+C₂*t)
      rw [show -d^2/((4+ε)*t)+B₀+C₂*t = B₀+(-d^2/((4+ε)*t)+C₂*t) by ring,Real.exp_add]
      ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
