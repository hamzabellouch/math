import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedDet
import OAI.Analysis.AffineBernstein.DualDetPhase

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualDetCompact
open Filter
open scoped Topology

lemma affineMaximal_dual_det_phase_bound {n : ℕ} {V Ω K : Set (Space n)}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (hKV : K ⊆ V) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hp : ∀ x ∈ V, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0)
    (hbd : ∀ x ∈ K, x ∉ Ω → dualCutoff u h x = 0)
    {γ M D : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hrad : ∀ x ∈ Ω, positionSquared x ≤ M)
    (hdepth : ∀ x ∈ Ω, -dualCutoff u h x ≤ D) {x : Space n} (hx : x ∈ Ω) :
    dualDetPhase u h γ x ≤ (2*(n:ℝ)*((n:ℝ)+2)/γ)^n * D^2 * Real.exp (γ*M/2) := by
  obtain ⟨y,hyK,hymax⟩ := hK.exists_isMaxOn ⟨x,hΩK hx⟩
    ((continuousOn_dualDetPhase hV hu hp h γ).mono hKV)
  have hxy : dualDetPhase u h γ x ≤ dualDetPhase u h γ y := hymax (hΩK hx)
  have hyp : 0 < dualDetPhase u h γ y :=
    (dualDetPhase_pos (hp x (hKV (hΩK hx))) (hneg x hx) γ).trans_le hxy
  have hy : y ∈ Ω := by
    by_contra hn
    have hz : dualDetPhase u h γ y = 0 := by simp [dualDetPhase,hbd y hyK hn]
    rw [hz] at hyp
    exact (lt_irrefl 0) hyp
  have hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) y := by
    filter_upwards [hΩ.mem_nhds hy] with z hz
    apply Real.exp_le_exp.mp
    rw [← dualDetPhase_eq_exp (hp z (hKV (hΩK hz))) (hneg z hz) γ,
      ← dualDetPhase_eq_exp (hp y (hKV hyK)) (hneg y hy) γ]
    exact hymax (hΩK hz)
  exact hxy.trans (dualDetPhase_peak_bound hΩ (hu.mono (hΩK.trans hKV))
    (fun z hz => hp z (hKV (hΩK hz))) hm h hneg hy hγ hM hD hsmall
    (hrad y hy) (hdepth y hy) hmax)

lemma positionSquared_eq_norm_sq {n : ℕ} (x : Space n) : positionSquared x = ‖x‖^2 := by
  simpa only [positionSquared,Real.norm_eq_abs,sq_abs] using (EuclideanSpace.norm_sq_eq x).symm

lemma dualHeight_zero {n : ℕ} (u : Space n → ℝ) : dualHeight u 0 = 0 := by
  simp [dualHeight,tangentHeight]

/-- Determinant lower estimate from the original PDE and the genuinely
geometric, all-base section modulus. The dual section is pulled back to
primal coordinates, avoiding any assumed Legendre-PDE regularity. -/
lemma affineMaximal_det_inverse_upper_of_modulus {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (hp : ∀ x ∈ O, (hessian u x).PosDef)
    (hm : AffineMaximalOn O u) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0:Space n) r ⊆ O) (b : ℝ → ℝ)
    (hb : 0 < b r) (hmod : HasLowerSectionModulus O u b) :
    ((hessian u 0).det)⁻¹ ≤
      (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * (b r/2)^2 *
        Real.exp (r^2/(4*(r^2+1))) / (b r/2)^(n+2) := by
  let h := b r/2
  let Ω := O ∩ (dualHeight u) ⁻¹' Iio h
  let K := Metric.closedBall (0:Space n) r ∩ (dualHeight u) ⁻¹' Iic h
  have hh : 0 < h := half_pos hb
  have h0 : (0:Space n) ∈ O := hball (Metric.mem_closedBall_self hr.le)
  have hc := (contDiffOn_dualHeight hO hu).continuousOn
  have hΩ : IsOpen Ω := hc.isOpen_inter_preimage hO isOpen_Iio
  have hΩr : Ω ⊆ Metric.ball 0 r := by
    intro x hx
    have hs : (0:Space n) ∈ tangentSection O u x (b r) := by
      refine ⟨h0,?_⟩
      have HH : dualHeight u x < h := hx.2
      change tangentHeight u x 0 < b r
      change dualHeight u x < b r
      exact HH.trans (by dsimp [h]; linarith)
    have H := hmod x hx.1 r hr hs
    simpa only [Metric.mem_ball,dist_comm] using H
  have hΩK : Ω ⊆ K := fun x hx => ⟨Metric.ball_subset_closedBall (hΩr hx),(show dualHeight u x < h from hx.2).le⟩
  have hKO : K ⊆ O := fun _ hx => hball hx.1
  have hK : IsCompact K := (isCompact_closedBall (0:Space n) r).of_isClosed_subset
    ((hc.mono hball).preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic) inter_subset_left
  have hneg : ∀ x ∈ Ω, dualCutoff u h x < 0 := fun _ hx => sub_neg.mpr hx.2
  have hbd : ∀ x ∈ K, x ∉ Ω → dualCutoff u h x = 0 := by
    intro x hx hn
    have hlo : h ≤ dualHeight u x := by
      by_contra nh
      exact hn ⟨hKO hx,lt_of_not_ge nh⟩
    exact sub_eq_zero.mpr (le_antisymm hx.2 hlo)
  have hdepth : ∀ x ∈ Ω, -dualCutoff u h x ≤ h := by
    intro x hx
    have H := tangentHeight_nonneg hO hcv hu hp hx.1 h0
    change 0 ≤ dualHeight u x at H
    dsimp [dualCutoff]
    linarith
  have hrad : ∀ x ∈ Ω, positionSquared x ≤ r^2 := by
    intro x hx
    rw [positionSquared_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (by have H := hΩr hx; rw [Metric.mem_ball,dist_zero_right] at H; exact H.le) 2
  let γ : ℝ := 1/(2*(r^2+1))
  have hden : 0 < 2*(r^2+1) := by positivity
  have hγ : 0 < γ := one_div_pos.mpr hden
  have hsmall : γ*r^2 ≤ 1/2 := by
    dsimp [γ]
    rw [one_div_mul_eq_div,div_le_iff₀ hden]
    linarith [sq_nonneg r]
  have h0Ω : (0:Space n) ∈ Ω := ⟨h0,by simpa only [dualHeight_zero,Set.mem_preimage,Set.mem_Iio] using hh⟩
  have H := affineMaximal_dual_det_phase_bound hO hΩ hK hΩK hKO hu hp
    (fun x hx => hm x hx.1) h hneg hbd hγ (sq_nonneg r) hh.le hsmall hrad hdepth h0Ω
  have he : γ*r^2/2 = r^2/(4*(r^2+1)) := by dsimp [γ]; field_simp; ring
  have hd : 2*(n:ℝ)*((n:ℝ)+2)/γ = 2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)) := by
    simp only [γ,div_eq_mul_inv,one_mul,inv_inv]
  rw [he,hd] at H
  have hz : dualDetPhase u h γ 0 = ((hessian u 0).det)⁻¹ * h^(n+2) := by
    simp [dualDetPhase,dualCutoff,dualHeight_zero,positionEnergy]
  rw [hz] at H
  exact (le_div_iff₀ (pow_pos hh _)).mpr H

end DualDetCompact


end
end AffineBernstein
end

end OAI
