import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.Contact.Inner

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma scalar_family_uniform_semiconvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    (a b K : ℝ) (hK : 0≤K) (L : ℝ≥0) :
    ∃ C>0,∀ p∈Kp,∀ S : Set E,Convex ℝ S → ∀ f:E → ℝ,
      LipschitzOnWith L f S → (∀ x∈S,f x∈Icc a b) →
      (∀ x∈S,∃ l:E →L[ℝ] ℝ,∀ y∈S,f x+l (y-x)-K*‖y-x‖^2≤f y) →
      ConvexOn ℝ S (fun x=>Φ (p,f x)+C/2*‖x‖^2) := by
  let dd := fun q:P×ℝ=>fderiv ℝ (fun s=>Φ (q.1,s)) q.2
  let hh := fun q:P×ℝ=>fderiv ℝ (fderiv ℝ (fun s=>Φ (q.1,s))) q.2
  have hdd : Continuous dd := continuous_iff_continuousAt.mpr (fun q=>
    (ContDiffAt.partial_snd_fderiv (f := fun p s=>Φ (p,s)) (hΦ.contDiffAt (x := q))).continuousAt)
  have hhh : Continuous hh := continuous_iff_continuousAt.mpr (fun q=>
    (ContDiffAt.partial_snd_fderiv_two (f := fun p s=>Φ (p,s)) (hΦ.contDiffAt (x := q))).continuousAt)
  obtain ⟨A0,hA0⟩ := (hKp.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn (f := dd) hdd.continuousOn
  obtain ⟨B0,hB0⟩ := (hKp.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn (f := hh) hhh.continuousOn
  let A := max A0 0
  let B := max B0 0
  have hA : 0≤A := le_max_right _ _
  have hB : 0≤B := le_max_right _ _
  let C := 2*(A*K+B*(L:ℝ)^2+1)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro p hp S hS f hlip hrange hs
  let φ := fun s=>Φ (p,s)
  have hφ : ContDiff ℝ 2 φ := (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply convexOn_of_quadratic_lower_supports hS (C/2)
  intro x hx
  obtain ⟨l,hl⟩ := hs x hx
  refine ⟨deriv φ (f x) • l,?_⟩
  intro y hy
  have H := first_order_remainder_le_of_hessian_bound (convex_Icc a b) hB
    (fun z hz=>hφ.contDiffAt) (fun z hz=>by exact (hB0 (p,z) ⟨hp,hz⟩).trans (le_max_left _ _))
    (hrange x hx) (hrange y hy)
  rw [fderiv_eq_deriv_mul] at H
  have Hlow := (abs_le.mp H).1
  have Hf := mul_le_mul_of_nonneg_left (hl y hy) ((hmono p hp).deriv_nonneg (x := f x))
  have Hlip := hlip.dist_le_mul y hy x hx
  rw [dist_eq_norm,dist_eq_norm] at Hlip
  have Hsq := sq_le_sq₀ (norm_nonneg (f y-f x)) (by positivity : 0≤(L:ℝ)*‖y-x‖) |>.mpr Hlip
  have HB := mul_le_mul_of_nonneg_left Hsq hB
  have HA : deriv φ (f x)≤A := by
    have hh0 := hA0 (p,f x) ⟨hp,hrange x hx⟩
    have hh1 : |deriv φ (f x)|≤A0 := by
      simpa only [dd,←norm_deriv_eq_norm_fderiv,Real.norm_eq_abs] using hh0
    exact (le_abs_self _).trans (hh1.trans (le_max_left _ _))
  have HK := mul_le_mul_of_nonneg_right HA (mul_nonneg hK (sq_nonneg ‖y-x‖))
  simp only [_root_.smul_apply,smul_eq_mul]
  dsimp only [C]
  nlinarith [sq_nonneg ‖y-x‖]
end WeakMTWTransport

end

end OAI
