import OAI.Geometry.RCD.Sobolev.EuclideanDirectionalLaplacian

namespace OAI

/-! # Local rigidity of harmonic functions with constant gradient norm -/

open Set Metric InnerProductSpace Laplacian
open scoped ContDiff BigOperators Topology
noncomputable section
namespace RegularPointCoordinates

theorem laplacian_finite_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Euclidean n → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : Euclidean n) :
    (Δ (fun y => ∑ i ∈ s, f i y)) x = ∑ i ∈ s, (Δ (f i)) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContDiff ℝ 2 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hc : ContDiff ℝ 2 (fun y => ∑ j ∈ s, f j y) := ContDiff.sum hfs
    simp only [Finset.sum_insert hi]
    change (Δ (f i + fun y => ∑ j ∈ s, f j y)) x = _
    rw [hfi.contDiffAt.laplacian_add hc.contDiffAt, ih hfs]

theorem harmonic_constant_energy_second_directional_zero {n : ℕ}
    {f : Euclidean n → ℝ} (hf : ContDiff ℝ 3 f) {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (hh : HarmonicOnNhd f Ω) {C : ℝ}
    (he : ∀ y ∈ Ω, ‖fderiv ℝ f y‖^2 = C) {x : Euclidean n} (hx : x ∈ Ω)
    (i j : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1) = 0 := by
  classical
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let d := fun i y => fderiv ℝ f y (e i)
  have hd (i : Fin n) : ContDiff ℝ 2 (d i) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hΔ (i : Fin n) : (Δ (d i)) x = 0 := by
    change (Δ (fun y => fderiv ℝ f y (e i))) x = 0
    rw [laplacian_directional_commute hf x (e i)]
    have hzero : (Δ f) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact (hh y hy).2.self_of_nhds
    rw [hzero.fderiv_eq]
    simp
  have hnorm : (fun y => ‖fderiv ℝ f y‖^2) = fun y => ∑ i : Fin n, (d i y)^2 := by
    funext y
    simpa only [d,e,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_dual (fderiv ℝ f y)
  have hconstant : (fun y => ‖fderiv ℝ f y‖^2) =ᶠ[𝓝 x] fun _ => C := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact he y hy
  have hΔenergy : (Δ (fun y => ‖fderiv ℝ f y‖^2)) x = 0 := by
    have hz := (laplacian_congr_nhds hconstant).self_of_nhds
    simpa using hz
  rw [hnorm, laplacian_finite_sum Finset.univ (fun i y => (d i y)^2)
    (fun i _ => (hd i).pow 2)] at hΔenergy
  simp_rw [laplacian_square_formula (hd _) x, hΔ, mul_zero, zero_add] at hΔenergy
  have hnonneg (i : Fin n) : 0 ≤ 2*∑ j : Fin n, (fderiv ℝ (d i) x (e j))^2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hi := (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)).trans_eq hΔenergy
  have hj := Finset.single_le_sum (fun k _ => sq_nonneg (fderiv ℝ (d i) x (e k)))
    (Finset.mem_univ j)
  have hz : (fderiv ℝ (d i) x (e j))^2 = 0 := by nlinarith [sq_nonneg (fderiv ℝ (d i) x (e j))]
  exact sq_eq_zero_iff.mp hz

theorem harmonic_constant_energy_hessian_zero {n : ℕ}
    {f : Euclidean n → ℝ} (hf : ContDiff ℝ 3 f) {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (hh : HarmonicOnNhd f Ω) {C : ℝ}
    (he : ∀ y ∈ Ω, ‖fderiv ℝ f y‖^2 = C) {x : Euclidean n} (hx : x ∈ Ω) :
    fderiv ℝ (fderiv ℝ f) x = 0 := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hp (i j : Fin n) : fderiv ℝ (fderiv ℝ f) x (b j) (b i) = 0 := by
    have h := harmonic_constant_energy_second_directional_zero hf hΩ hh he hx i j
    have hd := (hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) x
    simpa [b,fderiv_clm_apply hd (differentiableAt_const _)] using h
  ext v w
  nth_rw 1 [← b.sum_repr v]
  rw [map_sum, sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, smul_apply]
  nth_rw 1 [← b.sum_repr w]
  rw [map_sum]
  simp only [map_smul, hp, smul_zero, Finset.sum_const_zero]

theorem harmonic_constant_energy_affine {n : ℕ}
    {f : Euclidean n → ℝ} (hf : ContDiff ℝ 3 f) {S C : ℝ} (hS : 0 < S)
    (hh : HarmonicOnNhd f (ball 0 S))
    (he : ∀ y ∈ ball (0 : Euclidean n) S, ‖fderiv ℝ f y‖^2 = C) :
    ∀ x ∈ ball (0 : Euclidean n) S, f x = f 0 + fderiv ℝ f 0 x := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hconst (x : Euclidean n) (hx : x ∈ ball (0 : Euclidean n) S) :
      fderiv ℝ f x = fderiv ℝ f 0 :=
    isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : Euclidean n) S).isPreconnected
      hdf.differentiableOn (fun y hy => harmonic_constant_energy_hessian_zero hf isOpen_ball hh he hy)
      hx (mem_ball_self hS)
  let g := fun x => f x-fderiv ℝ f 0 x
  have hg : Differentiable ℝ g := (hf.differentiable (by norm_num)).sub (fderiv ℝ f 0).differentiable
  have hz : EqOn (fderiv ℝ g) 0 (ball (0 : Euclidean n) S) := by
    intro x hx
    change fderiv ℝ (f-⇑(fderiv ℝ f 0)) x = 0
    rw [fderiv_sub (hf.differentiable (by norm_num) x) (fderiv ℝ f 0).differentiableAt,
      (fderiv ℝ f 0).fderiv, hconst x hx, sub_self]
  intro x hx
  have heq := isOpen_ball.is_const_of_fderiv_eq_zero
    (convex_ball (0 : Euclidean n) S).isPreconnected hg.differentiableOn hz hx (mem_ball_self hS)
  change f x-fderiv ℝ f 0 x = f 0-fderiv ℝ f 0 0 at heq
  rw [map_zero, sub_zero] at heq
  linarith

end RegularPointCoordinates

end

end OAI
