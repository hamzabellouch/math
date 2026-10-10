import OAI.Analysis.HenonEmden.Mollification

namespace OAI

universe uE

section Scaling

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
noncomputable section

open Set Filter Topology
namespace HenonLaneEmden


noncomputable def alpha (p q A B : ℝ) := (2+A+p*(2+B))/(p*q-1)
noncomputable def beta (p q A B : ℝ) := (2+B+q*(2+A))/(p*q-1)

lemma scaling_relations {p q A B : ℝ} (hpq : 1 < p*q) :
    p*beta p q A B = alpha p q A B+2+A ∧
    q*alpha p q A B = beta p q A B+2+B := by
  unfold alpha beta
  have h : p*q-1 ≠ 0 := ne_of_gt (sub_pos.mpr hpq)
  constructor
  · field_simp [h]
    ring
  · have h' : q*p-1 ≠ 0 := by simpa [mul_comm] using h
    field_simp [h, h']
    ring

lemma alpha_pos {p q A B : ℝ} (hp : 0 < p) (hA : -2 < A) (hB : -2 < B)
    (hpq : 1 < p*q) : 0 < alpha p q A B := by
  apply div_pos _ (sub_pos.mpr hpq)
  exact add_pos (by linarith) (mul_pos hp (by linarith))

lemma beta_pos {p q A B : ℝ} (hq : 0 < q) (hA : -2 < A) (hB : -2 < B)
    (hpq : 1 < p*q) : 0 < beta p q A B := by
  apply div_pos _ (sub_pos.mpr hpq)
  exact add_pos (by linarith) (mul_pos hq (by linarith))

lemma subcritical_scaling_exponent {n : ℕ} {p q A B : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p*q) (hsub : Subcritical n p q A B) :
    0 < alpha p q A B + beta p q A B + 2 - (n : ℝ) := by
  have hp1 : 0 < p+1 := by linarith
  have hq1 : 0 < q+1 := by linarith
  have hden : 0 < p*q-1 := sub_pos.mpr hpq
  have hid : ((n : ℝ)+A)/(p+1) + ((n : ℝ)+B)/(q+1) - ((n : ℝ)-2) =
      (p*q-1)/((p+1)*(q+1)) * (alpha p q A B+beta p q A B+2-(n : ℝ)) := by
    unfold alpha beta
    field_simp
    ring
  unfold Subcritical at hsub
  have hleft : 0 < ((n : ℝ)+A)/(p+1) + ((n : ℝ)+B)/(q+1) - ((n : ℝ)-2) :=
    by simpa only [one_add_one_eq_two] using (sub_pos.mpr hsub)
  rw [hid] at hleft
  exact pos_of_mul_pos_right hleft (div_nonneg hden.le (mul_pos hp1 hq1).le)

section LaplacianScaling
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma laplacian_comp_dilation (f : E → ℝ) {R : ℝ} (hR : R ≠ 0) (x : E) :
    Laplacian.laplacian (fun y => f (R • y)) x = R^2 * Laplacian.laplacian f (R • x) := by
  let g : E ≃L[ℝ] E := (Units.mk0 R hR) • ContinuousLinearEquiv.refl ℝ E
  have hg (y : E) : g y = R • y := by simp [g]
  have hi := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y => f (R • y)) = f ∘ g := by ext y; simp [hg]
  rw [heq, hi]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe, hg]
  -- The pointwise vector family is factored by multilinearity.
  convert (iteratedFDeriv ℝ 2 f (R • x)).map_smul_univ (fun _ : Fin 2 => R)
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] using 1
  simp [pow_two, smul_eq_mul]

end LaplacianScaling

noncomputable def dilation {n : ℕ} (u : Space n → ℝ) (a R : ℝ) : Space n → ℝ :=
  fun x => R^a*u (R • x)

lemma dilation_regular {n : ℕ} {u : Space n → ℝ} (a : ℝ) {R : ℝ} (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) :
    ContDiffOn ℝ 2 (dilation u a R) ({0}ᶜ : Set (Space n)) := by
  apply contDiffOn_const.mul
  apply hu.comp (ContDiff.const_smul R contDiff_id).contDiffOn
  intro x hx
  exact smul_ne_zero (ne_of_gt hR) hx

lemma dilation_equation {n : ℕ} {u v : Space n → ℝ} {p A a b R : ℝ}
    (hR : 0 < R) (hrel : p*b = a+2+A)
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hv : ∀ x, 0 < v x)
    (heq : ∀ x, x ≠ 0 → -(Laplacian.laplacian u) x = ‖x‖^A*(v x)^p)
    (x : Space n) (hx : x ≠ 0) :
    -(Laplacian.laplacian (dilation u a R)) x = ‖x‖^A*(dilation v b R x)^p := by
  have hxR : R • x ≠ 0 := smul_ne_zero (ne_of_gt hR) hx
  have hu' : ContDiffAt ℝ 2 (fun y => u (R • y)) x := by
    apply (hu.contDiffAt ((isClosed_singleton.isOpen_compl).mem_nhds hxR)).comp x
    exact (ContDiff.const_smul R contDiff_id).contDiffAt
  have hLap : Laplacian.laplacian (dilation u a R) x =
      R^a*(R^2*Laplacian.laplacian u (R • x)) := by
    change Laplacian.laplacian (R^a • (fun y => u (R • y))) x = _
    rw [InnerProductSpace.laplacian_smul (R^a) hu', laplacian_comp_dilation u (ne_of_gt hR)]
    rfl
  have hscale : R^a*R^2*R^A = (R^b)^p := by
    rw [← Real.rpow_mul hR.le, mul_comm b p, hrel, Real.rpow_add hR, Real.rpow_add hR, Real.rpow_two]
  rw [hLap]
  calc
    -(R^a*(R^2*Laplacian.laplacian u (R • x))) =
        R^a*R^2*(-Laplacian.laplacian u (R • x)) := by ring
    _ = R^a*R^2*(‖R • x‖^A*(v (R • x))^p) := by rw [heq _ hxR]
    _ = (R^a*R^2*R^A)*‖x‖^A*(v (R • x))^p := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg x)]
      ring
    _ = ‖x‖^A*(dilation v b R x)^p := by
      rw [hscale, dilation, Real.mul_rpow (Real.rpow_nonneg hR.le _) (hv _).le]
      ring

lemma IsSolution.dilate {n : ℕ} {p q A B : ℝ} {u v : Space n → ℝ}
    (h : IsSolution n p q A B u v) (hpq : 1 < p*q) {R : ℝ} (hR : 0 < R) :
    IsSolution n p q A B (dilation u (alpha p q A B) R)
      (dilation v (beta p q A B) R) := by
  have hrels := scaling_relations (A := A) (B := B) hpq
  refine ⟨?_, ?_, dilation_regular _ hR h.regular_u, dilation_regular _ hR h.regular_v,
    ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul (h.continuous_u.comp (continuous_id.const_smul R))
  · exact continuous_const.mul (h.continuous_v.comp (continuous_id.const_smul R))
  · intro x; exact mul_pos (Real.rpow_pos_of_pos hR _) (h.positive_u _)
  · intro x; exact mul_pos (Real.rpow_pos_of_pos hR _) (h.positive_v _)
  · exact dilation_equation hR hrels.1 h.regular_u h.positive_v h.equation_u
  · exact dilation_equation hR hrels.2 h.regular_v h.positive_u h.equation_v

end HenonLaneEmden

end
end Scaling

end OAI
