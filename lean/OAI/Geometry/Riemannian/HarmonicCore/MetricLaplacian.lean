import OAI.Geometry.Riemannian.HarmonicCore.DeterminantDerivative
import OAI.Geometry.Riemannian.HarmonicCore.Energy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma inverse_derivative (g : SmoothMetric3) (x u : E3) :
    Matrix.of (fun i j ↦ fderiv ℝ (fun y ↦ (g.coeff y)⁻¹ i j) x u) =
      -(g.coeff x)⁻¹ * Matrix.of (fun i j ↦ fderiv ℝ (fun y ↦ g.coeff y i j) x u) * (g.coeff x)⁻¹ := by
  let D : M3 := fun i j ↦ fderiv ℝ (fun y ↦ g.coeff y i j) x u
  let V : M3 := fun i j ↦ fderiv ℝ (fun y ↦ (g.coeff y)⁻¹ i j) x u
  have hi (y : E3) : g.coeff y * (g.coeff y)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (g.positive y).det_pos.ne')
  have hd : D * (g.coeff x)⁻¹ + g.coeff x * V = 0 := by
    ext i j
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
      ((g.smooth i k).differentiable (by simp) x).hasFDerivAt.mul
        ((g.inverse_contDiff k j).differentiable (by simp) x).hasFDerivAt)
    have he : (fun y ↦ ∑ k, g.coeff y i k * (g.coeff y)⁻¹ k j) =
        fun _ : E3 ↦ (1 : M3) i j := funext (fun y ↦ congrFun (congrFun (hi y) i) j)
    simp only [Pi.mul_apply] at h
    rw [he] at h
    have hz := congrArg (fun f : E3 →L[ℝ] ℝ ↦ f u) h.fderiv
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, sum_apply,
      add_apply, smul_apply, smul_eq_mul] at hz
    change (∑ k, D i k * (g.coeff x)⁻¹ k j) +
      (∑ k, g.coeff x i k * V k j) = 0
    simp only [D, V, ← Finset.sum_add_distrib]
    convert hz.symm using 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hinv : (g.coeff x)⁻¹ * g.coeff x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (g.positive x).det_pos.ne')
  have h := congrArg (fun A : M3 ↦ (g.coeff x)⁻¹ * A) hd
  rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul, mul_zero] at h
  change V = -(g.coeff x)⁻¹ * D * (g.coeff x)⁻¹
  rw [neg_mul, neg_mul]
  exact eq_neg_of_add_eq_zero_right h

lemma coeff_symmetric (g : SmoothMetric3) (x : E3) : (g.coeff x).IsSymm := by
  simpa only [Matrix.isHermitian_iff_isSymm] using (g.positive x).isHermitian

lemma coeff_symm (g : SmoothMetric3) (x : E3) (i j : Fin 3) :
    g.coeff x i j = g.coeff x j i := ((g.coeff_symmetric x).apply i j).symm

lemma inverse_symmetric (g : SmoothMetric3) (x : E3) (i j : Fin 3) :
    (g.coeff x)⁻¹ i j = (g.coeff x)⁻¹ j i := by
  exact ((Matrix.isHermitian_iff_isSymm.mp (g.positive x).inv.isHermitian).apply i j).symm

lemma smooth_coord_hasDerivAt {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : E3) (i : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ f (x+t • coordinateVector i)) (coordDeriv f i x) 0 := by
  have hline : HasDerivAt (fun t : ℝ ↦ x+t • coordinateVector i) (coordinateVector i) 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const (coordinateVector i)) using 1
    simp
  convert! ((hf.differentiable (by simp) (x+0 • coordinateVector i)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline using 1
  simp [coordDeriv]

lemma determinant_coordDeriv (g : SmoothMetric3) (x : E3) (d : Fin 3) :
    coordDeriv (fun y ↦ (g.coeff y).det) d x = (g.coeff x).det *
      ∑ i, ∑ j, (g.coeff x)⁻¹ i j * coordDeriv (fun y ↦ g.coeff y j i) d x := by
  let D : M3 := fun i j ↦ coordDeriv (fun y ↦ g.coeff y i j) d x
  have h1 := determinant_hasDerivAt (G := fun t : ℝ ↦ g.coeff (x+t • coordinateVector d))
    (D:=D) (t:=0) (fun i j ↦ smooth_coord_hasDerivAt (g.smooth i j) x d)
  have h2 := smooth_coord_hasDerivAt (determinant_contDiff g.smooth) x d
  have h3 := h2.unique h1
  simp only [zero_smul,add_zero] at h3
  rw [h3]
  change (∑ i, ∑ j, (g.coeff x).adjugate i j * D j i) = _
  simp only [Matrix.inv_def,Matrix.smul_apply,Ring.inverse_eq_inv',smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [(g.positive x).det_pos.ne']
  rfl

lemma density_coordDeriv (g : SmoothMetric3) (x : E3) (d : Fin 3) :
    coordDeriv (fun y ↦ Real.sqrt (g.coeff y).det) d x =
      (Real.sqrt (g.coeff x).det / 2) *
        ∑ i, ∑ j, (g.coeff x)⁻¹ i j * coordDeriv (fun y ↦ g.coeff y j i) d x := by
  have h := (smooth_coord_hasDerivAt (determinant_contDiff g.smooth) x d).sqrt
    (by simpa only [zero_smul,add_zero] using (g.positive x).det_pos.ne')
  have hs : ContDiff ℝ ∞ (fun y ↦ Real.sqrt (g.coeff y).det) :=
    (determinant_contDiff g.smooth).sqrt (fun y ↦ (g.positive y).det_pos.ne')
  have he := (smooth_coord_hasDerivAt hs x d).unique h
  simp only [zero_smul,add_zero] at he
  rw [he,g.determinant_coordDeriv]
  have hp : 0 < Real.sqrt (g.coeff x).det := Real.sqrt_pos.mpr (g.positive x).det_pos
  have hsq := Real.sq_sqrt (g.positive x).det_pos.le
  field_simp
  nth_rw 1 [← hsq]
  ring

lemma inverse_coordDeriv (g : SmoothMetric3) (x : E3) (d i j : Fin 3) :
    coordDeriv (fun y ↦ (g.coeff y)⁻¹ i j) d x =
      -∑ b, ∑ a, (g.coeff x)⁻¹ i a * coordDeriv (fun y ↦ g.coeff y a b) d x *
        (g.coeff x)⁻¹ b j := by
  have hh := congrArg (fun M : M3 ↦ M i j) (g.inverse_derivative x (coordinateVector d))
  simpa only [Matrix.of_apply,Matrix.mul_apply,Matrix.neg_apply,neg_mul,
    Finset.sum_neg_distrib,Finset.sum_mul,coordDeriv] using hh

lemma coordDeriv_mul {f h : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (i : Fin 3) (x : E3) :
    coordDeriv (fun y ↦ f y * h y) i x = coordDeriv f i x * h x + f x * coordDeriv h i x := by
  unfold coordDeriv
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hh.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma divergence_inverse_algebra (A : M3) (D : Fin 3 → M3) (w : ℝ)
    (hA : ∀ i j, A i j = A j i) (j : Fin 3) :
    (∑ i, (((w/2)*(∑ a, ∑ b, A a b * D i b a))*A i j -
      w*(∑ b, ∑ a, A i a * D i a b * A b j))) =
      -w*(∑ a, ∑ b, A a b*((1/2:ℝ)*∑ q, A j q*(D a b q+D b a q-D q a b))) := by
  simp only [Fin.sum_univ_three]
  simp only [hA 0 j,hA 1 j,hA 2 j,hA 1 0,hA 2 0,hA 2 1]
  ring

lemma energyMatrix_contDiff (g : SmoothMetric3) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ g.energyMatrix x i j) :=
  ((determinant_contDiff g.smooth).sqrt (fun y ↦ (g.positive y).det_pos.ne')).mul
    (g.inverse_contDiff i j)

lemma energyMatrix_divergence (g : SmoothMetric3) (x : E3) (j : Fin 3) :
    (∑ i, coordDeriv (fun y ↦ g.energyMatrix y i j) i x) =
      -Real.sqrt (g.coeff x).det * ∑ a, ∑ b, (g.coeff x)⁻¹ a b * g.christoffel x j a b := by
  have hd := divergence_inverse_algebra (g.coeff x)⁻¹
    (fun d a b ↦ coordDeriv (fun y ↦ g.coeff y a b) d x)
    (Real.sqrt (g.coeff x).det) (g.inverse_symmetric x) j
  convert hd using 1
  · apply Finset.sum_congr rfl
    intro i _
    change coordDeriv (fun y ↦ Real.sqrt (g.coeff y).det * (g.coeff y)⁻¹ i j) i x = _
    rw [coordDeriv_mul ((determinant_contDiff g.smooth).sqrt
      (fun y ↦ (g.positive y).det_pos.ne')) (g.inverse_contDiff i j),
      g.density_coordDeriv,g.inverse_coordDeriv]
    ring
  · rfl

lemma coordDeriv_contDiff {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (coordDeriv f i) := by
  unfold coordDeriv
  exact hf.fderiv_right (by simp) |>.clm_apply contDiff_const

lemma coordDeriv_sum {ι : Type*} [Fintype ι] (f : ι → E3 → ℝ)
    (hf : ∀ a,ContDiff ℝ ∞ (f a)) (i : Fin 3) (x : E3) :
    coordDeriv (fun y ↦ ∑ a,f a y) i x = ∑ a,coordDeriv (f a) i x := by
  unfold coordDeriv
  rw [fderiv_fun_sum (fun a _ ↦ (hf a).differentiable (by simp) x)]
  simp only [sum_apply]

lemma coordDeriv_twice {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (x : E3) :
    coordDeriv (coordDeriv f j) i x =
      iteratedFDeriv ℝ 2 f x ![coordinateVector i,coordinateVector j] := by
  unfold coordDeriv
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x)
    (differentiableAt_const (c:=coordinateVector j))]
  simp

def metricFlux (g : SmoothMetric3) (f : E3 → ℝ) (x : E3) (i : Fin 3) : ℝ :=
  ∑ j,g.energyMatrix x i j * coordDeriv f j x

lemma metricFlux_contDiff (g : SmoothMetric3) {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ g.metricFlux f x i) :=
  ContDiff.sum (fun j _ ↦ (g.energyMatrix_contDiff i j).mul (coordDeriv_contDiff hf j))

lemma laplacian_divergence (g : SmoothMetric3) {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : E3) :
    (∑ i,coordDeriv (fun y ↦ g.metricFlux f y i) i x) =
      Real.sqrt (g.coeff x).det * g.laplacian f x := by
  have hexp : (∑ i,coordDeriv (fun y ↦ g.metricFlux f y i) i x) =
      (∑ j,(∑ i,coordDeriv (fun y ↦ g.energyMatrix y i j) i x)*coordDeriv f j x) +
      Real.sqrt (g.coeff x).det * ∑ i,∑ j,(g.coeff x)⁻¹ i j *
        iteratedFDeriv ℝ 2 f x ![coordinateVector i,coordinateVector j] := by
    simp only [metricFlux,coordDeriv_sum _ (fun j ↦ (g.energyMatrix_contDiff _ j).mul
      (coordDeriv_contDiff hf j)),coordDeriv_mul (g.energyMatrix_contDiff _ _)
      (coordDeriv_contDiff hf _),coordDeriv_twice hf,Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    · simp only [energyMatrix,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hexp]
  simp only [g.energyMatrix_divergence,laplacian]
  simp only [Fin.sum_univ_three]
  ring

lemma laplacian_green (g : SmoothMetric3) {f φ : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x * (Real.sqrt (g.coeff x).det * g.laplacian f x)) =
      -(∫ x, ∑ i,coordDeriv φ i x * g.metricFlux f x i) := by
  have hflux (i : Fin 3) := g.metricFlux_contDiff hf i
  have hdflux (i : Fin 3) := coordDeriv_contDiff (hflux i) i
  have hleft (i : Fin 3) : Integrable (fun x ↦ φ x *
      coordDeriv (fun y ↦ g.metricFlux f y i) i x) (volume : Measure E3) :=
    (hφ.continuous.mul (hdflux i).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hright (i : Fin 3) : Integrable (fun x ↦ coordDeriv φ i x *
      g.metricFlux f x i) (volume : Measure E3) :=
    ((coordDeriv_contDiff hφ i).continuous.mul (hflux i).continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ (coordinateVector i)).mul_right)
  have hparts (i : Fin 3) :
      (∫ x,φ x * coordDeriv (fun y ↦ g.metricFlux f y i) i x) =
        -(∫ x,coordDeriv φ i x * g.metricFlux f x i) := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact hright i
    · exact hleft i
    · exact (hφ.continuous.mul (hflux i).continuous).integrable_of_hasCompactSupport hc.mul_right
    · intro x _; exact hφ.differentiable (by simp) x
    · intro x _; exact (hflux i).differentiable (by simp) x
  simp_rw [← g.laplacian_divergence hf,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i),
    integral_finsetSum _ (fun i _ ↦ hright i)]
  simp only [hparts,Finset.sum_neg_distrib]

lemma density_laplacian_contDiff (g : SmoothMetric3) {f : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x ↦ Real.sqrt (g.coeff x).det * g.laplacian f x) := by
  have he : (fun x ↦ Real.sqrt (g.coeff x).det * g.laplacian f x) =
      (fun x ↦ ∑ i,coordDeriv (fun y ↦ g.metricFlux f y i) i x) := by
    funext x
    exact (g.laplacian_divergence hf x).symm
  rw [he]
  exact ContDiff.sum (fun i _ ↦ coordDeriv_contDiff (g.metricFlux_contDiff hf i) i)

lemma laplacian_eq_zero_of_weak_energy (g : SmoothMetric3) (R : ℝ) {f : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hweak : ∀ (φ : E3 → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0:E3) R →
      (∫ x,∑ i,coordDeriv φ i x * g.metricFlux f x i) = 0) :
    ∀ x ∈ Metric.ball (0:E3) R, g.laplacian f x = 0 := by
  have hc := (g.density_laplacian_contDiff hf).continuous
  have hae := (Metric.isOpen_ball : IsOpen (Metric.ball (0:E3) R)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hc.locallyIntegrable.locallyIntegrableOn (s:=Metric.ball (0:E3) R))
    (fun φ hφ hcompact hs ↦ by
      simpa only [smul_eq_mul,hweak φ hφ hcompact hs,neg_zero] using
        g.laplacian_green hf hφ hcompact)
  have he : Set.EqOn (fun x ↦ Real.sqrt (g.coeff x).det * g.laplacian f x)
      (fun _ ↦ 0) (Metric.ball (0:E3) R) :=
    (volume : Measure E3).eqOn_open_of_ae_eq
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr hae) Metric.isOpen_ball
      hc.continuousOn continuous_const.continuousOn
  intro x hx
  exact (mul_eq_zero.mp (he hx)).resolve_left
    (Real.sqrt_pos.mpr (g.positive x).det_pos).ne'

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
