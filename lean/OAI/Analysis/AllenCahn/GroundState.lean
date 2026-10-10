import OAI.Analysis.AllenCahn.EllipticRegularity

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open scoped ENNReal
open MeasureTheory Filter Topology

lemma coordDeriv_continuous_of_C1 {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) : Continuous (coordDeriv f i) := by
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma coordDeriv_hasCompactSupport {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) (i : Fin n) : HasCompactSupport (coordDeriv f i) := by
  exact hf.fderiv_apply ℝ _

lemma integral_test_laplacian {n : ℕ} {f h : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hh : ContDiff ℝ 2 h) :
    (∫ x, f x * Laplacian.laplacian h x) =
      -(∫ x, ∑ i : Fin n, coordDeriv f i x * coordDeriv h i x) := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hI (i : Fin n) : Integrable
      (fun x => f x * coordDeriv (coordDeriv h i) i x) :=
    (hf.continuous.mul (coordDeriv_continuous_of_C1 (coordDeriv_contDiff hh i) i)).integrable_of_hasCompactSupport hc.mul_right
  have hJ (i : Fin n) : Integrable
      (fun x => coordDeriv f i x * coordDeriv h i x) :=
    ((coordDeriv_continuous_of_C1 hf i).mul (coordDeriv_continuous_of_C1 h1 i)).integrable_of_hasCompactSupport (coordDeriv_hasCompactSupport hc i).mul_right
  simp_rw [laplacian_eq_sum_coordDeriv hh, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hJ i) (hI i)
    ((hf.continuous.mul (coordDeriv_continuous_of_C1 h1 i)).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => (coordDeriv_contDiff hh i).differentiable (by norm_num) x)

theorem positive_ground_state_identity {n : ℕ} {h η : Space n → ℝ}
    (hh : ContDiff ℝ 2 h) (hp : ∀ x, 0 < h x)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ x, (‖gradient η x‖ ^ 2 + (Laplacian.laplacian h x / h x) * η x ^ 2)) =
      ∫ x, h x ^ 2 * ‖gradient (fun y => η y / h y) x‖ ^ 2 := by
  have hn : ∀ x, h x ≠ 0 := fun x => (hp x).ne'
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  let f : Space n → ℝ := fun x => η x ^ 2 / h x
  have hf : ContDiff ℝ 1 f := (hη.pow 2).div h1 hn
  have hfc : HasCompactSupport f := by
    simpa only [f, pow_two, div_eq_mul_inv, Pi.mul_def] using
      (hηc.mul_right (f' := η)).mul_right (f' := fun x => (h x)⁻¹)
  have hI (i : Fin n) : Integrable
      (fun x => f x * coordDeriv (coordDeriv h i) i x) :=
    (hf.continuous.mul (coordDeriv_continuous_of_C1 (coordDeriv_contDiff hh i) i)).integrable_of_hasCompactSupport hfc.mul_right
  have hJ (i : Fin n) : Integrable
      (fun x => coordDeriv f i x * coordDeriv h i x) :=
    ((coordDeriv_continuous_of_C1 hf i).mul (coordDeriv_continuous_of_C1 h1 i)).integrable_of_hasCompactSupport (coordDeriv_hasCompactSupport hfc i).mul_right
  have hK (i : Fin n) : Integrable (fun x => (coordDeriv η i x) ^ 2) := by
    apply ((coordDeriv_continuous_of_C1 hη i).pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two, Pi.mul_apply] using
      (coordDeriv_hasCompactSupport hηc i).mul_right (f' := coordDeriv η i)
  have hIl : Integrable (fun x => f x * Laplacian.laplacian h x) := by
    simp_rw [laplacian_eq_sum_coordDeriv hh, Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => hI i)
  have hJs : Integrable (fun x => ∑ i : Fin n, coordDeriv f i x * coordDeriv h i x) :=
    integrable_finsetSum _ (fun i _ => hJ i)
  have hKg : Integrable (fun x => ‖gradient η x‖ ^ 2) := by
    simp_rw [gradient_norm_sq]
    exact integrable_finsetSum _ (fun i _ => hK i)
  have hid (x : Space n) :
      ‖gradient η x‖ ^ 2 - (∑ i : Fin n, coordDeriv f i x * coordDeriv h i x) =
        h x ^ 2 * ‖gradient (fun y => η y / h y) x‖ ^ 2 := by
    simp_rw [gradient_norm_sq, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [coordDeriv_div (hηd.fun_pow 2) hd hn,
      coordDeriv_square hηd, coordDeriv_div hηd hd hn]
    field_simp [hn x]
    ring
  calc
    (∫ x, (‖gradient η x‖ ^ 2 + (Laplacian.laplacian h x / h x) * η x ^ 2)) =
        ∫ x, (‖gradient η x‖ ^ 2 + f x * Laplacian.laplacian h x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp only [f]
      ring
    _ = (∫ x, ‖gradient η x‖ ^ 2) + ∫ x, f x * Laplacian.laplacian h x :=
      integral_add hKg hIl
    _ = (∫ x, ‖gradient η x‖ ^ 2) -
        ∫ x, ∑ i : Fin n, coordDeriv f i x * coordDeriv h i x := by
      rw [integral_test_laplacian hf hfc hh, sub_eq_add_neg]
    _ = ∫ x, (‖gradient η x‖ ^ 2 -
        ∑ i : Fin n, coordDeriv f i x * coordDeriv h i x) :=
      (integral_sub hKg hJs).symm
    _ = ∫ x, h x ^ 2 * ‖gradient (fun y => η y / h y) x‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall hid)

lemma stable_of_positive_jacobi {n : ℕ} {u h : Space n → ℝ}
    (hh : ContDiff ℝ 2 h) (hp : ∀ x, 0 < h x)
    (hEq : ∀ x, Laplacian.laplacian h x = (3 * u x ^ 2 - 1) * h x) : Stable u := by
  intro η hη hηc
  have hQ := positive_ground_state_identity hh hp hη hηc
  have hn : ∀ x, h x ≠ 0 := fun x => (hp x).ne'
  simp_rw [hEq, mul_div_cancel_right₀ _ (hn _)] at hQ
  change 0 ≤ ∫ x, (‖gradient η x‖ ^ 2 + (3 * u x ^ 2 - 1) * η x ^ 2)
  rw [hQ]
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma coordDeriv_allenCahn_jacobi {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hAC : AllenCahn u) (i : Fin n) (x : Space n) :
    Laplacian.laplacian (coordDeriv u i) x =
      (3 * u x ^ 2 - 1) * coordDeriv u i x := by
  rw [laplacian_coordDeriv hu]
  have he : Laplacian.laplacian u = fun x => u x ^ 3 - u x := funext hAC
  rw [he]
  have hd := hu.differentiable (by simp)
  rw [coordDeriv_sub (hd.fun_pow 3) hd]
  change fderiv ℝ (fun y => u y ^ 3) x _ - _ = _
  rw [fderiv_fun_pow 3 (hd x)]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub]
  change 3 * u x ^ 2 * coordDeriv u i x - coordDeriv u i x = _
  ring

theorem stable_of_coordinate_monotone {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (hb : ∀ x, u x ∈ Set.Icc (-1 : ℝ) 1)
    (hAC : AllenCahn u) (j : Fin n)
    (hmon : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single j 1)) : Stable u := by
  have hs : ContDiff ℝ ∞ u := RegularitySupport.DeGiorgi.allenCahn_smooth hu hb hAC
  apply stable_of_positive_jacobi (smooth_C2 (coordDeriv_smooth hs j))
  · intro x
    change 0 < fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)
    simpa only [EuclideanSpace.basisFun_apply] using hmon x
  · exact coordDeriv_allenCahn_jacobi hs hAC j

end DeGiorgi
end

end OAI
