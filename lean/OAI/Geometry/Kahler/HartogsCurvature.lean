import OAI.Geometry.Kahler.MetricCalculus

namespace OAI

universe uKahler2074_1 uKahler2080_1 uKahler2312_1 uKahler2472_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma coordinates_complex_smul (c : ℂ) (u : Ambient) :
    coordinates (c • u) = c • coordinates u := by
  funext i
  fin_cases i <;> rfl

private lemma complex_direction_algebra (a b z : ℂ) :
    (a * z + b * star z - Complex.I * (a * (Complex.I * z) + b * star (Complex.I * z))) / 2 =
      a * z := by
  simp only [star_mul', Complex.star_def, Complex.conj_I]
  linear_combination (b * starRingEnd ℂ z - a * z) / 2 * Complex.I_sq

private lemma anticomplex_direction_algebra (a b z : ℂ) :
    (a * z + b * star z + Complex.I * (a * (Complex.I * z) + b * star (Complex.I * z))) / 2 =
      b * star z := by
  simp only [star_mul', Complex.star_def, Complex.conj_I]
  linear_combination (a * z - b * starRingEnd ℂ z) / 2 * Complex.I_sq

lemma fderiv_complex_direction (f : Ambient → ℂ) (p u : Ambient) :
    (fderiv ℝ f p u - Complex.I * fderiv ℝ f p (Complex.I • u)) / 2 =
      ∑ i, dz f p i * coordinates u i := by
  rw [fderiv_wirtinger f p u, fderiv_wirtinger f p (Complex.I • u)]
  simp only [coordinates_complex_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact complex_direction_algebra _ _ _

lemma fderiv_anticomplex_direction (f : Ambient → ℂ) (p u : Ambient) :
    (fderiv ℝ f p u + Complex.I * fderiv ℝ f p (Complex.I • u)) / 2 =
      ∑ i, dbar f p i * star (coordinates u i) := by
  rw [fderiv_wirtinger f p u, fderiv_wirtinger f p (Complex.I • u)]
  simp only [coordinates_complex_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact anticomplex_direction_algebra _ _ _

def complexJacobian (F : Ambient → Ambient) (p : Ambient) : Fin 3 → Fin 3 → ℂ :=
  fun a i => coordinates (fderiv ℂ F p (coordVector i)) a

lemma dz_comp_holomorphic {f : Ambient → ℂ} {F : Ambient → Ambient} {p : Ambient}
    (hf : DifferentiableAt ℝ f (F p)) (hF : DifferentiableAt ℂ F p) (i : Fin 3) :
    dz (f ∘ F) p i = ∑ a, dz f (F p) a * complexJacobian F p a i := by
  have hd := (hf.hasFDerivAt.comp p (hF.hasFDerivAt.restrictScalars ℝ)).fderiv
  rw [dz, hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]
  exact fderiv_complex_direction f (F p) (fderiv ℂ F p (coordVector i))

lemma dbar_comp_holomorphic {f : Ambient → ℂ} {F : Ambient → Ambient} {p : Ambient}
    (hf : DifferentiableAt ℝ f (F p)) (hF : DifferentiableAt ℂ F p) (i : Fin 3) :
    dbar (f ∘ F) p i = ∑ a, dbar f (F p) a * star (complexJacobian F p a i) := by
  have hd := (hf.hasFDerivAt.comp p (hF.hasFDerivAt.restrictScalars ℝ)).fderiv
  rw [dbar, hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]
  exact fderiv_anticomplex_direction f (F p) (fderiv ℂ F p (coordVector i))

lemma dz_holomorphic {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℂ f p)
    (i : Fin 3) : dz f p i = fderiv ℂ f p (coordVector i) := by
  rw [dz, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination -fderiv ℂ f p (coordVector i) / 2 * Complex.I_sq

lemma dbar_holomorphic {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℂ f p)
    (i : Fin 3) : dbar f p i = 0 := by
  rw [dbar, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination fderiv ℂ f p (coordVector i) / 2 * Complex.I_sq

lemma dz_sum {ι : Type uKahler2074_1} (s : Finset ι) {f : ι → Ambient → ℂ} {p : Ambient}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) p) (i : Fin 3) :
    dz (fun q => ∑ j ∈ s, f j q) p i = ∑ j ∈ s, dz (f j) p i := by
  simp only [dz, fderiv_fun_sum hf, sum_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

lemma dbar_sum {ι : Type uKahler2080_1} (s : Finset ι) {f : ι → Ambient → ℂ} {p : Ambient}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) p) (i : Fin 3) :
    dbar (fun q => ∑ j ∈ s, f j q) p i = ∑ j ∈ s, dbar (f j) p i := by
  simp only [dbar, fderiv_fun_sum hf, sum_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

lemma complexJacobian_analyticAt {F : Ambient → Ambient} {p : Ambient}
    (hF : AnalyticAt ℂ F p) (a i : Fin 3) :
    AnalyticAt ℂ (fun q => complexJacobian F q a i) p := by
  let ev : (Ambient →L[ℂ] Ambient) →L[ℂ] Ambient :=
    ContinuousLinearMap.apply ℂ Ambient (coordVector i)
  let L : Ambient →L[ℂ] ℂ := (ContinuousLinearMap.proj a).comp coordinateEquiv.toContinuousLinearMap
  exact ((L.comp ev).analyticAt _).comp hF.fderiv

lemma complexHessian_comp_holomorphic {f : Ambient → ℝ} {F : Ambient → Ambient}
    {p : Ambient} (hf : ContDiffAt ℝ 2 f (F p)) (hF : AnalyticAt ℂ F p) (i j : Fin 3) :
    complexHessian (f ∘ F) p i j =
      ∑ a, ∑ b, complexHessian f (F p) a b * complexJacobian F p a i *
        star (complexJacobian F p b j) := by
  have hdF := hF.differentiableAt
  have he : (fun q => dbar (fun r => (f (F r) : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => ∑ b, dbar (fun r => (f r : ℂ)) (F q) b * star (complexJacobian F q b j)) := by
    filter_upwards [hF.eventually_analyticAt,
      hdF.continuousAt (hf.eventually (by norm_num))] with q hFq hfq
    change ContDiffAt ℝ 2 f (F q) at hfq
    exact dbar_comp_holomorphic
      ((_root_.OAI.ContDiffAt.hartogs_real_cast hfq).differentiableAt (by norm_num)) hFq.differentiableAt j
  have hdb (b : Fin 3) : DifferentiableAt ℝ (fun q => dbar (fun r => (f r : ℂ)) q b) (F p) :=
    (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) b).differentiableAt (by norm_num)
  have hJ (a i : Fin 3) := (complexJacobian_analyticAt hF a i).differentiableAt
  change dz (fun q => dbar (fun r => (f (F r) : ℂ)) q j) p i = _
  rw [dz_congr he]
  have hs := dz_sum Finset.univ (fun b hb =>
    ((hdb b).comp p (hdF.restrictScalars ℝ)).mul ((hJ b j).restrictScalars ℝ).star) i
  change dz (fun q => ∑ b, dbar (fun r => (f r : ℂ)) (F q) b *
    star (complexJacobian F q b j)) p i = _ at hs
  rw [hs]
  calc
    _ = ∑ b, ∑ a, complexHessian f (F p) a b * complexJacobian F p a i *
        star (complexJacobian F p b j) := by
      apply Finset.sum_congr rfl
      intro b hb
      change dz (fun q => dbar (fun r => (f r : ℂ)) (F q) b *
        star (complexJacobian F q b j)) p i = _
      have hm := dz_mul ((hdb b).comp p (hdF.restrictScalars ℝ))
        ((hJ b j).restrictScalars ℝ).star i
      change dz (fun q => dbar (fun r => (f r : ℂ)) (F q) b *
        star (complexJacobian F q b j)) p i = _ at hm
      rw [hm, dz_conj ((hJ b j).restrictScalars ℝ), dbar_holomorphic (hJ b j)]
      simp only [star_zero, mul_zero, add_zero]
      have hc := dz_comp_holomorphic (hdb b) hdF i
      rw [hc, Finset.sum_mul]
      rfl
    _ = _ := Finset.sum_comm

def dzMatrix (g : Ambient → CMatrix) (p : Ambient) (a : Fin 3) : CMatrix :=
  Matrix.of (fun i j => dz (fun q => g q i j) p a)
def dbarMatrix (g : Ambient → CMatrix) (p : Ambient) (a : Fin 3) : CMatrix :=
  Matrix.of (fun i j => dbar (fun q => g q i j) p a)

lemma matrix_diff_entry {g : Ambient → CMatrix} {p : Ambient}
    (hg : DifferentiableAt ℝ g p) (i j : Fin 3) :
    DifferentiableAt ℝ (fun q => g q i j) p :=
  differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j

lemma matrix_diff_mul {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    DifferentiableAt ℝ (fun q => f q * g q) p := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun q => ∑ k, f q i k * g q k j) p
  exact DifferentiableAt.fun_sum fun k hk => (matrix_diff_entry hf i k).mul (matrix_diff_entry hg k j)

lemma dzMatrix_mul {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dzMatrix (fun q => f q * g q) p a = dzMatrix f p a * g p + f p * dzMatrix g p a := by
  ext i j
  change dz (fun q => ∑ k, f q i k * g q k j) p a =
    (∑ k, dz (fun q => f q i k) p a * g p k j) +
      ∑ k, f p i k * dz (fun q => g q k j) p a
  have hs := dz_sum Finset.univ (fun k hk =>
    (matrix_diff_entry hf i k).mul (matrix_diff_entry hg k j)) a
  change dz (fun q => ∑ k, f q i k * g q k j) p a = _ at hs
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact dz_mul (matrix_diff_entry hf i k) (matrix_diff_entry hg k j) a

lemma dbarMatrix_mul {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dbarMatrix (fun q => f q * g q) p a = dbarMatrix f p a * g p + f p * dbarMatrix g p a := by
  ext i j
  change dbar (fun q => ∑ k, f q i k * g q k j) p a =
    (∑ k, dbar (fun q => f q i k) p a * g p k j) +
      ∑ k, f p i k * dbar (fun q => g q k j) p a
  have hs := dbar_sum Finset.univ (fun k hk =>
    (matrix_diff_entry hf i k).mul (matrix_diff_entry hg k j)) a
  change dbar (fun q => ∑ k, f q i k * g q k j) p a = _ at hs
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact dbar_mul (matrix_diff_entry hf i k) (matrix_diff_entry hg k j) a

lemma dbarMatrix_add {f g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dbarMatrix (fun q => f q + g q) p a = dbarMatrix f p a + dbarMatrix g p a := by
  ext i j
  exact dbar_add (matrix_diff_entry hf i j) (matrix_diff_entry hg i j) a

lemma dzMatrix_congr {f g : Ambient → CMatrix} {p : Ambient}
    (h : f =ᶠ[𝓝 p] g) (a : Fin 3) : dzMatrix f p a = dzMatrix g p a := by
  ext i j
  exact dz_congr (h.mono fun q hq => congrFun (congrFun hq i) j) a

lemma dbarMatrix_congr {f g : Ambient → CMatrix} {p : Ambient}
    (h : f =ᶠ[𝓝 p] g) (a : Fin 3) : dbarMatrix f p a = dbarMatrix g p a := by
  ext i j
  exact dbar_congr (h.mono fun q hq => congrFun (congrFun hq i) j) a

lemma matrix_contDiffAt_dz {g : Ambient → CMatrix} {p : Ambient} {m n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g p) (hm : m + 1 ≤ n) (a : Fin 3) :
    ContDiffAt ℝ m (fun q => dzMatrix g q a) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact _root_.OAI.ContDiffAt.hartogs_dz (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j) hm a

lemma matrix_contDiffAt_dbar {g : Ambient → CMatrix} {p : Ambient} {m n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g p) (hm : m + 1 ≤ n) (a : Fin 3) :
    ContDiffAt ℝ m (fun q => dbarMatrix g q a) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact _root_.OAI.ContDiffAt.hartogs_dbar (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j) hm a

def curvatureMatrix (g : Ambient → CMatrix) (p : Ambient) (a b : Fin 3) : CMatrix :=
  -dbarMatrix (fun q => dzMatrix g q a) p b + dzMatrix g p a * (g p)⁻¹ * dbarMatrix g p b

lemma curvatureMatrix_apply (g : Ambient → CMatrix) (p : Ambient) (a b c d : Fin 3) :
    curvatureMatrix g p a b c d = curvature g p a b c d := by
  simp only [curvatureMatrix, curvature, Matrix.neg_apply, Matrix.add_apply,
    Matrix.mul_apply, dzMatrix, dbarMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma gauge_curvature_algebra (A M B Az Mz Mb Bb Mzb : CMatrix)
    (hA : A.det ≠ 0) (hM : M.det ≠ 0) (hB : B.det ≠ 0) :
    -(Az * Mb * B + A * Mzb * B + (Az * M + A * Mz) * Bb) +
      (Az * M + A * Mz) * B * (A * M * B)⁻¹ * (A * Mb * B + A * M * Bb) =
        A * (-Mzb + Mz * M⁻¹ * Mb) * B := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hM' : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  simp only [Matrix.mul_inv_rev, mul_add, add_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left B _ hB',
    Matrix.nonsing_inv_mul_cancel_left A _ hA',
    Matrix.mul_nonsing_inv_cancel_left M _ hM',
    Matrix.nonsing_inv_mul_cancel_left M _ hM']
  noncomm_ring

lemma curvatureMatrix_gauge {A M B : Ambient → CMatrix} {p : Ambient}
    (hA : ContDiffAt ℝ 2 A p) (hM : ContDiffAt ℝ 2 M p) (hB : ContDiffAt ℝ 2 B p)
    (hAdbar : ∀ᶠ q in 𝓝 p, ∀ a, dbarMatrix A q a = 0)
    (hBdz : ∀ᶠ q in 𝓝 p, ∀ a, dzMatrix B q a = 0)
    (hAdet : (A p).det ≠ 0) (hMdet : (M p).det ≠ 0) (hBdet : (B p).det ≠ 0)
    (a b : Fin 3) :
    curvatureMatrix (fun q => A q * M q * B q) p a b =
      A p * curvatureMatrix M p a b * B p := by
  have hAd := hA.differentiableAt (by norm_num)
  have hMd := hM.differentiableAt (by norm_num)
  have hBd := hB.differentiableAt (by norm_num)
  have hAzd := (matrix_contDiffAt_dz hA (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  have hMzd := (matrix_contDiffAt_dz hM (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  have hAb : dbarMatrix A p b = 0 := (hAdbar.self_of_nhds) b
  have hBza : dzMatrix B p a = 0 := (hBdz.self_of_nhds) a
  have hAzb : dbarMatrix (fun q => dzMatrix A q a) p b = 0 := by
    ext i j
    change dbar (fun q => dz (fun r => A r i j) q a) p b = 0
    rw [← dz_dbar_comm (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j) a b]
    have he : (fun q => dbar (fun r => A r i j) q b) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hAdbar] with q hq
      exact congrFun (congrFun (hq b) i) j
    rw [dz_congr he]
    simp [dz]
  have hfirst : (fun q => dzMatrix (fun r => A r * M r * B r) q a) =ᶠ[𝓝 p]
      (fun q => (dzMatrix A q a * M q + A q * dzMatrix M q a) * B q) := by
    filter_upwards [hA.eventually (by norm_num), hM.eventually (by norm_num),
      hB.eventually (by norm_num), hBdz] with q hAq hMq hBq hBzq
    rw [dzMatrix_mul (matrix_diff_mul (hAq.differentiableAt (by norm_num))
      (hMq.differentiableAt (by norm_num))) (hBq.differentiableAt (by norm_num)),
      dzMatrix_mul (hAq.differentiableAt (by norm_num)) (hMq.differentiableAt (by norm_num)),
      hBzq a, mul_zero, add_zero]
  have hsecond : dbarMatrix (fun q => dzMatrix (fun r => A r * M r * B r) q a) p b =
      dzMatrix A p a * dbarMatrix M p b * B p +
      A p * dbarMatrix (fun q => dzMatrix M q a) p b * B p +
      (dzMatrix A p a * M p + A p * dzMatrix M p a) * dbarMatrix B p b := by
    have hsumd : DifferentiableAt ℝ
        (fun q => dzMatrix A q a * M q + A q * dzMatrix M q a) p :=
      (matrix_diff_mul hAzd hMd).add (matrix_diff_mul hAd hMzd)
    rw [dbarMatrix_congr hfirst,
      dbarMatrix_mul hsumd hBd,
      dbarMatrix_add (matrix_diff_mul hAzd hMd) (matrix_diff_mul hAd hMzd),
      dbarMatrix_mul hAzd hMd, dbarMatrix_mul hAd hMzd, hAzb, hAb]
    simp only [zero_mul, zero_add, add_mul]
  have hbar : dbarMatrix (fun q => A q * M q * B q) p b =
      A p * dbarMatrix M p b * B p + A p * M p * dbarMatrix B p b := by
    rw [dbarMatrix_mul (matrix_diff_mul hAd hMd) hBd, dbarMatrix_mul hAd hMd, hAb]
    simp only [zero_mul, zero_add]
  have hpoint : dzMatrix (fun q => A q * M q * B q) p a =
      (dzMatrix A p a * M p + A p * dzMatrix M p a) * B p := hfirst.self_of_nhds
  unfold curvatureMatrix
  rw [hsecond, hpoint, hbar]
  exact gauge_curvature_algebra _ _ _ _ _ _ _ _ hAdet hMdet hBdet

lemma dbarMatrix_smul {f : Ambient → ℂ} {g : Ambient → CMatrix} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (a : Fin 3) :
    dbarMatrix (fun q => f q • g q) p a = dbar f p a • g p + f p • dbarMatrix g p a := by
  ext i j
  exact dbar_mul hf (matrix_diff_entry hg i j) a

lemma dbarMatrix_sum {ι : Type uKahler2312_1} (s : Finset ι) {f : ι → Ambient → CMatrix} {p : Ambient}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) p) (a : Fin 3) :
    dbarMatrix (fun q => ∑ k ∈ s, f k q) p a = ∑ k ∈ s, dbarMatrix (f k) p a := by
  ext i j
  simpa only [dbarMatrix, Matrix.of_apply, Matrix.sum_apply] using
    dbar_sum s (fun k hk => matrix_diff_entry (hf k hk) i j) a

lemma dzMatrix_comp_holomorphic {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : DifferentiableAt ℝ g (F p)) (hF : DifferentiableAt ℂ F p) (a : Fin 3) :
    dzMatrix (g ∘ F) p a = ∑ e, complexJacobian F p e a • dzMatrix g (F p) e := by
  ext i j
  simpa only [dzMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm, Function.comp_def] using dz_comp_holomorphic (matrix_diff_entry hg i j) hF a

lemma dbarMatrix_comp_holomorphic {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : DifferentiableAt ℝ g (F p)) (hF : DifferentiableAt ℂ F p) (a : Fin 3) :
    dbarMatrix (g ∘ F) p a = ∑ e, star (complexJacobian F p e a) • dbarMatrix g (F p) e := by
  ext i j
  simpa only [dbarMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm, Function.comp_def] using dbar_comp_holomorphic (matrix_diff_entry hg i j) hF a

lemma curvatureMatrix_comp_holomorphic {g : Ambient → CMatrix} {F : Ambient → Ambient}
    {p : Ambient} (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p) (a b : Fin 3) :
    curvatureMatrix (g ∘ F) p a b = ∑ e, ∑ f,
      (complexJacobian F p e a * star (complexJacobian F p f b)) •
        curvatureMatrix g (F p) e f := by
  have hgd := hg.differentiableAt (by norm_num)
  have hFd := hF.differentiableAt
  have hJ (e i : Fin 3) := (complexJacobian_analyticAt hF e i).differentiableAt
  have hgzd (e : Fin 3) :=
    (matrix_contDiffAt_dz hg (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  have hgzF (e : Fin 3) := (hgzd e).comp p (hFd.restrictScalars ℝ)
  have he : (fun q => dzMatrix (g ∘ F) q a) =ᶠ[𝓝 p]
      (fun q => ∑ e, complexJacobian F q e a • dzMatrix g (F q) e) := by
    filter_upwards [hF.eventually_analyticAt,
      hFd.continuousAt (hg.eventually (by norm_num))] with q hFq hgq
    change ContDiffAt ℝ 2 g (F q) at hgq
    exact dzMatrix_comp_holomorphic (hgq.differentiableAt (by norm_num)) hFq.differentiableAt a
  have hsecond : dbarMatrix (fun q => dzMatrix (g ∘ F) q a) p b =
      ∑ e, ∑ f, (complexJacobian F p e a * star (complexJacobian F p f b)) •
        dbarMatrix (fun q => dzMatrix g q e) (F p) f := by
    rw [dbarMatrix_congr he]
    have hs := dbarMatrix_sum Finset.univ
      (fun e he => ((hJ e a).restrictScalars ℝ).smul (hgzF e)) b
    change dbarMatrix (fun q => ∑ e, complexJacobian F q e a • dzMatrix g (F q) e) p b = _ at hs
    rw [hs]
    apply Finset.sum_congr rfl
    intro e he
    have hm := dbarMatrix_smul ((hJ e a).restrictScalars ℝ) (hgzF e) b
    change dbarMatrix (fun q => complexJacobian F q e a • dzMatrix g (F q) e) p b = _ at hm
    change dbarMatrix (fun q => complexJacobian F q e a • dzMatrix g (F q) e) p b = _
    rw [hm, dbar_holomorphic (hJ e a), zero_smul, zero_add,
      dbarMatrix_comp_holomorphic (hgzd e) hFd, Finset.smul_sum]
    simp only [smul_smul]
  unfold curvatureMatrix
  rw [hsecond, dzMatrix_comp_holomorphic hgd hFd, dbarMatrix_comp_holomorphic hgd hFd]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Function.comp_apply,
    Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  rw [mul_comm (star (complexJacobian F p f b))]

def jacobianMatrix (F : Ambient → Ambient) (p : Ambient) : CMatrix :=
  Matrix.of (complexJacobian F p)

def pullbackMetric (g : Ambient → CMatrix) (F : Ambient → Ambient) (p : Ambient) : CMatrix :=
  (jacobianMatrix F p)ᵀ * g (F p) * (jacobianMatrix F p)ᵀᴴ

lemma complexHessian_pullback {f : Ambient → ℝ} {F : Ambient → Ambient} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f (F p)) (hF : AnalyticAt ℂ F p) :
    complexHessian (f ∘ F) p = pullbackMetric (complexHessian f) F p := by
  ext i j
  rw [complexHessian_comp_holomorphic hf hF]
  simp only [pullbackMetric, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, jacobianMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma curvatureMatrix_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (a b : Fin 3) :
    curvatureMatrix (pullbackMetric g F) p a b =
      (jacobianMatrix F p)ᵀ * (∑ e, ∑ f,
        (complexJacobian F p e a * star (complexJacobian F p f b)) •
          curvatureMatrix g (F p) e f) * (jacobianMatrix F p)ᵀᴴ := by
  have hAa (i j : Fin 3) : AnalyticAt ℂ (fun q => (jacobianMatrix F q)ᵀ i j) p :=
    complexJacobian_analyticAt hF j i
  have hA : ContDiffAt ℝ 2 (fun q => (jacobianMatrix F q)ᵀ) p := by
    exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      (hAa i j).contDiffAt.restrict_scalars ℝ
  have hB : ContDiffAt ℝ 2 (fun q => (jacobianMatrix F q)ᵀᴴ) p := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp p
      ((hAa j i).contDiffAt (n := 2) |>.restrict_scalars ℝ)
  have hM : ContDiffAt ℝ 2 (g ∘ F) p :=
    hg.comp p (hF.contDiffAt.restrict_scalars ℝ)
  have hAdb : ∀ᶠ q in 𝓝 p, ∀ i, dbarMatrix (fun r => (jacobianMatrix F r)ᵀ) q i = 0 := by
    filter_upwards [hF.eventually_analyticAt] with q hq
    intro i
    ext e f
    exact dbar_holomorphic (complexJacobian_analyticAt hq f e).differentiableAt i
  have hBdz : ∀ᶠ q in 𝓝 p, ∀ i, dzMatrix (fun r => (jacobianMatrix F r)ᵀᴴ) q i = 0 := by
    filter_upwards [hF.eventually_analyticAt] with q hq
    intro i
    ext e f
    change dz (fun r => star (complexJacobian F r e f)) q i = 0
    rw [dz_conj ((complexJacobian_analyticAt hq e f).differentiableAt.restrictScalars ℝ),
      dbar_holomorphic (complexJacobian_analyticAt hq e f).differentiableAt, star_zero]
  have hAne : (jacobianMatrix F p)ᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using hJdet
  have hBne : (jacobianMatrix F p)ᵀᴴ.det ≠ 0 := by
    simpa only [Matrix.det_conjTranspose, star_ne_zero] using hAne
  have hh := curvatureMatrix_gauge hA hM hB hAdb hBdz hAne hgdet hBne a b
  change curvatureMatrix (pullbackMetric g F) p a b =
    (jacobianMatrix F p)ᵀ * curvatureMatrix (g ∘ F) p a b * (jacobianMatrix F p)ᵀᴴ at hh
  rw [hh, curvatureMatrix_comp_holomorphic hg hF]

def matrixPush (A : CMatrix) (u : Ambient) : Ambient :=
  coordinateEquiv.symm (A *ᵥ coordinates u)

def matrixPull (A h : CMatrix) : CMatrix := Aᵀ * h * Aᵀᴴ

lemma hermitianValue_dot (h : CMatrix) (u v : Ambient) :
    hermitianValue h u v = coordinates u ⬝ᵥ (h *ᵥ star (coordinates v)) := by
  simp only [hermitianValue, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma hermitianValue_matrixPull (A h : CMatrix) (u v : Ambient) :
    hermitianValue (matrixPull A h) u v = hermitianValue h (matrixPush A u) (matrixPush A v) := by
  simp only [hermitianValue_dot, matrixPull, matrixPush, coordinates_equiv_symm,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_conjTranspose, star_star, Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma matrixPull_apply (A h : CMatrix) (i j : Fin 3) :
    matrixPull A h i j = ∑ a, ∑ b, h a b * A a i * star (A b j) := by
  simp only [matrixPull, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma hermitianValue_sum {ι : Type uKahler2472_1} (s : Finset ι) (h : ι → CMatrix) (u v : Ambient) :
    hermitianValue (∑ k ∈ s, h k) u v = ∑ k ∈ s, hermitianValue (h k) u v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermitianValue]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, hermitianValue, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib] at *
    rw [ih]

lemma coordinates_complex_decomposition (u : Ambient) :
    u = ∑ i, coordinates u i • coordVector i := by
  apply coordinateEquiv.injective
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three, coordinates, coordVector, coordinateEquiv,
    coordinateLinearEquiv]

lemma matrixPush_jacobian (F : Ambient → Ambient) (p u : Ambient) :
    matrixPush (jacobianMatrix F p) u = fderiv ℂ F p u := by
  apply coordinateEquiv.injective
  simp only [matrixPush, ContinuousLinearEquiv.apply_symm_apply]
  change (jacobianMatrix F p) *ᵥ coordinates u = coordinates (fderiv ℂ F p u)
  conv_rhs => rw [coordinates_complex_decomposition u]
  ext a
  simp only [map_sum, map_smul, coordinates_equiv, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, jacobianMatrix, Matrix.of_apply, complexJacobian]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

def tensorPairMatrix (R : CurvatureTensor) (w y : Ambient) : CMatrix :=
  Matrix.of (fun a b => hermitianValue (Matrix.of (R a b)) w y)

lemma tensorValue_as_hermitianValue (R : CurvatureTensor) (u v w y : Ambient) :
    tensorValue R u v w y = hermitianValue (tensorPairMatrix R w y) u v := by
  simp only [tensorValue, hermitianValue, tensorPairMatrix, Matrix.of_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma tensorPairMatrix_curvature_apply (g : Ambient → CMatrix) (p w y : Ambient) (a b : Fin 3) :
    tensorPairMatrix (curvature g p) w y a b = hermitianValue (curvatureMatrix g p a b) w y := by
  have he : Matrix.of (curvature g p a b) = curvatureMatrix g p a b := by
    ext c d
    exact (curvatureMatrix_apply g p a b c d).symm
  change hermitianValue (Matrix.of (curvature g p a b)) w y = _
  rw [he]

lemma tensorPairMatrix_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (w y : Ambient) :
    tensorPairMatrix (curvature (pullbackMetric g F) p) w y =
      matrixPull (jacobianMatrix F p) (tensorPairMatrix (curvature g (F p))
        (matrixPush (jacobianMatrix F p) w) (matrixPush (jacobianMatrix F p) y)) := by
  ext a b
  rw [tensorPairMatrix_curvature_apply, curvatureMatrix_pullback hg hF hgdet hJdet]
  change hermitianValue (matrixPull (jacobianMatrix F p) _) w y = _
  rw [hermitianValue_matrixPull, matrixPull_apply]
  simp only [hermitianValue_sum, hermitianValue_smul]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  rw [tensorPairMatrix_curvature_apply]
  change (complexJacobian F p e a * star (complexJacobian F p f b)) * _ =
    _ * complexJacobian F p e a * star (complexJacobian F p f b)
  ring

lemma tensorValue_curvature_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (u v w y : Ambient) :
    tensorValue (curvature (pullbackMetric g F) p) u v w y =
      tensorValue (curvature g (F p)) (fderiv ℂ F p u) (fderiv ℂ F p v)
        (fderiv ℂ F p w) (fderiv ℂ F p y) := by
  rw [tensorValue_as_hermitianValue, tensorPairMatrix_pullback hg hF hgdet hJdet,
    hermitianValue_matrixPull, ← tensorValue_as_hermitianValue]
  simp only [matrixPush_jacobian]

lemma hermitianValue_pullback (g : Ambient → CMatrix) (F : Ambient → Ambient) (p u v : Ambient) :
    hermitianValue (pullbackMetric g F p) u v =
      hermitianValue (g (F p)) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  change hermitianValue (matrixPull (jacobianMatrix F p) (g (F p))) u v = _
  rw [hermitianValue_matrixPull, matrixPush_jacobian, matrixPush_jacobian]

lemma sectional_pullback {g : Ambient → CMatrix} {F : Ambient → Ambient} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g (F p)) (hF : AnalyticAt ℂ F p)
    (hgdet : (g (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0) (u v : Ambient) :
    sectional (pullbackMetric g F) p u v =
      sectional g (F p) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  simp only [sectional, tensorValue_curvature_pullback hg hF hgdet hJdet, realArea,
    hermitianValue_pullback]

lemma curvatureMatrix_congr {g h : Ambient → CMatrix} {p : Ambient}
    (he : g =ᶠ[𝓝 p] h) (a b : Fin 3) : curvatureMatrix g p a b = curvatureMatrix h p a b := by
  have hz : (fun q => dzMatrix g q a) =ᶠ[𝓝 p] fun q => dzMatrix h q a :=
    he.eventually_nhds.mono fun q hq => dzMatrix_congr hq a
  have hp : g p = h p := he.self_of_nhds
  rw [curvatureMatrix, curvatureMatrix, dbarMatrix_congr hz,
    dzMatrix_congr he, dbarMatrix_congr he, hp]

lemma curvature_congr {g h : Ambient → CMatrix} {p : Ambient}
    (he : g =ᶠ[𝓝 p] h) : curvature g p = curvature h p := by
  funext a b c d
  rw [← curvatureMatrix_apply, ← curvatureMatrix_apply, curvatureMatrix_congr he]

lemma sectional_congr {g h : Ambient → CMatrix} {p : Ambient}
    (he : g =ᶠ[𝓝 p] h) (u v : Ambient) : sectional g p u v = sectional h p u v := by
  have hp : g p = h p := he.self_of_nhds
  rw [sectional, sectional, curvature_congr he, hp]

lemma sectional_complexHessian_comp {f : Ambient → ℝ} {F : Ambient → Ambient} {p : Ambient}
    (hf : ContDiffAt ℝ ∞ f (F p)) (hF : AnalyticAt ℂ F p)
    (hfdet : (complexHessian f (F p)).det ≠ 0) (hJdet : (jacobianMatrix F p).det ≠ 0)
    (u v : Ambient) :
    sectional (complexHessian (f ∘ F)) p u v =
      sectional (complexHessian f) (F p) (fderiv ℂ F p u) (fderiv ℂ F p v) := by
  have hf2 : ContDiffAt ℝ 2 f (F p) := hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have he : complexHessian (f ∘ F) =ᶠ[𝓝 p] pullbackMetric (complexHessian f) F := by
    filter_upwards [hF.eventually_analyticAt,
      hF.differentiableAt.continuousAt (hf2.eventually (by norm_num))] with q hFq hfq
    change ContDiffAt ℝ 2 f (F q) at hfq
    exact complexHessian_pullback hfq hFq
  rw [sectional_congr he]
  exact sectional_pullback ((complexHessian_contDiffAt hf).of_le
    (by exact WithTop.coe_le_coe.mpr le_top)) hF hfdet hJdet u v

lemma fderiv_injective_of_jacobianMatrix_det {F : Ambient → Ambient} {p : Ambient}
    (hJ : (jacobianMatrix F p).det ≠ 0) : Function.Injective (fderiv ℂ F p) := by
  have hunit : IsUnit (jacobianMatrix F p) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hJ)
  have hmat := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  intro u v huv
  apply coordinateEquiv.injective
  apply hmat
  have hh := congrArg coordinates huv
  rw [← matrixPush_jacobian F p u, ← matrixPush_jacobian F p v] at hh
  simpa only [matrixPush, coordinates_equiv_symm, coordinates_equiv, ContinuousLinearEquiv.apply_symm_apply] using hh

end PinchedHartogs

end

end OAI
