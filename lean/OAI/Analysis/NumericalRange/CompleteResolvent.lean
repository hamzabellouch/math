import OAI.Analysis.NumericalRange.DiskCalculus

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_81} [Fintype n] [DecidableEq n]

lemma fourier_nat_pow (t : AddCircle (1:ℝ)) (k : ℕ) :
    fourier 1 t ^ k = fourier (k:ℤ) t := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ, hk, ← fourier_add]
    congr 2

lemma integrable_polynomial_diskDensity {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (p : ℂ[X]) :
    Integrable (fun t : AddCircle (1:ℝ) => p.eval (fourier 1 t) • diskDensity D t)
      circleMeasure := by
  exact ((p.continuous.comp (fourier 1).continuous).smul (continuous_diskDensity hD)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma polynomial_diskDensity {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (p : ℂ[X]) :
    (∫ t : AddCircle (1:ℝ), p.eval (fourier 1 t) • diskDensity D t ∂circleMeasure) =
      Polynomial.aeval D p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, add_smul, map_add]
    rw [integral_add (integrable_polynomial_diskDensity hD p)
      (integrable_polynomial_diskDensity hD q), hp, hq]
  | monomial k a =>
    simp only [Polynomial.eval_monomial, fourier_nat_pow, mul_smul]
    rw [integral_smul, diskDensity_moment hD]
    simp [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]

end

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_82} [Fintype n] [DecidableEq n]

lemma stable_spectrum_norm_lt_one {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {z : ℂ} (hz : z ∈ spectrum ℂ D) : ‖z‖ < 1 := by
  have hle : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ D := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ D) => (‖k‖₊ : ℝ≥0∞)) z hz
  have hl : (‖z‖₊ : ℝ≥0∞) < 1 := hle.trans_lt hD
  exact_mod_cast hl

lemma analytic_diskDensity {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    (∫ t : AddCircle (1:ℝ), f (fourier 1 t) • diskDensity D t ∂circleMeasure) =
      matrixAnalyticEval D f := by
  obtain ⟨r,hr,p,hp⟩ := analytic_closed_disk_polynomial_approximation hf
  have hmem (t : AddCircle (1:ℝ)) : fourier 1 t ∈ ball (0:ℂ) r := by
    simpa only [mem_ball, dist_zero_right, fourier_norm_value] using hr
  have hpc : TendstoUniformlyOn (fun N (t : AddCircle (1:ℝ)) => (p N).eval (fourier 1 t))
      (fun t => f (fourier 1 t)) atTop univ :=
    (hp.comp (fun t : AddCircle (1:ℝ) => fourier 1 t)).mono (fun t _ => hmem t)
  have hfc : Continuous (fun t : AddCircle (1:ℝ) => f (fourier 1 t)) := by
    exact hf.continuousOn.comp_continuous (fourier 1).continuous fun point => by
      simp only [mem_closedBall, dist_zero_right, fourier_norm_value, le_refl]
  obtain ⟨C,hC⟩ := isCompact_univ.bddAbove_image hfc.norm.continuousOn
  have hnorm : ∀ t ∈ (univ : Set (AddCircle (1:ℝ))), ‖f (fourier 1 t)‖ ≤ C := by
    intro t ht
    exact hC ⟨t, ht, rfl⟩
  have hev : ∀ᶠ N in atTop, ∀ t ∈ (univ : Set (AddCircle (1:ℝ))),
      ‖(p N).eval (fourier 1 t)‖ ≤ C+1 :=
    (uniformContinuous_norm.comp_tendstoUniformlyOn hpc).eventually_forall_le
      (by linarith) hnorm
  have hlim : Tendsto (fun N => ∫ t : AddCircle (1:ℝ),
      (p N).eval (fourier 1 t) • diskDensity D t ∂circleMeasure) atTop
      (nhds (∫ t : AddCircle (1:ℝ), f (fourier 1 t) • diskDensity D t ∂circleMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t => (C+1)*‖diskDensity D t‖)
    · exact Eventually.of_forall fun N => (integrable_polynomial_diskDensity hD (p N)).aestronglyMeasurable
    · filter_upwards [hev] with N hN
      exact ae_of_all _ fun t => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hN t (mem_univ _)) (norm_nonneg _)
    · exact (continuous_const.mul (continuous_diskDensity hD).norm).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact ae_of_all _ fun t => (hpc.tendsto_at (mem_univ t)).smul tendsto_const_nhds
  have hcalc := matrixAnalyticEval_tendsto_locallyUniform D isOpen_ball
    (fun z hz => show z ∈ ball (0:ℂ) r from by
      simpa only [mem_ball, dist_zero_right] using (stable_spectrum_norm_lt_one hD hz).trans hr)
    (F := fun N z => (p N).eval z)
    (fun N z _ => (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (p N)) z (mem_univ _)) hp.tendstoLocallyUniformlyOn
  simp only [polynomial_diskDensity hD] at hlim
  simp only [matrixAnalyticEval_polynomial] at hcalc
  exact tendsto_nhds_unique hlim hcalc

end

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_83} {m : Type u_84} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

def completeAnalyticEval (D : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    Matrix (n×m) (n×m) ℂ :=
  fun i j => matrixAnalyticEval D (fun z => F z i.2 j.2) i.1 j.1

lemma continuous_analytic_circle
    {m : Type u_84} [Fintype m] [DecidableEq m] {F : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, AnalyticOnNhd ℂ (fun z => F z i j) (closedBall 0 1)) :
    Continuous (fun t : AddCircle (1:ℝ) => F (fourier 1 t)) := by
  apply continuous_matrix
  intro i j
  exact (hF i j).continuousOn.comp_continuous (fourier 1).continuous fun point => by
    simp only [mem_closedBall, dist_zero_right, fourier_norm_value, le_refl]

theorem complete_analytic_disk_representation {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {F : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, AnalyticOnNhd ℂ (fun z => F z i j) (closedBall 0 1)) :
    (∫ t : AddCircle (1:ℝ), diskDensity D t ⊗ₖ F (fourier 1 t) ∂circleMeasure) =
      completeAnalyticEval D F := by
  have hi : Integrable (fun t : AddCircle (1:ℝ) => diskDensity D t ⊗ₖ F (fourier 1 t)) circleMeasure :=
    (continuous_kron (continuous_diskDensity hD) (continuous_analytic_circle hF)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  ext i j
  rw [matrix_integral_entry hi]
  unfold completeAnalyticEval
  rw [← analytic_diskDensity hD (hF i.2 j.2)]
  have hj : Integrable (fun t : AddCircle (1:ℝ) => F (fourier 1 t) i.2 j.2 • diskDensity D t) circleMeasure :=
    (((continuous_analytic_circle hF).matrix_elem i.2 j.2).smul
    (continuous_diskDensity hD)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry hj]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by simp [Matrix.kroneckerMap_apply, mul_comm]

theorem stable_complete_analytic_disk_bound {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (hDc : Dᴴ*D ≤ 1) {F : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, AnalyticOnNhd ℂ (fun z => F z i j) (closedBall 0 1))
    (hbound : ∀ t : AddCircle (1:ℝ), ‖F (fourier 1 t)‖ ≤ 1) :
    ‖completeAnalyticEval D F‖ ≤ 1 := by
  rw [← complete_analytic_disk_representation hD hF]
  apply norm_integral_density_kron
  · exact (continuous_diskDensity hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_kron (continuous_diskDensity hD) (continuous_analytic_circle hF)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro t
    exact Matrix.nonneg_iff_posSemidef.mp (diskDensity_nonneg hD hDc t)
  · simpa only [Nat.cast_zero, fourier_zero, one_smul, pow_zero] using diskDensity_moment hD 0
  · exact hbound

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

lemma primaryEval_add {V : Type u_85} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ T, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ T, AnalyticAt ℂ g z) :
    primaryEval T (fun z => f z + g z) = primaryEval T f + primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  simp only [LinearMap.add_apply, primaryEval_coe]
  rw [scalarJetEval_add (hf β hβ) (hg β hβ)]
  simp

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_const (D : Matrix n n ℂ) (c : ℂ) :
    matrixAnalyticEval D (fun _ => c) = algebraMap ℂ (Matrix n n ℂ) c := by
  apply Matrix.toLinAlgEquiv'.injective
  simp [matrixAnalyticEval, primaryEval_const]

lemma matrixAnalyticEval_id (D : Matrix n n ℂ) :
    matrixAnalyticEval D (fun z => z) = D := by
  simpa using matrixAnalyticEval_polynomial D (Polynomial.X : ℂ[X])

lemma matrixAnalyticEval_add (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z + g z) = matrixAnalyticEval D f + matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_add, AlgEquiv.apply_symm_apply]
  exact primaryEval_add _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma matrixAnalyticEval_mul (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z * g z) = matrixAnalyticEval D f * matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_mul, AlgEquiv.apply_symm_apply]
  exact primaryEval_mul _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma matrixAnalyticEval_sum {ι : Type u_88} (s : Finset ι) (D : Matrix n n ℂ) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (f i) z) :
    matrixAnalyticEval D (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, matrixAnalyticEval D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixAnalyticEval_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [matrixAnalyticEval_add D (hf i (Finset.mem_insert_self _ _))
      (fun z hz => Finset.analyticAt_fun_sum _ fun j hj => hf j (Finset.mem_insert_of_mem hj) z hz)]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma completeAnalyticEval_const
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun _ => C) = (1 : Matrix n n ℂ) ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

lemma completeAnalyticEval_add
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z + G z) =
      completeAnalyticEval D F + completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.add_apply]
  rw [matrixAnalyticEval_add D (hF _ _) (hG _ _)]
  rfl

lemma completeAnalyticEval_mul
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z * G z) =
      completeAnalyticEval D F * completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [matrixAnalyticEval_sum Finset.univ D (f := fun k z => F z i.2 k * G z k j.2)
    (fun k _ z hz => (hF i.2 k z hz).mul (hG k j.2 z hz))]
  simp only [Matrix.sum_apply]
  simp_rw [matrixAnalyticEval_mul D (hF _ _) (hG _ _), Matrix.mul_apply]
  rw [Finset.sum_comm]

lemma completeAnalyticEval_zsmul
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun z => z • C) = D ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, Matrix.smul_apply, smul_eq_mul]
  simp only [matrixAnalyticEval_mul D (f := fun z => z) (g := fun _ => C i.2 j.2)
    (fun _ _ => analyticAt_id) (fun _ _ => analyticAt_const),
    matrixAnalyticEval_id, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one]
  simp [Matrix.kroneckerMap_apply, mul_comm]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_eventuallyEq (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (h : ∀ z ∈ spectrum ℂ D, f =ᶠ[nhds z] g) :
    matrixAnalyticEval D f = matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_eventuallyEq _ (fun z hz => h z (by simpa using hz))

lemma completeAnalyticEval_eqOn
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : spectrum ℂ D ⊆ U) (he : EqOn F G U) :
    completeAnalyticEval D F = completeAnalyticEval D G := by
  ext i j
  unfold completeAnalyticEval
  apply congrArg (fun M : Matrix n n ℂ => M i.1 j.1)
  apply matrixAnalyticEval_eventuallyEq
  intro z hz
  filter_upwards [hU.mem_nhds (hDU hz)] with w hw
  rw [he hw]

lemma matrixAnalyticEval_sub (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z - g z) = matrixAnalyticEval D f - matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_sub, AlgEquiv.apply_symm_apply]
  exact primaryEval_sub _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_sub
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z - G z) =
      completeAnalyticEval D F - completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.sub_apply]
  rw [matrixAnalyticEval_sub D (hF _ _) (hG _ _)]
  rfl

lemma matrix_entry_analytic {f : ℂ → Matrix m m ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (i j : m) : AnalyticAt ℂ (fun w => f w i j) z := by
  let L : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact (L.toContinuousLinearMap.analyticAt (f z)).comp hf

lemma scalar_matrix_inverse_analytic {a : Matrix m m ℂ} {z : ℂ}
    (hunit : IsUnit (1-z • a)) :
    AnalyticAt ℂ (fun w : ℂ => (1-w • a)⁻¹) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => (1-w • a : Matrix m m ℂ)) z := by fun_prop
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using
    (show AnalyticAt ℂ Ring.inverse (1-z • a) from by
      simpa only [hunit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hunit.unit)).comp
        (f := fun w : ℂ => (1-w • a : Matrix m m ℂ)) ha

lemma resolvent_disk_analytic {a : Matrix m m ℂ} (ha : ‖a‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1-z • a)⁻¹) (ball 0 1) := by
  intro z hz
  apply scalar_matrix_inverse_analytic
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
    (by simpa only [mul_one] using mem_ball_zero_iff.mp hz)

lemma complete_resolvent_inverse {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    {a : Matrix m m ℂ} (ha : ‖a‖ ≤ 1) :
    completeAnalyticEval D (fun z => (1-z • a)⁻¹) * (1-D ⊗ₖ a) = 1 := by
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz =>
    mem_ball_zero_iff.mpr (stable_spectrum_norm_lt_one hD hz)
  have hR i j z hz := matrix_entry_analytic (resolvent_disk_analytic ha z (hspec hz)) i j
  have hM i j (z:ℂ) : AnalyticAt ℂ (fun w => (1-w • a) i j) z := by
    apply matrix_entry_analytic
    fun_prop
  have he : completeAnalyticEval D (fun z => (1-z • a)⁻¹*(1-z • a)) = 1 := by
    rw [completeAnalyticEval_eqOn D isOpen_ball hspec (G := fun _ => (1 : Matrix m m ℂ))]
    · rw [completeAnalyticEval_const, Matrix.one_kronecker_one]
    · intro z hz
      apply Matrix.nonsing_inv_mul
      apply (Matrix.isUnit_iff_isUnit_det _).mp
      apply isUnit_one_sub_of_norm_lt_one
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
        (by simpa only [mul_one] using mem_ball_zero_iff.mp hz)
  rw [completeAnalyticEval_mul D hR (fun i j z _ => hM i j z)] at he
  have hm : completeAnalyticEval D (fun z => (1 : Matrix m m ℂ)-z • a) = 1-D ⊗ₖ a := by
    rw [completeAnalyticEval_sub D (F := fun _ => (1 : Matrix m m ℂ)) (G := fun z => z • a)
      (fun _ _ _ _ => analyticAt_const)
      (fun i j z _ => matrix_entry_analytic (by fun_prop) i j),
      completeAnalyticEval_const, Matrix.one_kronecker_one, completeAnalyticEval_zsmul]
  rwa [hm] at he

lemma complete_resolvent_inverse_of_isUnit {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    {a : Matrix m m ℂ} (ha : ∀ z ∈ ball (0:ℂ) 1, IsUnit (1-z • a)) :
    completeAnalyticEval D (fun z => (1-z • a)⁻¹) * (1-D ⊗ₖ a) = 1 := by
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz =>
    mem_ball_zero_iff.mpr (stable_spectrum_norm_lt_one hD hz)
  have hR i j z hz := matrix_entry_analytic (scalar_matrix_inverse_analytic (ha z (hspec hz))) i j
  have hM i j (z:ℂ) : AnalyticAt ℂ (fun w => (1-w • a) i j) z := by
    apply matrix_entry_analytic
    fun_prop
  have he : completeAnalyticEval D (fun z => (1-z • a)⁻¹*(1-z • a)) = 1 := by
    rw [completeAnalyticEval_eqOn D isOpen_ball hspec (G := fun _ => (1 : Matrix m m ℂ))]
    · rw [completeAnalyticEval_const, Matrix.one_kronecker_one]
    · intro z hz
      apply Matrix.nonsing_inv_mul
      apply (Matrix.isUnit_iff_isUnit_det _).mp
      exact ha z hz
  rw [completeAnalyticEval_mul D hR (fun i j z _ => hM i j z)] at he
  have hm : completeAnalyticEval D (fun z => (1 : Matrix m m ℂ)-z • a) = 1-D ⊗ₖ a := by
    rw [completeAnalyticEval_sub D (F := fun _ => (1 : Matrix m m ℂ)) (G := fun z => z • a)
      (fun _ _ _ _ => analyticAt_const)
      (fun i j z _ => matrix_entry_analytic (by fun_prop) i j),
      completeAnalyticEval_const, Matrix.one_kronecker_one, completeAnalyticEval_zsmul]
  rwa [hm] at he


end CompleteCrouzeix

end

end OAI
