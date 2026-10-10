import Mathlib
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Rational Trivialization. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u

open scoped Topology
open Filter

namespace SplitTangent.TangentSplitting
section
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 
def coordinateProjector (x : X.Carrier) (z : Model X) : Model X →L[ℂ] Model X :=
  let t := trivializationAt (Model X) (Tangent X) x
  let y := (chartAt (Model X) x).symm z
  (t.continuousLinearMapAt ℂ y).comp ((S.projector y).comp (t.symmL ℂ y))

def coordinateMatrix (x : X.Carrier) (i j : Fin X.dim) (z : Model X) : ℂ :=
  LinearMap.toMatrix' (S.coordinateProjector x z).toLinearMap i j

theorem coordinateMatrix_mulVec (x : X.Carrier) (z v : Model X) :
    Matrix.mulVec (fun i j => S.coordinateMatrix x i j z) v = S.coordinateProjector x z v :=
  LinearMap.toMatrix'_mulVec _ _

theorem coordinateProjector_idempotent (x : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target) (v : Model X) :
    S.coordinateProjector x z (S.coordinateProjector x z v) = S.coordinateProjector x z v := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hy : (chartAt (Model X) x).symm z ∈ t.baseSet :=
    (chartAt (Model X) x).map_target hz
  simp only [coordinateProjector,ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hy, S.idempotent]

theorem coordinateMatrix_idempotent (x : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target) (i j : Fin X.dim) :
    ∑ k, S.coordinateMatrix x i k z * S.coordinateMatrix x k j z =
      S.coordinateMatrix x i j z := by
  have hcomp : (S.coordinateProjector x z).toLinearMap.comp
      (S.coordinateProjector x z).toLinearMap = (S.coordinateProjector x z).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact S.coordinateProjector_idempotent x hz v
  have hM := congrArg LinearMap.toMatrix' hcomp
  rw [LinearMap.toMatrix'_comp] at hM
  exact congrFun (congrFun hM i) j

 

theorem coordinateMatrix_analytic (x : X.Carrier) (i j : Fin X.dim) :
    AnalyticOnNhd ℂ (S.coordinateMatrix x i j) (chartAt (Model X) x).target := by
  let t := trivializationAt (Model X) (Tangent X) x
  let b := Pi.basisFun ℂ (Fin X.dim)
  let c := chartAt (Model X) x
  let H := fun y : X.Carrier => (t ⟨y,S.projector y (t.localFrame b j y)⟩).2
  have hframe : HolomorphicSectionOn X (t.localFrame b j) t.baseSet :=
    t.contMDiffOn_localFrame_baseSet ω b j
  have hH : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ, Model X) ω H t.baseSet :=
    t.contMDiffOn_section_baseSet_iff.mp (S.holomorphicSectionOn_projectField hframe)
  have heq : Set.EqOn (S.coordinateMatrix x i j) (fun z => H (c.symm z) i) c.target := by
    intro z hz
    have hy : c.symm z ∈ t.baseSet := c.map_target hz
    have hb : t.symmL ℂ (c.symm z) (Pi.single j 1) = t.localFrame b j (c.symm z) := by
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet t b hy]
      simp only [Bundle.Trivialization.basisAt,Module.Basis.map_apply,b,Pi.basisFun_apply]
      simp only [Bundle.Trivialization.linearEquivAt_symm_apply,Bundle.Trivialization.symmL_apply t hy]
    simp only [coordinateMatrix,LinearMap.toMatrix'_apply,coordinateProjector,
      ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply]
    rw [hb,Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ t hy]
  intro z hz
  have hc : ContMDiffAt 𝓘(ℂ,Model X) (ModelWithCorners X) ω c.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) x) hz
  have hh : AnalyticAt ℂ (fun z => H (c.symm z)) z :=
    ((hH.contMDiffAt (t.open_baseSet.mem_nhds (c.map_target hz))).comp z hc).contDiffAt.analyticAt
  apply (analyticAt_pi_iff.mp hh i).congr
  exact Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hz) (fun z hz => (heq hz).symm)

end

variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def coordinateTransition (x y : X.Carrier) : Model X → Model X :=
  (chartAt (Model X) y) ∘ (chartAt (Model X) x).symm

theorem coordinateTransition_analytic (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source) :
    AnalyticAt ℂ (coordinateTransition x y) z := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) y) hzy
  have hd := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z hd).contDiffAt.analyticAt

theorem coordinateTransition_derivative (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source) :
    fderiv ℂ (coordinateTransition x y) z =
      ((trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ
        ((chartAt (Model X) x).symm z)).comp
      ((trivializationAt (Model X) (Tangent X) x).symmL ℂ
        ((chartAt (Model X) x).symm z)) := by
  let c := chartAt (Model X) x
  let d := chartAt (Model X) y
  have hc := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) y) hzy).mdifferentiableAt (by simp)
  have hd := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz).mdifferentiableAt (by simp)
  have hA : (trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ (c.symm z) =
      mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) d (c.symm z) := by
    exact TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hzy
  have hB : (trivializationAt (Model X) (Tangent X) x).symmL ℂ (c.symm z) =
      mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm z := by
    have he := TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) (c.map_target hz)
    have he' : (trivializationAt (Model X) (Tangent X) x).symmL ℂ (c.symm z) =
        mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c (c.symm z)) := by
      simpa [extChartAt_coe_symm,extChartAt_coe,ModelWithCorners,c] using he
    rw [c.right_inv hz] at he'
    exact he' 
  change fderiv ℂ (d ∘ c.symm) z = _
  rw [hA,hB]
  exact mfderiv_eq_fderiv.symm.trans (mfderiv_comp z hc hd)

 
theorem coordinateProjector_intertwining (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source) :
    (fderiv ℂ (coordinateTransition x y) z).comp (S.coordinateProjector x z) =
      (S.coordinateProjector y (coordinateTransition x y z)).comp
        (fderiv ℂ (coordinateTransition x y) z) := by
  rw [coordinateTransition_derivative x y hz hzy]
  let t := trivializationAt (Model X) (Tangent X) x
  let t' := trivializationAt (Model X) (Tangent X) y
  have hx : (chartAt (Model X) x).symm z ∈ t.baseSet := (chartAt (Model X) x).map_target hz
  have hy : (chartAt (Model X) x).symm z ∈ t'.baseSet := hzy
  have he : (chartAt (Model X) y).symm (coordinateTransition x y z) =
      (chartAt (Model X) x).symm z := (chartAt (Model X) y).left_inv hzy
  simp only [coordinateProjector]
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hx,t'.symmL_continuousLinearMapAt hy]

end SplitTangent.TangentSplitting

end

noncomputable section
universe u
open Filter Topology Set Bundle
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SplitTangent.HolomorphicLinearODE
section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

def solutionCoeff (A : ℕ → R) (v : R) : ℕ → R
  | 0 => v
  | n+1 => ((n+1 : ℕ) : ℂ)⁻¹ •
      ∑ i ∈ Finset.range (n+1), A i * solutionCoeff A v (n-i)
termination_by n => n

omit [CompleteSpace R] in
lemma solutionCoeff_recurrence (A : ℕ → R) (v : R) (n : ℕ) :
    ((n+1 : ℕ) : ℂ) • solutionCoeff A v (n+1) =
      ∑ i ∈ Finset.range (n+1), A i * solutionCoeff A v (n-i) := by
  rw [solutionCoeff,smul_smul]
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_inv_cancel₀ hn,one_smul]

omit [CompleteSpace R] in
lemma solutionCoeff_norm {A : ℕ → R} (v : R) {B : ℝ} (hB : 0 < B)
    (hA : ∀ n, ‖A n‖ ≤ B^(n+1)) (n : ℕ) :
    ‖solutionCoeff A v n‖ ≤ B^n * ‖v‖ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [solutionCoeff]
    | succ n =>
      rw [solutionCoeff,norm_smul]
      have hc : ‖(((n+1 : ℕ) : ℂ))⁻¹‖ = ((n+1 : ℕ) : ℝ)⁻¹ := by rw [norm_inv,Complex.norm_natCast]
      rw [hc]
      have hs : ‖∑ i ∈ Finset.range (n+1), A i * solutionCoeff A v (n-i)‖ ≤
          ((n+1 : ℕ) : ℝ) * (B^(n+1) * ‖v‖) := by
        calc
          _ ≤ ∑ i ∈ Finset.range (n+1), ‖A i * solutionCoeff A v (n-i)‖ := norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range (n+1), B^(n+1) * ‖v‖ := by
            apply Finset.sum_le_sum
            intro i hi
            have hin : i ≤ n := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            calc
              _ ≤ ‖A i‖ * ‖solutionCoeff A v (n-i)‖ := norm_mul_le _ _
              _ ≤ B^(i+1) * (B^(n-i) * ‖v‖) := by
                exact mul_le_mul (hA i) (ih _ (by omega)) (norm_nonneg _) (pow_nonneg hB.le _)
              _ = B^(n+1) * ‖v‖ := by rw [← mul_assoc,← pow_add]; congr 2; omega
          _ = _ := by simp [nsmul_eq_mul]
      calc
        _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (((n+1 : ℕ) : ℝ) * (B^(n+1) * ‖v‖)) := by gcongr
        _ = _ := by rw [inv_mul_cancel_left₀ (by positivity)]

def series (a : ℕ → R) : FormalMultilinearSeries ℂ ℂ R :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

omit [CompleteSpace R] in
@[simp] lemma series_coeff (a : ℕ → R) (n : ℕ) : (series a).coeff n = a n := by
  simp [series,FormalMultilinearSeries.coeff,ContinuousMultilinearMap.mkPiRing_apply]

omit [CompleteSpace R] in
lemma series_radius {a : ℕ → R} {B C : ℝ} (hB : 0 < B)
    (ha : ∀ n, ‖a n‖ ≤ B^n*C) :
    (ENNReal.ofReal B⁻¹) ≤ (series a).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hB.le)]
  apply (series a).le_radius_of_bound C (r := ⟨B⁻¹,inv_nonneg.mpr hB.le⟩)
  intro n
  simp only [series,ContinuousMultilinearMap.norm_mkPiRing]
  change ‖a n‖ * (B⁻¹)^n ≤ C
  calc
    _ ≤ (B^n*C)*(B⁻¹)^n := mul_le_mul_of_nonneg_right (ha n) (by positivity)
    _ = (B^n*(B⁻¹)^n)*C := by ring
    _ = C := by rw [← mul_pow,mul_inv_cancel₀ hB.ne',one_pow,one_mul]

omit [CompleteSpace R] in
lemma solutionSeries_pos {A : ℕ → R} (v : R) {B : ℝ} (hB : 0 < B)
    (hA : ∀ n, ‖A n‖ ≤ B^(n+1)) :
    0 < (series (solutionCoeff A v)).radius :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr hB))
    (series_radius hB (solutionCoeff_norm v hB hA))

omit [CompleteSpace R] in
lemma cauchy_eval (a b : ℕ → R) (z : ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), (z^i • a i) * (z^(n-i) • b (n-i))) =
      z^n • ∑ i ∈ Finset.range (n+1), a i * b (n-i) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_mul_smul,← pow_add]
  congr 2
  have : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  omega

lemma hasDerivAt_solutionSeries {A : ℕ → R} (v : R) {B : ℝ} (hB : 0 < B)
    (hA : ∀ n, ‖A n‖ ≤ B^(n+1)) {z : ℂ}
    (hzA : ‖z‖ₑ < (series A).radius)
    (hzY : ‖z‖ₑ < (series (solutionCoeff A v)).radius) :
    HasDerivAt (series (solutionCoeff A v)).sum
      ((series A).sum z * (series (solutionCoeff A v)).sum z) z := by
  let p := series (solutionCoeff A v)
  have hp : 0 < p.radius := solutionSeries_pos v hB hA
  have hzY' : z ∈ Metric.eball 0 p.radius := by simpa using hzY
  have hzA' : z ∈ Metric.eball 0 (series A).radius := by simpa using hzA
  have hD := (ContinuousLinearMap.apply ℂ R 1).hasSum
    ((p.hasFPowerSeriesOnBall hp).fderiv.hasSum hzY')
  have hprod := hasSum_sum_range_mul_of_summable_norm
    ((series A).summable_norm_apply hzA') (p.summable_norm_apply hzY')
  have he : (fun n => (ContinuousLinearMap.apply ℂ R 1)
      (p.derivSeries n fun _ => z)) =
      (fun n => ∑ i ∈ Finset.range (n+1),
        ((series A) i fun _ => z) * (p (n-i) fun _ => z)) := by
    funext n
    simp only [ContinuousLinearMap.apply_apply,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_apply,FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [p,series_coeff]
    rw [cauchy_eval,← Nat.cast_smul_eq_nsmul ℂ,solutionCoeff_recurrence]
  rw [← he] at hprod
  have hdval := hD.unique hprod
  simp only [zero_add,ContinuousLinearMap.apply_apply] at hdval
  rw [(series A).hasSum hzA' |>.tsum_eq,p.hasSum hzY' |>.tsum_eq] at hdval
  have hder := ((p.hasFPowerSeriesOnBall hp).analyticAt_of_mem hzY').differentiableAt.hasFDerivAt.hasDerivAt
  rw [hdval] at hder
  exact hder

omit [CompleteSpace R] in
lemma coeff_bound {p : FormalMultilinearSeries ℂ ℂ R} (hp : 0 < p.radius) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, ‖p.coeff n‖ ≤ B^(n+1) := by
  obtain ⟨r,hr0,hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hr : 0 < r := by exact_mod_cast hr0
  obtain ⟨C,hC,hCp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr hrp
  let B := max C (r : ℝ)⁻¹
  have hCB : C ≤ B := le_max_left _ _
  have hrB : (r : ℝ)⁻¹ ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le hC hCB
  refine ⟨B,hB,fun n => ?_⟩
  calc
    ‖p.coeff n‖ = ‖p n‖ := (p.norm_apply_eq_norm_coef).symm
    _ ≤ C / (r : ℝ)^n := hCp n
    _ = C * ((r : ℝ)⁻¹)^n := by rw [div_eq_mul_inv,inv_pow]
    _ ≤ B * B^n := mul_le_mul hCB (pow_le_pow_left₀ (by positivity) hrB n)
      (by positivity) hB.le
    _ = B^(n+1) := by rw [pow_succ,mul_comm]

omit [CompleteSpace R] in
@[simp] lemma series_of_coeff (p : FormalMultilinearSeries ℂ ℂ R) :
    series p.coeff = p := by
  funext n
  exact p.mkPiRing_coeff_eq n

lemma exists_local_solution {A : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x) (v : R) :
    ∃ Y : ℂ → R, AnalyticAt ℂ Y x ∧ Y x = v ∧
      ∀ᶠ z in 𝓝 x, HasDerivAt Y (A z * Y z) z := by
  obtain ⟨p,r,hp⟩ := hA
  obtain ⟨B,hB,hbound⟩ := coeff_bound (hp.r_pos.trans_le hp.r_le)
  let q := series (solutionCoeff p.coeff v)
  have hq : 0 < q.radius := solutionSeries_pos v hB hbound
  let Y : ℂ → R := fun z => q.sum (z-x)
  have hqA : AnalyticAt ℂ q.sum 0 := (q.hasFPowerSeriesOnBall hq).analyticAt
  refine ⟨Y,?_,?_,?_⟩
  · simpa [Y] using hqA.comp_sub x
  · change q.sum (x-x) = v
    rw [sub_self,← (q.hasFPowerSeriesOnBall hq).coeff_zero (fun _ => 1)]
    simp [q,series,ContinuousMultilinearMap.mkPiRing_apply,solutionCoeff]
  · have hrN : ∀ᶠ z in 𝓝 x, z ∈ Metric.eball x r := Metric.eball_mem_nhds x hp.r_pos
    have hqN : ∀ᶠ z in 𝓝 x, z ∈ Metric.eball x q.radius := Metric.eball_mem_nhds x hq
    filter_upwards [hrN,hqN] with z hzr hzq
    have hzr' : z-x ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hzr
    have hzq' : ‖z-x‖ₑ < q.radius := by simpa [edist_eq_enorm_sub] using hzq
    have hzp : ‖z-x‖ₑ < (series p.coeff).radius := by
      simpa using (show ‖z-x‖ₑ < r by simpa using hzr').trans_le hp.r_le
    have hder := hasDerivAt_solutionSeries v hB hbound hzp hzq'
    have heA : (series p.coeff).sum (z-x) = A z := by
      rw [series_of_coeff,← hp.sum hzr',add_sub_cancel]
    rw [heA] at hder
    simpa [Y,Function.comp_def] using hder.scomp z ((hasDerivAt_id z).sub_const x)

lemma inverse_mul_horizontal {Y Z : ℂ → R} {A : R} {z : ℂ}
    (hY : HasDerivAt Y (A * Y z) z) (hZ : HasDerivAt Z (A * Z z) z)
    (hu : IsUnit (Y z)) :
    HasDerivAt (fun w => Ring.inverse (Y w) * Z w) 0 z := by
  obtain ⟨u,he⟩ := hu
  have hi : HasDerivAt (fun w => Ring.inverse (Y w))
      (-(Ring.inverse (Y z) * (A * Y z) * Ring.inverse (Y z))) z := by
    have h := (hasFDerivAt_ringInverse (𝕜 := ℂ) u)
    rw [he] at h
    convert! h.comp_hasDerivAt z hY using 1; try rfl
    simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply]
    rw [← Ring.inverse_unit u,he]
  convert! hi.mul hZ using 1; try rfl
  have hc : Y z * Ring.inverse (Y z) = 1 := Ring.mul_inverse_cancel _ ⟨u,he⟩
  simp only [neg_mul,mul_assoc,hc,mul_one,neg_add_cancel]

lemma exists_local_fundamental {A : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x) :
    ∃ Y : ℂ → R, AnalyticAt ℂ Y x ∧ Y x = 1 ∧
      ∀ᶠ z in 𝓝 x, HasDerivAt Y (A z * Y z) z ∧ IsUnit (Y z) := by
  obtain ⟨Y,hYa,hY0,hYd⟩ := exists_local_solution hA 1
  refine ⟨Y,hYa,hY0,hYd.and ?_⟩
  have hn : {a : R | IsUnit a} ∈ 𝓝 (Y x) :=
    Units.isOpen.mem_nhds (hY0 ▸ isUnit_one)
  exact hYa.continuousAt.eventually hn

lemma local_uniqueness {A f g : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x)
    (hf : ∀ᶠ z in 𝓝 x, HasDerivAt f (A z * f z) z)
    (hg : ∀ᶠ z in 𝓝 x, HasDerivAt g (A z * g z) z)
    (he : f x = g x) : f =ᶠ[𝓝 x] g := by
  obtain ⟨Y,hYa,hY0,hY⟩ := exists_local_fundamental hA
  obtain ⟨ε,hε,hs⟩ := Metric.eventually_nhds_iff_ball.mp (hY.and (hf.and hg))
  let D : ℂ → R := fun z => Ring.inverse (Y z) * (f z-g z)
  have hd (z : ℂ) (hz : z ∈ Metric.ball x ε) : HasDerivAt D 0 z := by
    have hsub : HasDerivAt (fun w => f w-g w) (A z * (f z-g z)) z := by
      convert! (hs z hz).2.1.sub (hs z hz).2.2 using 1; try rfl
      exact mul_sub _ _ _
    exact inverse_mul_horizontal (hs z hz).1.1 hsub (hs z hz).1.2
  filter_upwards [Metric.ball_mem_nhds x hε] with z hz
  have hc : D z = D x := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball x ε).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hε)
  have hmul := congrArg (fun a => Y z*a) hc
  have hcancel := Ring.mul_inverse_cancel (Y z) (hs z hz).1.2
  have hz0 : f z-g z = 0 := by
    simpa only [D,he,sub_self,mul_zero,← mul_assoc,hcancel,one_mul] using hmul
  exact sub_eq_zero.mp hz0

 

def transport (Y : ℂ → R) (s t : ℂ) : R := Y t * Ring.inverse (Y s)

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_self {Y : ℂ → R} {s : ℂ} (hs : IsUnit (Y s)) :
    transport Y s s = 1 := Ring.mul_inverse_cancel _ hs

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_trans {Y : ℂ → R} {s t u : ℂ} (ht : IsUnit (Y t)) :
    transport Y t u * transport Y s t = transport Y s u := by
  simp only [transport, mul_assoc, ← mul_assoc (Ring.inverse (Y t)),
    Ring.inverse_mul_cancel _ ht, one_mul]

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_isUnit {Y : ℂ → R} {s t : ℂ}
    (hs : IsUnit (Y s)) (ht : IsUnit (Y t)) : IsUnit (transport Y s t) := by
  obtain ⟨u,hu⟩ := hs
  rw [transport, ← hu, Ring.inverse_unit]
  exact ht.mul (Units.isUnit _)

lemma transport_analyticAt {Y : ℂ → R} {s t : ℂ}
    (hs : AnalyticAt ℂ Y s) (ht : AnalyticAt ℂ Y t) (hu : IsUnit (Y s)) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => transport Y w.1 w.2) (s,t) := by
  have hf : AnalyticAt ℂ (fun w : ℂ × ℂ => Y w.1) (s,t) := hs.comp analyticAt_fst
  have hg : AnalyticAt ℂ (fun w : ℂ × ℂ => Y w.2) (s,t) := ht.comp analyticAt_snd
  have hi : AnalyticAt ℂ (fun w : ℂ × ℂ => Ring.inverse (Y w.1)) (s,t) :=
    (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp_of_eq hf rfl
  exact hg.mul hi

omit [CompleteSpace R] in
lemma transport_hasDerivAt {A Y : ℂ → R} {s t : ℂ}
    (ht : HasDerivAt Y (A t * Y t) t) :
    HasDerivAt (transport Y s) (A t * transport Y s t) t := by
  convert! ht.mul_const (Ring.inverse (Y s)) using 1; try rfl
  exact (mul_assoc _ _ _).symm

 

theorem exists_local_transport {A : ℂ → R} {x : ℂ} (hA : AnalyticAt ℂ A x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → R,
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2)
        (Metric.ball x ε ×ˢ Metric.ball x ε) ∧
      (∀ s ∈ Metric.ball x ε, T s s = 1) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, IsUnit (T s t)) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ u ∈ Metric.ball x ε,
        T t u * T s t = T s u) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε,
        HasDerivAt (T s) (A t * T s t) t) := by
  obtain ⟨Y,hYa,hY0,hY⟩ := exists_local_fundamental hA
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff_ball.mp (hYa.eventually_analyticAt.and hY)
  refine ⟨ε,hε,transport Y,?_,?_,?_,?_,?_⟩
  · intro w hw
    exact transport_analyticAt (he w.1 hw.1).1 (he w.2 hw.2).1 (he w.1 hw.1).2.2
  · intro s hs; exact transport_self (he s hs).2.2
  · intro s hs t ht; exact transport_isUnit (he s hs).2.2 (he t ht).2.2
  · intro s hs t ht u hu; exact transport_trans (he t ht).2.2
  · intro s hs t ht; exact transport_hasDerivAt (he t ht).2.1

 
theorem eqOn_of_solution {A f g : ℂ → R} {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hA : AnalyticOnNhd ℂ A U)
    (hf : ∀ z ∈ U, HasDerivAt f (A z * f z) z)
    (hg : ∀ z ∈ U, HasDerivAt g (A z * g z) z)
    {x : ℂ} (hx : x ∈ U) (he : f x = g x) : EqOn f g U := by
  have hfa : AnalyticOnNhd ℂ f U :=
    (show DifferentiableOn ℂ f U from fun z hz => (hf z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  have hga : AnalyticOnNhd ℂ g U :=
    (show DifferentiableOn ℂ g U from fun z hz => (hg z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  apply hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc hx
  apply local_uniqueness (hA x hx) _ _ he
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => hf z hz)
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => hg z hz)

 
omit [CompleteSpace R] in
lemma gauge_hasDerivAt {A B H Y : ℂ → R} {z : ℂ}
    (hH : HasDerivAt H (B z * H z - H z * A z) z)
    (hY : HasDerivAt Y (A z * Y z) z) :
    HasDerivAt (fun w => H w * Y w) (B z * (H z * Y z)) z := by
  convert! hH.mul hY using 1; try rfl
  simp only [sub_mul,mul_assoc,sub_add_cancel]

 

lemma intertwine_eventually {A P Y : ℂ → R} {x : ℂ}
    (hA : AnalyticAt ℂ A x) (hY0 : Y x = 1)
    (hY : ∀ᶠ z in 𝓝 x, HasDerivAt Y (A z * Y z) z)
    (hP : ∀ᶠ z in 𝓝 x, HasDerivAt P (A z * P z - P z * A z) z) :
    ∀ᶠ z in 𝓝 x, P z * Y z = Y z * P x := by
  apply local_uniqueness hA
  · filter_upwards [hP,hY] with z hp hy
    exact gauge_hasDerivAt hp hy
  · filter_upwards [hY] with z hz
    convert! hz.mul_const (P x) using 1; try rfl
    exact (mul_assoc _ _ _).symm
  · simp only [hY0,mul_one,one_mul]

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma transport_intertwines {Y P : ℂ → R} {x s t : ℂ}
    (hs : P s * Y s = Y s * P x) (ht : P t * Y t = Y t * P x)
    (hu : IsUnit (Y s)) : P t * transport Y s t = transport Y s t * P s := by
  have he : P x * Ring.inverse (Y s) = Ring.inverse (Y s) * P s := by
    have h := congrArg (fun a => Ring.inverse (Y s) * a * Ring.inverse (Y s)) hs
    simpa only [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one,
      ← mul_assoc (Ring.inverse (Y s)) (Y s),Ring.inverse_mul_cancel _ hu,one_mul] using h.symm
  unfold transport
  rw [← mul_assoc, ht, mul_assoc, he, mul_assoc]


omit [CompleteSpace R] in
lemma solutionCoeff_differentiableOn {A : ℕ → ℂ → R} {U : Set ℂ}
    (hA : ∀ n, DifferentiableOn ℂ (A n) U) (v : R) (n : ℕ) :
    DifferentiableOn ℂ (fun s => solutionCoeff (fun i => A i s) v n) U := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [solutionCoeff]
    | succ n =>
      simp only [solutionCoeff]
      have hd : DifferentiableOn ℂ (fun s =>
          ∑ i ∈ Finset.range (n+1), A i s * solutionCoeff (fun i => A i s) v (n-i)) U := by
        apply DifferentiableOn.fun_sum
        intro i hi
        exact (hA i).fun_mul (ih (n-i) (by omega))
      exact hd.fun_const_smul (((n+1 : ℕ) : ℂ)⁻¹)

 

def parameterSolution (A : ℕ → ℂ → R) (v : R) (s t : ℂ) : R :=
  ∑' n, t^n • solutionCoeff (fun i => A i s) v n

 

lemma parameterSolution_differentiableOn {A : ℕ → ℂ → R} {U : Set ℂ}
    {t : ℂ → ℂ} {B r : ℝ} (hU : IsOpen U) (hB : 0 < B) (hr : 0 ≤ r)
    (hBr : r*B < 1) (hA : ∀ n, DifferentiableOn ℂ (A n) U)
    (hbound : ∀ n s, s ∈ U → ‖A n s‖ ≤ B^(n+1))
    (ht : DifferentiableOn ℂ t U) (htr : ∀ s ∈ U, ‖t s‖ ≤ r) (v : R) :
    DifferentiableOn ℂ (fun s => parameterSolution A v s (t s)) U := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one (mul_nonneg hr hB.le) hBr).mul_right ‖v‖)
    (fun n => (ht.pow n).smul (solutionCoeff_differentiableOn hA v n)) hU
  intro n s hs
  change ‖t s ^ n • solutionCoeff (fun i => A i s) v n‖ ≤ (r*B)^n * ‖v‖
  rw [norm_smul,norm_pow]
  calc
    ‖t s‖^n * ‖solutionCoeff (fun i => A i s) v n‖ ≤
        r^n * (B^n * ‖v‖) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (htr s hs) n)
        (solutionCoeff_norm v hB (fun i => hbound i s hs) n)
        (norm_nonneg _) (pow_nonneg hr _)
    _ = (r*B)^n * ‖v‖ := by rw [mul_pow]; ring

lemma parameterSolution_analyticAt {A : ℕ → ℂ → R} {U : Set ℂ}
    {t : ℂ → ℂ} {B r : ℝ} (hU : IsOpen U) (hB : 0 < B) (hr : 0 ≤ r)
    (hBr : r*B < 1) (hA : ∀ n, DifferentiableOn ℂ (A n) U)
    (hbound : ∀ n s, s ∈ U → ‖A n s‖ ≤ B^(n+1))
    (ht : DifferentiableOn ℂ t U) (htr : ∀ s ∈ U, ‖t s‖ ≤ r)
    (v : R) {s : ℂ} (hs : s ∈ U) :
    AnalyticAt ℂ (fun s => parameterSolution A v s (t s)) s :=
  (parameterSolution_differentiableOn hU hB hr hBr hA hbound ht htr v).analyticAt
    (hU.mem_nhds hs)

omit [CompleteSpace R] in
@[simp] lemma parameterSolution_zero (A : ℕ → ℂ → R) (v : R) (s : ℂ) :
    parameterSolution A v s 0 = v := by
  rw [parameterSolution,tsum_eq_single 0]
  · simp [solutionCoeff]
  · intro n hn
    simp [zero_pow hn]

omit [CompleteSpace R] in
lemma parameterSolution_eq_series_sum (A : ℕ → ℂ → R) (v : R) (s t : ℂ) :
    parameterSolution A v s t = (series (solutionCoeff (fun i => A i s) v)).sum t := by
  simp only [parameterSolution,FormalMultilinearSeries.sum,series,
    ContinuousMultilinearMap.mkPiRing_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma parameterSolution_hasDerivAt {A : ℕ → ℂ → R} {B : ℝ} (hB : 0 < B)
    {s t : ℂ} (hbound : ∀ n, ‖A n s‖ ≤ B^(n+1)) (ht : ‖t‖ < B⁻¹) (v : R) :
    HasDerivAt (parameterSolution A v s)
      ((series (fun i => A i s)).sum t * parameterSolution A v s t) t := by
  have hradA : ENNReal.ofReal B⁻¹ ≤ (series (fun i => A i s)).radius :=
    series_radius hB (fun n => by simpa [pow_succ] using hbound n)
  have hradY : ENNReal.ofReal B⁻¹ ≤ (series (solutionCoeff (fun i => A i s) v)).radius :=
    series_radius hB (solutionCoeff_norm v hB hbound)
  have hte : ‖t‖ₑ < ENNReal.ofReal B⁻¹ := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hB) |>.mpr ht
  have he : parameterSolution A v s = (series (solutionCoeff (fun i => A i s) v)).sum :=
    funext (parameterSolution_eq_series_sum A v s)
  rw [he]
  exact
    hasDerivAt_solutionSeries v hB hbound (hte.trans_le hradA) (hte.trans_le hradY)


omit [CompleteSpace R] in
lemma changeOriginSeries_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ E R) (n l : ℕ) :
    ‖p.changeOriginSeries n l‖ ≤ (2 : ℝ)^(n+l) * ‖p (n+l)‖ := by
  have hc : Fintype.card {s : Finset (Fin (n+l)) // s.card=l} ≤ 2^(n+l) := by
    simpa only [Fintype.card_finset,Fintype.card_fin] using
      (Fintype.card_subtype_le (fun s : Finset (Fin (n+l)) => s.card=l))
  have hn := p.nnnorm_changeOriginSeries_le_tsum n l
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hn
  calc
    ‖p.changeOriginSeries n l‖ ≤
        (Fintype.card {s : Finset (Fin (n+l)) // s.card=l} : ℝ) * ‖p (n+l)‖ := by
      exact_mod_cast hn
    _ ≤ (2 : ℝ)^(n+l) * ‖p (n+l)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast hc

omit [CompleteSpace R] in
lemma changeOrigin_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : FormalMultilinearSeries ℂ E R} {D C : ℝ} (hD : 0 < D) (hC : 0 ≤ C)
    (hp : ∀ n, ‖p n‖ ≤ C*D^n) {x : E} (hx : ‖x‖ ≤ (4*D)⁻¹) (n : ℕ) :
    ‖p.changeOrigin x n‖ ≤ (2*C) * (2*D)^n := by
  have hterm (l : ℕ) : ‖p.changeOriginSeries n l (fun _ => x)‖ ≤
      (C*(2*D)^n) * ((1/2 : ℝ)^l) := by
    calc
      _ ≤ ‖p.changeOriginSeries n l‖ * ‖x‖^l := by
        simpa using (p.changeOriginSeries n l).le_opNorm (fun _ => x)
      _ ≤ ((2 : ℝ)^(n+l) * (C*D^(n+l))) * ((4*D)⁻¹)^l := by
        apply mul_le_mul
        · exact (changeOriginSeries_norm_bound p n l).trans
            (mul_le_mul_of_nonneg_left (hp (n+l)) (by positivity))
        · exact pow_le_pow_left₀ (norm_nonneg _) hx l
        · positivity
        · positivity
      _ = (C*(2*D)^n) * ((1/2 : ℝ)^l) := by
        have he0 : (2 : ℝ)^(n+l) * (C*D^(n+l)) = C*((2*D)^(n+l)) := by
          rw [mul_pow]; ring
        rw [he0,pow_add]
        have he : (2*D) * (4*D)⁻¹ = (1/2 : ℝ) := by field_simp [hD.ne']; ring
        rw [show C * ((2*D)^n * (2*D)^l) * ((4*D)⁻¹)^l =
          (C*(2*D)^n) * (((2*D)*((4*D)⁻¹))^l) by rw [mul_pow (2*D) ((4*D)⁻¹) l]; ring]
        rw [he]
  have hs : Summable (fun l : ℕ => (C*(2*D)^n) * (1/2 : ℝ)^l) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  calc
    _ ≤ ∑' l : ℕ, (C*(2*D)^n) * (1/2 : ℝ)^l := by
      exact tsum_of_norm_bounded hs.hasSum hterm
    _ = (2*C) * (2*D)^n := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)]
      ring

 

def verticalCoeff (p : FormalMultilinearSeries ℂ (ℂ × ℂ) R) (n : ℕ) (s : ℂ) : R :=
  p.changeOrigin (s,0) n (fun _ => (0,1))

lemma verticalCoeff_differentiableAt {p : FormalMultilinearSeries ℂ (ℂ × ℂ) R}
    (hp : 0 < p.radius) (n : ℕ) {s : ℂ} (hs : ‖s‖ₑ < p.radius) :
    DifferentiableAt ℂ (verticalCoeff p n) s := by
  have hs' : (s, (0:ℂ)) ∈ Metric.eball 0 p.radius := by
    rw [Metric.mem_eball,edist_eq_enorm_sub,sub_zero,← ofReal_norm]
    simpa using hs
  have hc := (p.hasFPowerSeriesOnBall_changeOrigin n hp).analyticAt_of_mem hs'
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ × ℂ) R
    (fun _ => (0,1))).differentiableAt.comp s
      (hc.differentiableAt.comp s (differentiableAt_id.prodMk (differentiableAt_const (0:ℂ))))

omit [CompleteSpace R] in
lemma verticalCoeff_bound {p : FormalMultilinearSeries ℂ (ℂ × ℂ) R}
    {D C : ℝ} (hD : 0 < D) (hC : 0 ≤ C) (hp : ∀ n, ‖p n‖ ≤ C*D^n)
    {s : ℂ} (hs : ‖s‖ ≤ (4*D)⁻¹) (n : ℕ) :
    ‖verticalCoeff p n s‖ ≤ (2*C) * (2*D)^n := by
  have he : ‖verticalCoeff p n s‖ ≤ ‖p.changeOrigin (s,0) n‖ := by
    simpa [verticalCoeff] using
      (p.changeOrigin (s,0) n).le_opNorm (fun _ => ((0:ℂ),(1:ℂ)))
  exact he.trans (changeOrigin_norm_bound hD hC hp (by simpa using hs) n)

omit [CompleteSpace R] in
lemma verticalCoeff_sum (p : FormalMultilinearSeries ℂ (ℂ × ℂ) R) (s t : ℂ) :
    (series (fun n => verticalCoeff p n s)).sum t = (p.changeOrigin (s,0)).sum (0,t) := by
  unfold FormalMultilinearSeries.sum
  apply tsum_congr
  intro n
  simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,series_coeff,verticalCoeff]
  convert! ((p.changeOrigin (s,0) n).map_smul_univ (fun _ => t) (fun _ => ((0:ℂ),(1:ℂ)))).symm using 1 <;> simp


lemma analytic_coefficient_polydisk {A : ℂ × ℂ → R} (hA : AnalyticAt ℂ A (0,0)) :
    ∃ (c : ℕ → ℂ → R) (δ B : ℝ), 0 < δ ∧ 0 < B ∧ δ*B < 1 ∧
      (∀ n, DifferentiableOn ℂ (c n) (Metric.ball 0 δ)) ∧
      (∀ n s, ‖s‖ < δ → ‖c n s‖ ≤ B^(n+1)) ∧
      (∀ s t, ‖s‖ < δ → ‖t‖ < δ → (series (fun n => c n s)).sum t = A (s,t)) := by
  obtain ⟨p,ρ,hp⟩ := hA
  obtain ⟨r,hr0,hrρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hr : 0 < r := by exact_mod_cast hr0
  have hrr : (0 : ℝ) < r := hr
  have hrp : (r : ENNReal) < p.radius := hrρ.trans_le hp.r_le
  obtain ⟨C,hC,hCp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr hrp
  let D : ℝ := (r : ℝ)⁻¹
  have hD : 0 < D := inv_pos.mpr hrr
  have hpd (n : ℕ) : ‖p n‖ ≤ C*D^n := by
    simpa [D,div_eq_mul_inv,inv_pow] using hCp n
  let B := max (2*C) (2*D)
  have hCB : 2*C ≤ B := le_max_left _ _
  have hDB : 2*D ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hCB
  let δ := min ((4*D)⁻¹) (min ((r:ℝ)/3) (B⁻¹/2))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδD : δ ≤ (4*D)⁻¹ := min_le_left _ _
  have hδr : δ ≤ (r:ℝ)/3 := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ B⁻¹/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδBr : δ*B < 1 := by
    calc
      δ*B ≤ (B⁻¹/2)*B := mul_le_mul_of_nonneg_right hδB hB.le
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  have hsr (s : ℂ) (hs : ‖s‖ < δ) : ‖s‖ < (r:ℝ) := by linarith
  have hse (s : ℂ) (hs : ‖s‖ < δ) : ‖s‖ₑ < (r:ENNReal) := by exact_mod_cast hsr s hs
  refine ⟨verticalCoeff p,δ,B,hδ,hB,hδBr,?_,?_,?_⟩
  · intro n s hs
    apply (verticalCoeff_differentiableAt (hp.r_pos.trans_le hp.r_le) n
      ((hse s (by simpa using hs)).trans hrp)).differentiableWithinAt
  · intro n s hs
    calc
      ‖verticalCoeff p n s‖ ≤ (2*C)*(2*D)^n := verticalCoeff_bound hD hC.le hpd (hs.le.trans hδD) n
      _ ≤ B*B^n := mul_le_mul hCB (pow_le_pow_left₀ (by positivity) hDB n) (by positivity) hB.le
      _ = B^(n+1) := by rw [pow_succ,mul_comm]
  · intro s t hs ht
    rw [verticalCoeff_sum]
    have hsum : ‖s‖ + ‖t‖ < (r:ℝ) := by linarith
    have hsum' : (‖(s,(0:ℂ))‖₊ + ‖((0:ℂ),t)‖₊ : ENNReal) < (r:ENNReal) := by
      simp only [Prod.nnnorm_def,nnnorm_zero,max_eq_left (show (0:NNReal) ≤ ‖s‖₊ from zero_le),max_eq_right (show (0:NNReal) ≤ ‖t‖₊ from zero_le)]
      exact_mod_cast hsum
    rw [p.changeOrigin_eval (hsum'.trans hrp)]
    have hmem : (s,t) ∈ Metric.eball (0:ℂ × ℂ) ρ := by
      rw [Metric.mem_eball,edist_eq_enorm_sub,sub_zero,← ofReal_norm]
      apply lt_trans _ hrρ
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_lt_ofReal_iff hrr |>.mpr
      exact max_lt (hsr s hs) (hsr t ht)
    simpa using (hp.sum hmem).symm

lemma parameterSolution_continuousOn {c : ℕ → ℂ → R} {U : Set ℂ}
    {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hrB : r*B < 1)
    (hc : ∀ n, ContinuousOn (c n) U)
    (hbound : ∀ n s, s ∈ U → ‖c n s‖ ≤ B^(n+1)) (v : R) :
    ContinuousOn (fun w : ℂ × ℂ => parameterSolution c v w.1 w.2)
      (U ×ˢ Metric.closedBall 0 r) := by
  refine continuousOn_tsum (fun n => ?_)
    ((summable_geometric_of_lt_one (mul_nonneg hr hB.le) hrB).mul_right ‖v‖) ?_
  · have hsc (n : ℕ) : ContinuousOn (fun s => solutionCoeff (fun i => c i s) v n) U := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => simpa [solutionCoeff] using (continuousOn_const (c := v) (s := U))
        | succ n =>
          simp only [solutionCoeff]
          apply ContinuousOn.const_smul
          apply continuousOn_finsetSum
          intro i hi
          exact (hc i).mul (ih (n-i) (by omega))
    exact (continuousOn_snd.pow n).smul ((hsc n).comp continuousOn_fst (fun _ hw => hw.1))
  · intro n w hw
    change ‖w.2^n • solutionCoeff (fun i => c i w.1) v n‖ ≤ (r*B)^n * ‖v‖
    rw [norm_smul,norm_pow]
    have hwr : ‖w.2‖ ≤ r := by simpa using hw.2
    calc
      _ ≤ r^n * (B^n*‖v‖) := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hwr n)
        (solutionCoeff_norm v hB (fun i => hbound i w.1 hw.1) n)
        (norm_nonneg _) (pow_nonneg hr _)
      _ = _ := by rw [mul_pow]; ring



lemma parameterSolution_analyticAt_curves {c : ℕ → ℂ → R} {δ B : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hδB : δ*B < 1)
    (hc : ∀ n, DifferentiableOn ℂ (c n) (Metric.ball 0 δ))
    (hbound : ∀ n s, ‖s‖ < δ → ‖c n s‖ ≤ B^(n+1))
    {q t : ℂ → ℂ} {z : ℂ} (hq : AnalyticAt ℂ q z) (ht : AnalyticAt ℂ t z)
    (hqδ : ‖q z‖ < δ) (htδ : ‖t z‖ < δ) (v : R) :
    AnalyticAt ℂ (fun w => parameterSolution c v (q w) (t w)) z := by
  have hqb' : ∀ᶠ w in 𝓝 z, q w ∈ Metric.ball 0 δ :=
    hq.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqδ))
  have htb' : ∀ᶠ w in 𝓝 z, t w ∈ Metric.ball 0 δ :=
    ht.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr htδ))
  have hqb : ∀ᶠ w in 𝓝 z, ‖q w‖ < δ := hqb'.mono (fun _ hw => mem_ball_zero_iff.mp hw)
  have htb : ∀ᶠ w in 𝓝 z, ‖t w‖ < δ := htb'.mono (fun _ hw => mem_ball_zero_iff.mp hw)
  obtain ⟨η,hη,he⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hq.eventually_analyticAt.and ht.eventually_analyticAt).and (hqb.and htb))
  have hqd : DifferentiableOn ℂ q (Metric.ball z η) := fun w hw =>
    (he w hw).1.1.differentiableAt.differentiableWithinAt
  have htd : DifferentiableOn ℂ t (Metric.ball z η) := fun w hw =>
    (he w hw).1.2.differentiableAt.differentiableWithinAt
  have hcd (n : ℕ) : DifferentiableOn ℂ (fun w => c n (q w)) (Metric.ball z η) :=
    (hc n).comp hqd (fun w hw => by simpa using (he w hw).2.1)
  exact parameterSolution_analyticAt Metric.isOpen_ball hB hδ.le hδB hcd
    (fun n w hw => hbound n (q w) (he w hw).2.1) htd
    (fun w hw => (he w hw).2.2.le) v (Metric.mem_ball_self hη)

 

lemma exists_parameter_fundamental {A : ℂ × ℂ → R} (hA : AnalyticAt ℂ A (0,0)) :
    ∃ (Y : ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s, Y s 0 = 1) ∧
      (∀ s t, ‖s‖ < ε → ‖t‖ < ε →
        HasDerivAt (Y s) (A (s,t)*Y s t) t ∧ IsUnit (Y s t)) ∧
      (∀ (q t : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ t z →
        ‖q z‖ < ε → ‖t z‖ < ε → AnalyticAt ℂ (fun w => Y (q w) (t w)) z) := by
  obtain ⟨c,δ,B,hδ,hB,hδB,hc,hbound,hsum⟩ := analytic_coefficient_polydisk hA
  let Y := parameterSolution c (1:R)
  have hYc : ContinuousAt (fun w : ℂ × ℂ => Y w.1 w.2) (0,0) := by
    apply (parameterSolution_continuousOn hB hδ.le hδB
      (fun n => (hc n).continuousOn) (fun n s hs => hbound n s (by simpa using hs)) 1).continuousAt
    exact prod_mem_nhds (Metric.ball_mem_nhds 0 hδ) (Metric.closedBall_mem_nhds 0 hδ)
  have hYu : ∀ᶠ w : ℂ × ℂ in 𝓝 (0,0), IsUnit (Y w.1 w.2) := by
    apply hYc.eventually
    have hy0 : Y 0 0 = 1 := parameterSolution_zero c 1 0
    apply Units.isOpen.mem_nhds
    change IsUnit (Y 0 0)
    rw [hy0]
    exact isUnit_one
  obtain ⟨η,hη,hηu⟩ := Metric.eventually_nhds_iff_ball.mp hYu
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  refine ⟨Y,ε,hε,parameterSolution_zero c 1,?_,?_⟩
  · intro s t hs ht
    constructor
    · have htB : ‖t‖ < B⁻¹ := by
        have hdB : δ < B⁻¹ := by
          apply (mul_lt_mul_iff_left₀ hB).mp
          rw [inv_mul_cancel₀ hB.ne']
          simpa [mul_comm] using hδB
        exact (ht.trans_le hεδ).trans hdB
      have hd := parameterSolution_hasDerivAt hB (fun n => hbound n s (hs.trans_le hεδ)) htB (1:R)
      rw [hsum s t (hs.trans_le hεδ) (ht.trans_le hεδ)] at hd
      exact hd
    · apply hηu (s,t)
      simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
      exact max_lt (hs.trans_le hεη) (ht.trans_le hεη)
  · intro q t z hq ht hqε htε
    exact parameterSolution_analyticAt_curves hδ hB hδB hc hbound hq ht
      (hqε.trans_le hεδ) (htε.trans_le hεδ) 1



 

theorem exists_parameter_transport {A : ℂ × ℂ → R} (hA : AnalyticAt ℂ A (0,0)) :
    ∃ (T : ℂ → ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s u, ‖s‖ < ε → ‖u‖ < ε → T s u u = 1) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → IsUnit (T s u v)) ∧
      (∀ s u v w, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ‖w‖ < ε →
        T s v w * T s u v = T s u w) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε →
        HasDerivAt (T s u) (A (s,v)*T s u v) v) ∧
      (∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
        ‖q z‖ < ε → ‖u z‖ < ε → ‖v z‖ < ε →
        AnalyticAt ℂ (fun w => T (q w) (u w) (v w)) z) := by
  obtain ⟨Y,ε,hε,hY0,hYd,hYa⟩ := exists_parameter_fundamental hA
  refine ⟨fun s => transport (Y s),ε,hε,?_,?_,?_,?_,?_⟩
  · intro s u hs hu
    exact transport_self (hYd s u hs hu).2
  · intro s u v hs hu hv
    exact transport_isUnit (hYd s u hs hu).2 (hYd s v hs hv).2
  · intro s u v w hs hu hv hw
    exact transport_trans (hYd s v hs hv).2
  · intro s u v hs hu hv
    exact transport_hasDerivAt (A := fun t => A (s,t)) (hYd s v hs hv).1
  · intro q u v z hq hu hv hqs hus hvs
    have hsu := hYa q u z hq hu hqs hus
    have hsv := hYa q v z hq hv hqs hvs
    exact hsv.mul ((analyticOnNhd_inverse (𝕜 := ℂ) _ (hYd (q z) (u z) hqs hus).2).comp_of_eq hsu rfl)

end

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
lemma idempotent_derivative {P : ℂ → R} {P' : R} {z : ℂ}
    (hP : HasDerivAt P P' z) (hid : ∀ᶠ w in 𝓝 z, P w * P w = P w) :
    P' * P z + P z * P' = P' := by
  exact (hP.mul hP).unique (hP.congr_of_eventuallyEq hid)

omit [NormedAlgebra ℂ R] [CompleteSpace R] in
lemma projector_derivative_sandwich {p q : R} (hp : p*p=p)
    (hq : q*p+p*q=q) : p*q*p=0 := by
  have hh := congrArg (fun a => p*a) hq
  have he : p*q*p+p*q=p*q := by
    simpa only [mul_add,← mul_assoc,hp] using hh
  exact add_eq_right.mp he

 

def projectorODE (P B : ℂ → R) (z : ℂ) : R :=
  deriv P z * P z - P z * deriv P z - P z * B z * P z

omit [CompleteSpace R] in
lemma projectorODE_commutator {P B : ℂ → R} {z : ℂ}
    (hP : DifferentiableAt ℂ P z) (hid : ∀ᶠ w in 𝓝 z, P w*P w=P w) :
    projectorODE P B z * P z - P z * projectorODE P B z = deriv P z := by
  have hh := idempotent_derivative hP.hasDerivAt hid
  have hp := hid.self_of_nhds
  have hz := projector_derivative_sandwich hp hh
  calc
    projectorODE P B z * P z - P z * projectorODE P B z =
      deriv P z * (P z*P z) + (P z*P z)*deriv P z -
      (P z*deriv P z*P z+P z*deriv P z*P z) -
      P z*B z*(P z*P z)+(P z*P z)*B z*P z := by
        unfold projectorODE
        noncomm_ring
    _ = deriv P z := by rw [hp,hz,add_zero,sub_zero,sub_add_cancel,hh]

lemma projectorODE_analyticAt {P B : ℂ → R} {z : ℂ}
    (hP : AnalyticAt ℂ P z) (hB : AnalyticAt ℂ B z) :
    AnalyticAt ℂ (projectorODE P B) z :=
  ((hP.deriv.mul hP).sub (hP.mul hP.deriv)).sub ((hP.mul hB).mul hP)

 

theorem exists_local_projector_transport {P B : ℂ → R} {x : ℂ}
    (hP : AnalyticAt ℂ P x) (hB : AnalyticAt ℂ B x)
    (hid : ∀ᶠ z in 𝓝 x, P z*P z=P z) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → R,
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2)
        (Metric.ball x ε ×ˢ Metric.ball x ε) ∧
      (∀ s ∈ Metric.ball x ε, T s s=1) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, IsUnit (T s t)) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ u ∈ Metric.ball x ε,
        T t u*T s t=T s u) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε,
        HasDerivAt (T s) (projectorODE P B t * T s t) t) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε,
        P t*T s t=T s t*P s) := by
  have hA := projectorODE_analyticAt hP hB
  obtain ⟨Y,hYa,hYx,hY⟩ := exists_local_fundamental hA
  have hpd : ∀ᶠ z in 𝓝 x, HasDerivAt P
      (projectorODE P B z * P z-P z*projectorODE P B z) z := by
    filter_upwards [hP.eventually_analyticAt,eventually_eventually_nhds.mpr hid] with z hz hi
    rw [projectorODE_commutator hz.differentiableAt hi]
    exact hz.differentiableAt.hasDerivAt
  have hint := intertwine_eventually hA hYx (hY.mono fun _ h => h.1) hpd
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff_ball.mp
    (hYa.eventually_analyticAt.and (hY.and hint))
  refine ⟨ε,hε,transport Y,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    exact transport_analyticAt (he w.1 hw.1).1 (he w.2 hw.2).1 (he w.1 hw.1).2.1.2
  · intro s hs
    exact transport_self (he s hs).2.1.2
  · intro s hs t ht
    exact transport_isUnit (he s hs).2.1.2 (he t ht).2.1.2
  · intro s hs t ht u hu
    exact transport_trans (he t ht).2.1.2
  · intro s hs t ht
    exact transport_hasDerivAt (he t ht).2.1.1
  · intro s hs t ht
    exact transport_intertwines (he s hs).2.2 (he t ht).2.2 (he s hs).2.1.2

end SplitTangent.HolomorphicLinearODE

namespace SplitTangent.ParameterProjector
section
open HolomorphicLinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

 
def verticalDerivative (P : ℂ × ℂ → R) (w : ℂ × ℂ) : R := fderiv ℂ P w (0,1)

omit [CompleteSpace R] in
lemma hasDerivAt_vertical {P : ℂ × ℂ → R} {s t : ℂ}
    (hP : DifferentiableAt ℂ P (s,t)) :
    HasDerivAt (fun v => P (s,v)) (verticalDerivative P (s,t)) t := by
  exact hP.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

lemma verticalDerivative_analyticAt {P : ℂ × ℂ → R} {w : ℂ × ℂ}
    (hP : AnalyticAt ℂ P w) : AnalyticAt ℂ (verticalDerivative P) w :=
  ((ContinuousLinearMap.apply ℂ R (E := ℂ × ℂ)).analyticAt_bilinear _).comp
    (analyticAt_const.prod hP.fderiv)

def equation (P B : ℂ × ℂ → R) (w : ℂ × ℂ) : R :=
  verticalDerivative P w * P w - P w * verticalDerivative P w - P w * B w * P w

lemma equation_analyticAt {P B : ℂ × ℂ → R} {w : ℂ × ℂ}
    (hP : AnalyticAt ℂ P w) (hB : AnalyticAt ℂ B w) : AnalyticAt ℂ (equation P B) w :=
  (((verticalDerivative_analyticAt hP).mul hP).sub
    (hP.mul (verticalDerivative_analyticAt hP))).sub ((hP.mul hB).mul hP)

omit [CompleteSpace R] in
lemma equation_eq {P B : ℂ × ℂ → R} {s t : ℂ}
    (hP : DifferentiableAt ℂ P (s,t)) :
    equation P B (s,t) = projectorODE (fun v => P (s,v)) (fun v => B (s,v)) t := by
  simp only [equation,projectorODE,(hasDerivAt_vertical hP).deriv]

 

lemma exists_preserving_parameter_fundamental {P B : ℂ × ℂ → R}
    (hP : AnalyticAt ℂ P (0,0)) (hB : AnalyticAt ℂ B (0,0))
    (hid : ∀ᶠ w in 𝓝 (0,0), P w*P w=P w) :
    ∃ (Y : ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s, Y s 0=1) ∧
      (∀ s t, ‖s‖ < ε → ‖t‖ < ε →
        HasDerivAt (Y s) (equation P B (s,t)*Y s t) t ∧ IsUnit (Y s t)) ∧
      (∀ s t, ‖s‖ < ε → ‖t‖ < ε → P (s,t)*Y s t=Y s t*P (s,0)) ∧
      (∀ (q t : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ t z →
        ‖q z‖ < ε → ‖t z‖ < ε → AnalyticAt ℂ (fun w => Y (q w) (t w)) z) := by
  have hA := equation_analyticAt hP hB
  obtain ⟨Y,r,hr,hY0,hYd,hYa⟩ := exists_parameter_fundamental hA
  obtain ⟨η,hη,hηd⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hP.eventually_analyticAt.and hA.eventually_analyticAt).and hid)
  let ε := min r η
  have hε : 0 < ε := lt_min hr hη
  have hεr : ε ≤ r := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hpol (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      AnalyticAt ℂ P (s,t) ∧ AnalyticAt ℂ (equation P B) (s,t) ∧ P (s,t)*P (s,t)=P (s,t) := by
    have hm : (s,t) ∈ Metric.ball (0,0) η := by
      simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
      exact max_lt (hs.trans_le hεη) (ht.trans_le hεη)
    exact ⟨(hηd (s,t) hm).1.1,(hηd (s,t) hm).1.2,(hηd (s,t) hm).2⟩
  refine ⟨Y,ε,hε,hY0,fun s t hs ht => hYd s t (hs.trans_le hεr) (ht.trans_le hεr),?_,?_⟩
  · intro s t hs ht
    have hconn (v : ℂ) (hv : v ∈ Metric.ball 0 ε) :
        HasDerivAt (fun w => P (s,w))
          (equation P B (s,v)*P (s,v)-P (s,v)*equation P B (s,v)) v := by
      have hpa := (hpol s v hs (mem_ball_zero_iff.mp hv)).1
      have hpd := hasDerivAt_vertical hpa.differentiableAt
      have hi : ∀ᶠ w in 𝓝 v, P (s,w)*P (s,w)=P (s,w) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
        exact (hpol s w hs (mem_ball_zero_iff.mp hw)).2.2
      rw [equation_eq hpa.differentiableAt,
        projectorODE_commutator hpd.differentiableAt hi]
      exact hpd.differentiableAt.hasDerivAt
    have ha : AnalyticOnNhd ℂ (fun v => equation P B (s,v)) (Metric.ball 0 ε) := by
      intro v hv
      exact (hpol s v hs (mem_ball_zero_iff.mp hv)).2.1.comp (analyticAt_const.prod analyticAt_id)
    have he := eqOn_of_solution (f := fun v => P (s,v)*Y s v)
      Metric.isOpen_ball (convex_ball (0:ℂ) ε).isPreconnected ha
      (fun v hv => gauge_hasDerivAt (A := fun v => equation P B (s,v))
        (B := fun v => equation P B (s,v)) (H := fun v => P (s,v)) (Y := Y s) (hconn v hv)
        (hYd s v (hs.trans_le hεr) ((mem_ball_zero_iff.mp hv).trans_le hεr)).1)
      (g := fun v => Y s v * P (s,0)) ?_ (Metric.mem_ball_self hε) ?_
    · exact he (mem_ball_zero_iff.mpr ht)
    · intro v hv
      convert! ((hYd s v (hs.trans_le hεr) ((mem_ball_zero_iff.mp hv).trans_le hεr)).1).mul_const (P (s,0)) using 1; try rfl
      exact (mul_assoc _ _ _).symm
    · simp only [hY0,mul_one,one_mul]
  · intro q t z hq ht hqε htε
    exact hYa q t z hq ht (hqε.trans_le hεr) (htε.trans_le hεr)

end

open HolomorphicLinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

lemma exists_preserving_parameter_transport {P B : ℂ × ℂ → R}
    (hP : AnalyticAt ℂ P (0,0)) (hB : AnalyticAt ℂ B (0,0))
    (hid : ∀ᶠ w in 𝓝 (0,0), P w*P w=P w) :
    ∃ (T : ℂ → ℂ → ℂ → R) (ε : ℝ), 0 < ε ∧
      (∀ s u, ‖s‖ < ε → ‖u‖ < ε → T s u u=1) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → IsUnit (T s u v)) ∧
      (∀ s u v w, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ‖w‖ < ε →
        T s v w*T s u v=T s u w) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε →
        HasDerivAt (T s u) (equation P B (s,v)*T s u v) v ∧
        P (s,v)*T s u v=T s u v*P (s,u)) ∧
      (∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
        ‖q z‖ < ε → ‖u z‖ < ε → ‖v z‖ < ε →
        AnalyticAt ℂ (fun w => T (q w) (u w) (v w)) z) := by
  obtain ⟨Y,ε,hε,hY0,hYd,hYP,hYa⟩ := exists_preserving_parameter_fundamental hP hB hid
  refine ⟨fun s => transport (Y s),ε,hε,?_,?_,?_,?_,?_⟩
  · intro s u hs hu
    exact transport_self (hYd s u hs hu).2
  · intro s u v hs hu hv
    exact transport_isUnit (hYd s u hs hu).2 (hYd s v hs hv).2
  · intro s u v w hs hu hv hw
    exact transport_trans (hYd s v hs hv).2
  · intro s u v hs hu hv
    exact ⟨transport_hasDerivAt (A := fun t => equation P B (s,t)) (hYd s v hs hv).1,
      transport_intertwines (P := fun t => P (s,t)) (hYP s u hs hu) (hYP s v hs hv) (hYd s u hs hu).2⟩
  · intro q u v z hq hu hv hqs hus hvs
    have hsu := hYa q u z hq hu hqs hus
    have hsv := hYa q v z hq hv hqs hvs
    exact hsv.mul ((analyticOnNhd_inverse (𝕜 := ℂ) _ (hYd (q z) (u z) hqs hus).2).comp_of_eq hsu rfl)

end SplitTangent.ParameterProjector

namespace SplitTangent.PullbackConnection
section
open HolomorphicLinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
lemma projected_bracket_eq {P : E → E →L[ℂ] E} {ξ e : E → E} {y : E}
    (hP : DifferentiableAt ℂ P y) (hξ : DifferentiableAt ℂ ξ y)
    (hzero : ∀ᶠ z in 𝓝 y, P z (ξ z)=0) :
    P y (VectorField.lieBracket ℂ ξ e y) =
      P y (fderiv ℂ e y (ξ y)) + (fderiv ℂ P y (e y)) (ξ y) := by
  have hd := (hP.hasFDerivAt.clm_apply hξ.hasFDerivAt).unique
    ((hasFDerivAt_const (0:E) y).congr_of_eventuallyEq hzero)
  have hv := congrArg (fun A : E →L[ℂ] E => A (e y)) hd
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,zero_apply] at hv
  simp only [VectorField.lieBracket,map_sub]
  rw [eq_neg_of_add_eq_zero_left hv,sub_neg_eq_add]

 
def coefficient (P : E → E →L[ℂ] E) (g : ℂ → E) (z : ℂ) : E →L[ℂ] E :=
  (fderiv ℂ P (g z)).flip (deriv g z)

 
def covariantDerivative (P : E → E →L[ℂ] E) (g v : ℂ → E) (z : ℂ) : E :=
  P (g z) (deriv v z) + P (g z) (coefficient P g z (v z))

lemma coefficient_analyticAt {P : E → E →L[ℂ] E} {g : ℂ → E} {z : ℂ}
    (hP : AnalyticAt ℂ P (g z)) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (coefficient P g) z := by
  have ha : AnalyticAt ℂ (fun w => (fderiv ℂ P (g w)).flip) z :=
    ((ContinuousLinearMap.flipₗᵢ (𝕜 := ℂ) (E := E) (Fₗ := E) (Gₗ := E)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (hP.fderiv.comp hg)
  exact (ha.contDiffAt.clm_apply hg.deriv.contDiffAt).analyticAt

omit [CompleteSpace E] in
lemma covariantDerivative_pulled_section {P : E → E →L[ℂ] E}
    {g : ℂ → E} {e ξ : E → E} {z : ℂ}
    (hP : DifferentiableAt ℂ P (g z)) (he : DifferentiableAt ℂ e (g z))
    (hξ : DifferentiableAt ℂ ξ (g z)) (hg : DifferentiableAt ℂ g z)
    (hzero : ∀ᶠ y in 𝓝 (g z), P y (ξ y)=0) (hvel : ξ (g z)=deriv g z)
    (hid : ∀ v, P (g z) (P (g z) v)=P (g z) v) :
    covariantDerivative P g (e ∘ g) z =
      P (g z) (VectorField.lieBracket ℂ ξ e (g z)) := by
  have hbr := projected_bracket_eq (e := e) hP hξ hzero
  rw [hvel] at hbr
  have hd := (he.hasFDerivAt.comp_hasDerivAt z hg.hasDerivAt).deriv
  unfold covariantDerivative coefficient
  rw [hd]
  have hp : P (g z) (P (g z) (VectorField.lieBracket ℂ ξ e (g z))) =
      P (g z) (P (g z) (fderiv ℂ e (g z) (deriv g z)) +
        (fderiv ℂ P (g z) (e (g z))) (deriv g z)) := congrArg (P (g z)) hbr
  simpa only [hid,map_add,ContinuousLinearMap.flip_apply,Function.comp_apply] using hp.symm

omit [CompleteSpace E] in
lemma covariantDerivative_leibniz {P : E → E →L[ℂ] E} {g v : ℂ → E}
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hv : DifferentiableAt ℂ v z) :
    covariantDerivative P g (fun w => f w • v w) z =
      deriv f z • P (g z) (v z) + f z • covariantDerivative P g v z := by
  unfold covariantDerivative
  have hd : deriv (fun w => f w • v w) z = deriv f z • v z + f z • deriv v z :=
    by simpa only [add_comm] using deriv_fun_smul hf hv
  rw [hd]
  simp only [map_add,map_smul,smul_add]
  abel

 
def equation (P : E → E →L[ℂ] E) (g : ℂ → E) : ℂ → E →L[ℂ] E :=
  projectorODE (P ∘ g) (coefficient P g)

lemma equation_analyticAt {P : E → E →L[ℂ] E} {g : ℂ → E} {z : ℂ}
    (hP : AnalyticAt ℂ P (g z)) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (equation P g) z :=
  projectorODE_analyticAt (hP.comp hg) (coefficient_analyticAt hP hg)

omit [CompleteSpace E] in
lemma projectorODE_horizontal {P B : ℂ → E →L[ℂ] E} {z : ℂ} {v : E}
    (hP : DifferentiableAt ℂ P z) (hid : ∀ᶠ w in 𝓝 z, P w * P w = P w)
    (hv : P z v = v) :
    P z (projectorODE P B z v) + P z (B z v) = 0 := by
  have hi := hid.self_of_nhds
  have hz := projector_derivative_sandwich hi (idempotent_derivative hP.hasDerivAt hid)
  have hvz := congrArg (fun A : E →L[ℂ] E => A v) hz
  simp only [mul_apply_eq_comp,hv,zero_apply] at hvz
  have hi' : ∀ w, P z (P z w) = P z w := fun w =>
    congrArg (fun A : E →L[ℂ] E => A w) hi
  simp only [projectorODE,sub_apply,mul_apply_eq_comp,map_sub,hv,hi',hvz,map_zero]
  abel

omit [CompleteSpace E] in
lemma horizontal_of_equation {P : E → E →L[ℂ] E} {g v : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℂ (P ∘ g) z)
    (hid : ∀ᶠ w in 𝓝 z, P (g w) * P (g w) = P (g w))
    (him : P (g z) (v z) = v z)
    (hv : HasDerivAt v (equation P g z (v z)) z) :
    covariantDerivative P g v z = 0 := by
  unfold covariantDerivative
  rw [hv.deriv]
  exact projectorODE_horizontal hP hid him

 

theorem exists_local_horizontal_transport {P : E → E →L[ℂ] E} {g : ℂ → E} {x : ℂ}
    (hP : AnalyticAt ℂ P (g x)) (hg : AnalyticAt ℂ g x)
    (hid : ∀ᶠ y in 𝓝 (g x), P y * P y = P y) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2)
        (Metric.ball x ε ×ˢ Metric.ball x ε) ∧
      (∀ s ∈ Metric.ball x ε, T s s=1) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, IsUnit (T s t)) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ u ∈ Metric.ball x ε,
        T t u*T s t=T s u) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ v : E,
        P (g s) v = v →
        P (g t) (T s t v) = T s t v ∧
        covariantDerivative P g (fun w => T s w v) t = 0) := by
  have hpg := hP.comp hg
  have hip : ∀ᶠ z in 𝓝 x, (P ∘ g) z * (P ∘ g) z = (P ∘ g) z :=
    hg.continuousAt hid
  obtain ⟨r,hr,T,hTa,hT0,hTu,hTc,hTd,hTi⟩ :=
    exists_local_projector_transport hpg (coefficient_analyticAt hP hg) hip
  obtain ⟨q,hq,hqn⟩ := Metric.eventually_nhds_iff_ball.mp
    (hpg.eventually_analyticAt.and (eventually_eventually_nhds.mpr hip))
  have hmr : Metric.ball x (min r q) ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
  have hmq : Metric.ball x (min r q) ⊆ Metric.ball x q := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r q,lt_min hr hq,T,?_,?_,?_,?_,?_⟩
  · exact hTa.mono (Set.prod_mono hmr hmr)
  · exact fun s hs => hT0 s (hmr hs)
  · exact fun s hs t ht => hTu s (hmr hs) t (hmr ht)
  · exact fun s hs t ht u hu => hTc s (hmr hs) t (hmr ht) u (hmr hu)
  · intro s hs t ht v hv
    have him : P (g t) (T s t v) = T s t v := by
      have hh := congrArg (fun A : E →L[ℂ] E => A v) (hTi s (hmr hs) t (hmr ht))
      simpa only [mul_apply_eq_comp,Function.comp_apply,hv] using hh
    refine ⟨him,horizontal_of_equation (hqn t (hmq ht)).1.differentiableAt
      (hqn t (hmq ht)).2 him ?_⟩
    have hd := (hTd s (hmr hs) t (hmr ht)).clm_apply (hasDerivAt_const t v)
    simpa only [equation,add_zero,map_zero,mul_apply_eq_comp] using hd


def familyCoefficient (P : E → E →L[ℂ] E) (F : ℂ × ℂ → E) (w : ℂ × ℂ) : E →L[ℂ] E :=
  (fderiv ℂ P (F w)).flip (fderiv ℂ F w (0,1))

lemma familyCoefficient_analyticAt {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E} {w : ℂ × ℂ}
    (hP : AnalyticAt ℂ P (F w)) (hF : AnalyticAt ℂ F w) :
    AnalyticAt ℂ (familyCoefficient P F) w := by
  have ha : AnalyticAt ℂ (fun w => (fderiv ℂ P (F w)).flip) w :=
    ((ContinuousLinearMap.flipₗᵢ (𝕜 := ℂ) (E := E) (Fₗ := E) (Gₗ := E)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (hP.fderiv.comp hF)
  have hb : AnalyticAt ℂ (fun w => fderiv ℂ F w (0,1)) w :=
    ((ContinuousLinearMap.apply ℂ E (E := ℂ × ℂ)).analyticAt_bilinear _).comp
      (analyticAt_const.prod hF.fderiv)
  exact (ha.contDiffAt.clm_apply hb.contDiffAt).analyticAt

omit [CompleteSpace E] in
lemma familyCoefficient_eq {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E} {s t : ℂ}
    (hF : DifferentiableAt ℂ F (s,t)) :
    familyCoefficient P F (s,t) = coefficient P (fun v => F (s,v)) t := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hd' : HasDerivAt (fun v => F (s,v)) (fderiv ℂ F (s,t) (0,1)) t := hd
  simp only [familyCoefficient,coefficient,hd'.deriv]

omit [CompleteSpace E] in
lemma familyEquation_eq {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E} {s t : ℂ}
    (hP : DifferentiableAt ℂ P (F (s,t))) (hF : DifferentiableAt ℂ F (s,t)) :
    ParameterProjector.equation (P ∘ F) (familyCoefficient P F) (s,t) =
      equation P (fun v => F (s,v)) t := by
  rw [ParameterProjector.equation_eq (hP.comp (s,t) hF)]
  simp only [equation,projectorODE,familyCoefficient_eq hF,Function.comp_def]

 

theorem exists_horizontal_parameter_transport {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E}
    (hP : AnalyticAt ℂ P (F (0,0))) (hF : AnalyticAt ℂ F (0,0))
    (hid : ∀ᶠ y in 𝓝 (F (0,0)), P y*P y=P y) :
    ∃ (T : ℂ → ℂ → ℂ → E →L[ℂ] E) (ε : ℝ), 0 < ε ∧
      (∀ s u, ‖s‖ < ε → ‖u‖ < ε → T s u u=1) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → IsUnit (T s u v)) ∧
      (∀ s u v w, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ‖w‖ < ε →
        T s v w*T s u v=T s u w) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ∀ e : E,
        P (F (s,u)) e=e → P (F (s,v)) (T s u v e)=T s u v e ∧
          covariantDerivative P (fun t => F (s,t)) (fun t => T s u t e) v=0) ∧
      (∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
        ‖q z‖ < ε → ‖u z‖ < ε → ‖v z‖ < ε →
        AnalyticAt ℂ (fun w => T (q w) (u w) (v w)) z) := by
  have hidF : ∀ᶠ w in 𝓝 (0,0), (P ∘ F) w*(P ∘ F) w=(P ∘ F) w := hF.continuousAt hid
  obtain ⟨T,r,hr,hT0,hTu,hTc,hTd,hTa⟩ := ParameterProjector.exists_preserving_parameter_transport
    (hP.comp hF) (familyCoefficient_analyticAt hP hF) hidF
  have hhP : ∀ᶠ w in 𝓝 (0,0), AnalyticAt ℂ P (F w) := hF.continuousAt hP.eventually_analyticAt
  obtain ⟨η,hη,hηd⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hhP.and hF.eventually_analyticAt).and hidF)
  let ε := min r η
  have hε : 0 < ε := lt_min hr hη
  have hεr : ε ≤ r := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hpol (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      AnalyticAt ℂ P (F (s,t)) ∧ AnalyticAt ℂ F (s,t) ∧ P (F (s,t))*P (F (s,t))=P (F (s,t)) := by
    have hm : (s,t) ∈ Metric.ball (0,0) η := by
      simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
      exact max_lt (hs.trans_le hεη) (ht.trans_le hεη)
    exact ⟨(hηd (s,t) hm).1.1,(hηd (s,t) hm).1.2,(hηd (s,t) hm).2⟩
  refine ⟨T,ε,hε,?_,?_,?_,?_,?_⟩
  · exact fun s u hs hu => hT0 s u (hs.trans_le hεr) (hu.trans_le hεr)
  · exact fun s u v hs hu hv => hTu s u v (hs.trans_le hεr) (hu.trans_le hεr) (hv.trans_le hεr)
  · exact fun s u v w hs hu hv hw => hTc s u v w (hs.trans_le hεr) (hu.trans_le hεr) (hv.trans_le hεr) (hw.trans_le hεr)
  · intro s u v hs hu hv e he
    have hpoint := hpol s v hs hv
    have hdata := hTd s u v (hs.trans_le hεr) (hu.trans_le hεr) (hv.trans_le hεr)
    have him : P (F (s,v)) (T s u v e)=T s u v e := by
      have hh := congrArg (fun A : E →L[ℂ] E => A e) hdata.2
      simpa only [mul_apply_eq_comp,Function.comp_apply,he] using hh
    have hg : AnalyticAt ℂ (fun t => F (s,t)) v := hpoint.2.1.comp (analyticAt_const.prod analyticAt_id)
    have hi : ∀ᶠ t in 𝓝 v, P (F (s,t))*P (F (s,t))=P (F (s,t)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv)] with t ht
      exact (hpol s t hs (mem_ball_zero_iff.mp ht)).2.2
    refine ⟨him,horizontal_of_equation (P := P) (g := fun t => F (s,t))
      (v := fun t => T s u t e) (hpoint.1.comp (f := fun t => F (s,t)) hg).differentiableAt hi him ?_⟩
    rw [familyEquation_eq hpoint.1.differentiableAt hpoint.2.1.differentiableAt] at hdata
    have hd := hdata.1.clm_apply (hasDerivAt_const v e)
    simpa only [add_zero,map_zero,mul_apply_eq_comp] using hd
  · exact fun q u v z hq hu hv hqs hus hvs => hTa q u v z hq hu hv
      (hqs.trans_le hεr) (hus.trans_le hεr) (hvs.trans_le hεr)

end

open HolomorphicLinearODE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

omit [CompleteSpace E] in
theorem covariantDerivative_naturality
    {P : E → E →L[ℂ] E} {Q : F → F →L[ℂ] F} {φ : E → F}
    {g v : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℂ P (g z)) (hQ : DifferentiableAt ℂ Q (φ (g z)))
    (hφ : AnalyticAt ℂ φ (g z)) (hg : DifferentiableAt ℂ g z)
    (hv : DifferentiableAt ℂ v z)
    (hnat : ∀ᶠ y in 𝓝 (g z), ∀ w : E,
      Q (φ y) (fderiv ℂ φ y w) = fderiv ℂ φ y (P y w))
    (hvel : P (g z) (deriv g z) = 0)
    (hid : ∀ w : F, Q (φ (g z)) (Q (φ (g z)) w) = Q (φ (g z)) w) :
    covariantDerivative Q (φ ∘ g) (fun t => fderiv ℂ φ (g t) (v t)) z =
      fderiv ℂ φ (g z) (covariantDerivative P g v z) := by
  let G := fderiv ℂ φ
  have hG : DifferentiableAt ℂ G (g z) := hφ.fderiv.differentiableAt
  have hφd := hφ.differentiableAt.hasFDerivAt
  have he : (fun y => Q (φ y) (G y (deriv g z))) =ᶠ[𝓝 (g z)]
      (fun y => G y (P y (deriv g z))) := hnat.mono fun y hy => hy _
  have hl := (hQ.hasFDerivAt.comp (g z) hφd).clm_apply
    (hG.hasFDerivAt.clm_apply (hasFDerivAt_const (deriv g z) (g z)))
  have hr := hG.hasFDerivAt.clm_apply
    (hP.hasFDerivAt.clm_apply (hasFDerivAt_const (deriv g z) (g z)))
  have hd := hl.unique (hr.congr_of_eventuallyEq he)
  have hde := congrArg (fun A : E →L[ℂ] F => A (v z)) hd
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,zero_apply,map_zero,add_zero,hvel] at hde
  have hsym := hφ.contDiffAt.isSymmSndFDerivAt_of_omega (v z) (deriv g z)
  have hzero := congrArg (Q (φ (g z))) hde
  simp only [G,Function.comp_apply,map_add,hid,hnat.self_of_nhds,zero_add] at hzero
  have hdg := (hφd.comp_hasDerivAt z hg.hasDerivAt).deriv
  have hdv := ((hG.hasFDerivAt.comp_hasDerivAt z hg.hasDerivAt).clm_apply
    hv.hasDerivAt).deriv
  simp only [G,Function.comp_apply] at hdv
  unfold covariantDerivative coefficient
  rw [hdg,hdv]
  simp only [Function.comp_apply,ContinuousLinearMap.flip_apply,map_add,
    hnat.self_of_nhds]
  change Q (φ (g z)) ((fderiv ℂ G (g z) (deriv g z)) (v z)) +
      G (g z) (P (g z) (deriv v z)) +
      Q (φ (g z)) ((fderiv ℂ Q (φ (g z)) (G (g z) (v z))) (G (g z) (deriv g z))) =
      G (g z) (P (g z) (deriv v z)) +
      G (g z) (P (g z) ((fderiv ℂ P (g z) (v z)) (deriv g z)))
  rw [show (fderiv ℂ G (g z) (deriv g z)) (v z) =
    (fderiv ℂ G (g z) (v z)) (deriv g z) from hsym.symm]
  calc
    _ = G (g z) (P (g z) (deriv v z)) +
        (Q (φ (g z)) ((fderiv ℂ G (g z) (v z)) (deriv g z)) +
          Q (φ (g z)) ((fderiv ℂ Q (φ (g z)) (G (g z) (v z))) (G (g z) (deriv g z)))) := by abel
    _ = _ := by rw [hzero]

end SplitTangent.PullbackConnection

namespace SplitTangent.HolomorphicLinearODE
open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma inverse_apply_horizontal {Y : ℂ → E →L[ℂ] E} {v : ℂ → E}
    {A : E →L[ℂ] E} {z : ℂ}
    (hY : HasDerivAt Y (A * Y z) z) (hv : HasDerivAt v (A (v z)) z)
    (hu : IsUnit (Y z)) :
    HasDerivAt (fun w => Ring.inverse (Y w) (v w)) 0 z := by
  obtain ⟨u,he⟩ := hu
  have hi : HasDerivAt (fun w => Ring.inverse (Y w))
      (-(Ring.inverse (Y z) * (A * Y z) * Ring.inverse (Y z))) z := by
    have h := (hasFDerivAt_ringInverse (𝕜 := ℂ) u)
    rw [he] at h
    convert! h.comp_hasDerivAt z hY using 1; try rfl
    simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply]
    rw [← Ring.inverse_unit u,he]
  convert! hi.clm_apply hv using 1; try rfl
  have hc : Y z * Ring.inverse (Y z) = 1 := Ring.mul_inverse_cancel _ ⟨u,he⟩
  rw [mul_assoc (Ring.inverse (Y z)),mul_assoc A,hc,mul_one]
  simp only [neg_apply,mul_apply_eq_comp,neg_add_cancel]

 
theorem vector_local_uniqueness {A : ℂ → E →L[ℂ] E} {f g : ℂ → E} {x : ℂ}
    (hA : AnalyticAt ℂ A x)
    (hf : ∀ᶠ z in 𝓝 x, HasDerivAt f (A z (f z)) z)
    (hg : ∀ᶠ z in 𝓝 x, HasDerivAt g (A z (g z)) z)
    (he : f x = g x) : f =ᶠ[𝓝 x] g := by
  obtain ⟨Y,hYa,hY0,hY⟩ := exists_local_fundamental hA
  obtain ⟨ε,hε,hs⟩ := Metric.eventually_nhds_iff_ball.mp (hY.and (hf.and hg))
  let D : ℂ → E := fun z => Ring.inverse (Y z) (f z-g z)
  have hd (z : ℂ) (hz : z ∈ Metric.ball x ε) : HasDerivAt D 0 z := by
    have hsub : HasDerivAt (fun w => f w-g w) (A z (f z-g z)) z := by
      convert! (hs z hz).2.1.sub (hs z hz).2.2 using 1; try rfl
      exact map_sub _ _ _
    exact inverse_apply_horizontal (hs z hz).1.1 hsub (hs z hz).1.2
  filter_upwards [Metric.ball_mem_nhds x hε] with z hz
  have hc : D z = D x := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball x ε).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hε)
  have hmul := congrArg (Y z) hc
  have hcancel := congrArg (fun A : E →L[ℂ] E => A (f z-g z))
    (Ring.mul_inverse_cancel (Y z) (hs z hz).1.2)
  have hz0 : f z-g z = 0 := by
    simpa only [D,he,sub_self,map_zero,← mul_apply_eq_comp,
      Ring.mul_inverse_cancel _ (hs z hz).1.2,one_apply_eq_self] using hmul
  exact sub_eq_zero.mp hz0

end SplitTangent.HolomorphicLinearODE

namespace SplitTangent.PullbackConnection
section
open HolomorphicLinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
lemma hasDerivAt_equation_of_horizontal {P : E → E →L[ℂ] E} {g v : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℂ (P ∘ g) z) (hv : DifferentiableAt ℂ v z)
    (hid : ∀ᶠ w in 𝓝 z, P (g w) * P (g w) = P (g w))
    (him : ∀ᶠ w in 𝓝 z, P (g w) (v w) = v w)
    (hh : covariantDerivative P g v z = 0) :
    HasDerivAt v (equation P g z (v z)) z := by
  have hfix := ((hP.hasDerivAt.clm_apply hv.hasDerivAt).congr_of_eventuallyEq (him.mono fun _ h => h.symm)).unique
    hv.hasDerivAt
  have hp := hid.self_of_nhds
  have hi := him.self_of_nhds
  have hz := congrArg (fun A : E →L[ℂ] E => A (v z))
    (projector_derivative_sandwich hp (idempotent_derivative hP.hasDerivAt hid))
  simp only [mul_apply_eq_comp,hi,zero_apply] at hz
  have hvd : deriv v z = deriv (P ∘ g) z (v z) -
      P (g z) (coefficient P g z (v z)) := by
    unfold covariantDerivative at hh
    change deriv (P ∘ g) z (v z) + P (g z) (deriv v z) = deriv v z at hfix
    rw [eq_neg_of_add_eq_zero_left hh] at hfix
    simpa only [sub_eq_add_neg,add_comm] using hfix.symm
  convert! hv.hasDerivAt using 1
  rw [hvd]
  simp only [equation,projectorODE,sub_apply,mul_apply_eq_comp,
    Function.comp_apply,hi,hz,sub_zero]

lemma horizontal_local_uniqueness {P : E → E →L[ℂ] E} {g f h : ℂ → E} {x : ℂ}
    (hP : AnalyticAt ℂ P (g x)) (hg : AnalyticAt ℂ g x)
    (hid : ∀ᶠ y in 𝓝 (g x), P y * P y=P y)
    (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z ∧ covariantDerivative P g f z=0)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z ∧ covariantDerivative P g h z=0)
    (hfi : ∀ᶠ z in 𝓝 x, P (g z) (f z)=f z)
    (hhi : ∀ᶠ z in 𝓝 x, P (g z) (h z)=h z)
    (he : f x=h x) : f =ᶠ[𝓝 x] h := by
  have hpg := hP.comp hg
  have hi := hg.continuousAt hid
  apply vector_local_uniqueness (equation_analyticAt hP hg) _ _ he
  · filter_upwards [hpg.eventually_analyticAt,eventually_eventually_nhds.mpr hi,
      eventually_eventually_nhds.mpr hfi,hf] with z hz hzi hzfi hzf
    exact hasDerivAt_equation_of_horizontal hz.differentiableAt hzf.1 hzi hzfi hzf.2
  · filter_upwards [hpg.eventually_analyticAt,eventually_eventually_nhds.mpr hi,
      eventually_eventually_nhds.mpr hhi,hh] with z hz hzi hzhi hzh
    exact hasDerivAt_equation_of_horizontal hz.differentiableAt hzh.1 hzi hzhi hzh.2

end

open HolomorphicLinearODE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

theorem horizontal_chart_compatibility
    {P : E → E →L[ℂ] E} {Q : F → F →L[ℂ] F} {φ : E → F}
    {g f : ℂ → E} {h : ℂ → F} {z : ℂ}
    (hP : AnalyticAt ℂ P (g z)) (hQ : AnalyticAt ℂ Q (φ (g z)))
    (hφ : AnalyticAt ℂ φ (g z)) (hg : AnalyticAt ℂ g z)
    (hf : AnalyticAt ℂ f z) (hh : AnalyticAt ℂ h z)
    (hidQ : ∀ᶠ y in 𝓝 (φ (g z)), Q y*Q y=Q y)
    (hnat : ∀ᶠ y in 𝓝 (g z), ∀ v : E, Q (φ y) (fderiv ℂ φ y v)=fderiv ℂ φ y (P y v))
    (hvel : ∀ᶠ w in 𝓝 z, P (g w) (deriv g w)=0)
    (hfi : ∀ᶠ w in 𝓝 z, P (g w) (f w)=f w)
    (hhi : ∀ᶠ w in 𝓝 z, Q (φ (g w)) (h w)=h w)
    (hfh : ∀ᶠ w in 𝓝 z, covariantDerivative P g f w=0)
    (hhh : ∀ᶠ w in 𝓝 z, covariantDerivative Q (φ ∘ g) h w=0)
    (he : h z=fderiv ℂ φ (g z) (f z)) :
    h =ᶠ[𝓝 z] fun w => fderiv ℂ φ (g w) (f w) := by
  have hcurve : AnalyticAt ℂ (φ ∘ g) z := hφ.comp hg
  have ht : AnalyticAt ℂ (fun w => fderiv ℂ φ (g w) (f w)) z :=
    ((ContinuousLinearMap.apply ℂ F (E := E)).analyticAt_bilinear _).comp
      (hf.prod (hφ.fderiv.comp hg))
  have hNatLocal : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 (g w), ∀ v : E,
      Q (φ y) (fderiv ℂ φ y v)=fderiv ℂ φ y (P y v) :=
    hg.continuousAt (eventually_eventually_nhds.mpr hnat)
  have hti : ∀ᶠ w in 𝓝 z, Q (φ (g w)) (fderiv ℂ φ (g w) (f w)) =
      fderiv ℂ φ (g w) (f w) := by
    filter_upwards [hg.continuousAt hnat,hfi] with w hn hi
    rw [hn (f w),hi]
  have hth : ∀ᶠ w in 𝓝 z, covariantDerivative Q (φ ∘ g)
      (fun w => fderiv ℂ φ (g w) (f w)) w=0 := by
    filter_upwards [hg.continuousAt hP.eventually_analyticAt,
      hcurve.continuousAt hQ.eventually_analyticAt,hg.continuousAt hφ.eventually_analyticAt,
      hg.eventually_analyticAt,hf.eventually_analyticAt,hNatLocal,hvel,
      hcurve.continuousAt hidQ,hfh] with w hp hq hφw hgw hfw hn hv hq2 hhor
    have hq2' : ∀ v : F, Q (φ (g w)) (Q (φ (g w)) v)=Q (φ (g w)) v := by
      intro v
      exact congrArg (fun A : F →L[ℂ] F => A v) hq2
    rw [covariantDerivative_naturality hp.differentiableAt hq.differentiableAt hφw
      hgw.differentiableAt hfw.differentiableAt hn hv hq2',hhor,map_zero]
  apply horizontal_local_uniqueness (P := Q) (g := φ ∘ g) hQ hcurve hidQ _ _ hhi hti he
  · filter_upwards [hh.eventually_analyticAt,hhh] with w ha hb
    exact ⟨ha.differentiableAt,hb⟩
  · filter_upwards [ht.eventually_analyticAt,hth] with w ha hb
    exact ⟨ha.differentiableAt,hb⟩

 

theorem horizontal_eqOn {P : E → E →L[ℂ] E} {g f h : ℂ → E} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hP : ∀ z ∈ U, AnalyticAt ℂ P (g z)) (hg : AnalyticOnNhd ℂ g U)
    (hf : AnalyticOnNhd ℂ f U) (hh : AnalyticOnNhd ℂ h U)
    (hid : ∀ z ∈ U, ∀ᶠ y in 𝓝 (g z), P y*P y=P y)
    (hfi : ∀ z ∈ U, P (g z) (f z)=f z) (hhi : ∀ z ∈ U, P (g z) (h z)=h z)
    (hfh : ∀ z ∈ U, covariantDerivative P g f z=0)
    (hhh : ∀ z ∈ U, covariantDerivative P g h z=0)
    {x : ℂ} (hx : x ∈ U) (he : f x=h x) : EqOn f h U := by
  apply hf.eqOn_of_preconnected_of_eventuallyEq hh hUc hx
  apply horizontal_local_uniqueness (hP x hx) (hg x hx) (hid x hx) _ _ _ _ he
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => ⟨(hf z hz).differentiableAt,hfh z hz⟩)
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun z hz => ⟨(hh z hz).differentiableAt,hhh z hz⟩)
  · exact Filter.Eventually.mono (hU.mem_nhds hx) hfi
  · exact Filter.Eventually.mono (hU.mem_nhds hx) hhi

end SplitTangent.PullbackConnection

open Filter Topology Set
namespace SplitTangent.TwoChartCovering
variable {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]

 

theorem exists_normalized_lifts {p : E → B} (hp : IsCoveringMap p)
    {f g : ℂ → B} (hf : Continuous f) (hg : Continuous g)
    (hov : ∀ z : ℂ, z ≠ 0 → f z = g z⁻¹)
    (a : ℂ) (e : E) (he : p e=f a) :
    ∃ (F G : C(ℂ,E)), F a=e ∧ p ∘ F=f ∧ p ∘ G=g ∧
      ∀ z : ℂ, z ≠ 0 → F z=G z⁻¹ := by
  obtain ⟨F,⟨hFa,hFp⟩,_⟩ := hp.existsUnique_continuousMap_lifts ⟨f,hf⟩ a e he
  have h1 : p (F 1)=g 1 := by
    have hh := congrFun hFp 1
    change p (F 1)=f 1 at hh
    simpa using hh.trans (hov 1 one_ne_zero)
  obtain ⟨G,⟨hG1,hGp⟩,_⟩ := hp.existsUnique_continuousMap_lifts ⟨g,hg⟩ 1 (F 1) h1
  refine ⟨F,G,hFa,hFp,hGp,?_⟩
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) := by
    exact (isPathConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) (0 : ℂ)).isConnected.isPreconnected
  have hci : ContinuousOn (fun z : ℂ => G z⁻¹) ({0}ᶜ : Set ℂ) := by
    exact G.continuous.comp_continuousOn (continuousOn_id.inv₀ (fun z hz => hz))
  have heq : EqOn (p ∘ F) (p ∘ fun z : ℂ => G z⁻¹) ({0}ᶜ : Set ℂ) := by
    intro z hz
    change p (F z)=p (G z⁻¹)
    have h1 := congrFun hFp z
    have h2 := congrFun hGp z⁻¹
    exact h1.trans ((hov z hz).trans h2.symm)
  have hbase : (F : ℂ → E) 1=(fun z : ℂ => G z⁻¹) 1 := by simpa using hG1.symm
  exact hp.eqOn_of_comp_eqOn hconn F.continuous.continuousOn hci heq one_ne_zero hbase

end SplitTangent.TwoChartCovering

namespace SplitTangent.HorizontalCovering
section
open Bundle
variable {ι B V : Type*} [TopologicalSpace B] [TopologicalSpace V] [DiscreteTopology V]

 

structure HorizontalCocycle (ι B V : Type*) [TopologicalSpace B] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet : ∀ x, x ∈ baseSet (indexAt x)
  change : ι → ι → B → V → V
  change_self : ∀ i x, x ∈ baseSet i → ∀ v, change i i x v=v
  change_comp : ∀ i j k x, x ∈ baseSet i ∩ baseSet j ∩ baseSet k → ∀ v,
    change j k x (change i j x v)=change i k x v
  change_locally_constant : ∀ i j x, x ∈ baseSet i ∩ baseSet j → ∀ v,
    ∀ᶠ y in 𝓝 x, change i j y v=change i j x v

namespace HorizontalCocycle
variable (D : HorizontalCocycle ι B V)

 

def toCore : FiberBundleCore ι B V where
  baseSet := D.baseSet
  isOpen_baseSet := D.isOpen_baseSet
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet
  coordChange := D.change
  coordChange_self := D.change_self
  continuousOn_coordChange := by
    intro i j
    apply continuousOn_prod_of_discrete_right.mpr
    intro v x hx
    exact (continuousAt_const.congr_of_eventuallyEq
      (D.change_locally_constant i j x hx.1 v)).continuousWithinAt
  coordChange_comp := D.change_comp

 

theorem isCoveringMap : IsCoveringMap D.toCore.proj :=
  FiberBundle.isCoveringMap

 

theorem coordinates_locally_constant {A : Type*} [TopologicalSpace A]
    {f : A → B} {s : C(A,D.toCore.TotalSpace)} (hs : D.toCore.proj ∘ s=f)
    {a : A} {i : ι} (ha : f a ∈ D.baseSet i) :
    ∀ᶠ y in 𝓝 a, (D.toCore.localTriv i (s y)).2=(D.toCore.localTriv i (s a)).2 := by
  have hsource : s a ∈ (D.toCore.localTriv i).source := by
    rw [D.toCore.mem_localTriv_source,← D.toCore.baseSet_at]
    change D.toCore.proj (s a) ∈ D.baseSet i
    rw [show D.toCore.proj (s a)=f a from congrFun hs a]
    exact ha
  have hc : ContinuousAt (fun y => (D.toCore.localTriv i (s y)).2) a :=
    ((D.toCore.localTriv i).toOpenPartialHomeomorph.continuousAt hsource).snd.comp s.continuous.continuousAt
  simpa only [ContinuousAt,nhds_discrete,tendsto_pure] using hc

 

theorem lift_local_form {A : Type*} [TopologicalSpace A]
    {f : A → B} (hf : Continuous f) {s : C(A,D.toCore.TotalSpace)}
    (hs : D.toCore.proj ∘ s=f) {a : A} {i : ι} (ha : f a ∈ D.baseSet i) :
    ∀ᶠ y in 𝓝 a, s y=(D.toCore.localTriv i).toPartialEquiv.symm
      (f y,(D.toCore.localTriv i (s a)).2) := by
  filter_upwards [D.coordinates_locally_constant hs ha,
    hf.continuousAt ((D.isOpen_baseSet i).mem_nhds ha)] with y hy hbase
  have hsource : s y ∈ (D.toCore.localTriv i).source := by
    rw [D.toCore.mem_localTriv_source,← D.toCore.baseSet_at]
    change D.toCore.proj (s y) ∈ D.baseSet i
    rw [show D.toCore.proj (s y)=f y from congrFun hs y]
    exact hbase
  have he : D.toCore.localTriv i (s y)=(f y,(D.toCore.localTriv i (s a)).2) := by
    apply Prod.ext
    · exact ((D.toCore.localTriv i).coe_fst hsource).trans (congrFun hs y)
    · exact hy
  rw [← he]
  exact ((D.toCore.localTriv i).toPartialEquiv.left_inv hsource).symm

 

theorem exists_two_chart_lifts {f g : ℂ → B} (hf : Continuous f) (hg : Continuous g)
    (hov : ∀ z : ℂ, z ≠ 0 → f z=g z⁻¹) (a : ℂ)
    (e : D.toCore.TotalSpace) (he : D.toCore.proj e=f a) :
    ∃ (F G : C(ℂ,D.toCore.TotalSpace)), F a=e ∧ D.toCore.proj ∘ F=f ∧ D.toCore.proj ∘ G=g ∧
      ∀ z : ℂ, z ≠ 0 → F z=G z⁻¹ :=
  TwoChartCovering.exists_normalized_lifts D.isCoveringMap hf hg hov a e he

end HorizontalCocycle
end

variable {B : Type*} [TopologicalSpace B] {V : B → Type*}

 

structure LocalTransportData (B : Type*) [TopologicalSpace B] (V : B → Type*) where
  domain : B → Set B
  domain_open : ∀ x, IsOpen (domain x)
  domain_self : ∀ x, x ∈ domain x
  forward : ∀ x y, V x → V y
  reverse : ∀ x y, V y → V x
  left_inv : ∀ x y, y ∈ domain x → Function.LeftInverse (reverse x y) (forward x y)
  right_inv : ∀ x y, y ∈ domain x → Function.RightInverse (reverse x y) (forward x y)
  forward_self : ∀ x v, forward x x v=v
  overlap : ∀ x y z, z ∈ domain x ∩ domain y → ∀ v : V x,
    ∀ᶠ w in 𝓝 z, forward y w (reverse y z (forward x z v))=forward x w v

namespace LocalTransportData
variable (D : LocalTransportData B V)

def localEquiv (x y : B) (hy : y ∈ D.domain x) : V x ≃ V y where
  toFun := D.forward x y
  invFun := D.reverse x y
  left_inv := D.left_inv x y hy
  right_inv := D.right_inv x y hy

lemma reverse_self (x : B) (v : V x) : D.reverse x x v=v := by
  simpa only [D.forward_self] using D.left_inv x x (D.domain_self x) v

include D in
 

theorem equiv_nonempty [ConnectedSpace B] (a x : B) : Nonempty (V a ≃ V x) := by
  let Z : Set B := {x | Nonempty (V a ≃ V x)}
  have ho : IsOpen Z := isOpen_iff_mem_nhds.mpr fun x hx =>
    Filter.mem_of_superset ((D.domain_open x).mem_nhds (D.domain_self x))
      (fun y hy => hx.map (fun e => e.trans (D.localEquiv x y hy)))
  have hoc : IsOpen Zᶜ := isOpen_iff_mem_nhds.mpr fun x hx =>
    Filter.mem_of_superset ((D.domain_open x).mem_nhds (D.domain_self x)) (fun y hy he =>
      hx (he.map (fun e => e.trans (D.localEquiv x y hy).symm)))
  have hu : Z=univ := (show IsClopen Z from ⟨isOpen_compl_iff.mp hoc,ho⟩).eq_univ
    ⟨a,⟨Equiv.refl _⟩⟩
  exact (show x ∈ Z from hu ▸ mem_univ x)

def fiberEquiv [ConnectedSpace B] (a x : B) : V a ≃ V x :=
  Classical.choice (D.equiv_nonempty a x)

 

def toCocycle [ConnectedSpace B] (a : B) : HorizontalCocycle B B (V a) where
  baseSet := D.domain
  isOpen_baseSet := D.domain_open
  indexAt := id
  mem_baseSet := D.domain_self
  change := fun i j z v => (D.fiberEquiv a j).symm
    (D.reverse j z (D.forward i z (D.fiberEquiv a i v)))
  change_self := by
    intro i z hz v
    rw [D.left_inv i z hz]
    exact (D.fiberEquiv a i).symm_apply_apply v
  change_comp := by
    intro i j k z hz v
    simp only [Equiv.apply_symm_apply]
    rw [D.right_inv j z hz.1.2 (D.forward i z (D.fiberEquiv a i v))]
  change_locally_constant := by
    intro i j z hz v
    filter_upwards [D.overlap i j z hz (D.fiberEquiv a i v),
      (D.domain_open j).mem_nhds hz.2] with w he hw
    have hh := congrArg (D.reverse j w) he
    rw [D.left_inv j w hw] at hh
    exact congrArg (D.fiberEquiv a j).symm hh.symm

variable [ConnectedSpace B] (a : B) [TopologicalSpace (V a)] [DiscreteTopology (V a)]

 
def decode (p : (D.toCocycle a).toCore.TotalSpace) : (b : B) × V b :=
  ⟨p.proj,D.fiberEquiv a p.proj p.2⟩

def encode (x : B) (v : V x) : (D.toCocycle a).toCore.TotalSpace :=
  ⟨x,(D.fiberEquiv a x).symm v⟩

@[simp] lemma decode_encode (x : B) (v : V x) : D.decode a (D.encode a x v)=⟨x,v⟩ := by
  change (⟨x,D.fiberEquiv a x ((D.fiberEquiv a x).symm v)⟩ : (b : B) × V b)=_
  rw [Equiv.apply_symm_apply]

lemma decode_local_frame {i x : B} (_ : x ∈ D.domain i) (v : V a) :
    D.decode a (((D.toCocycle a).toCore.localTriv i).toPartialEquiv.symm (x,v)) =
      ⟨x,D.forward i x (D.fiberEquiv a i v)⟩ := by
  change (⟨x,D.fiberEquiv a x ((D.fiberEquiv a x).symm
    (D.reverse x x (D.forward i x (D.fiberEquiv a i v)) ))⟩ : (b : B) × V b) = _
  simp only [Equiv.apply_symm_apply,D.reverse_self]

 

theorem decode_lift_local_form {A : Type*} [TopologicalSpace A] {f : A → B}
    (hf : Continuous f) {s : C(A,(D.toCocycle a).toCore.TotalSpace)}
    (hs : (D.toCocycle a).toCore.proj ∘ s=f) {z : A} {i : B}
    (hi : f z ∈ D.domain i) :
    ∃ v : V i, ∀ᶠ y in 𝓝 z, D.decode a (s y)=⟨f y,D.forward i (f y) v⟩ := by
  refine ⟨D.fiberEquiv a i (((D.toCocycle a).toCore.localTriv i) (s z)).2,?_⟩
  filter_upwards [(D.toCocycle a).lift_local_form hf hs hi,
    hf.continuousAt ((D.domain_open i).mem_nhds hi)] with y hy hbase
  rw [hy,D.decode_local_frame a hbase]

end LocalTransportData
end SplitTangent.HorizontalCovering

namespace SplitTangent.HorizontalCovering.LocalTransportData
variable {B : Type*} [TopologicalSpace B] {V : B → Type*}
variable (D : LocalTransportData B V)

 

def IsHorizontalAlong {A : Type*} [TopologicalSpace A] (f : A → B)
    (σ : A → (b : B) × V b) : Prop :=
  ∀ a, ∃ v : V (f a), ∀ᶠ y in 𝓝 a, σ y=⟨f y,D.forward (f a) (f y) v⟩

lemma horizontal_local_form {A : Type*} [TopologicalSpace A] {f : A → B}
    {σ : A → (b : B) × V b} (hσ : D.IsHorizontalAlong f σ) (a : A) :
    ∃ v : V (f a), σ a=⟨f a,v⟩ ∧ ∀ᶠ y in 𝓝 a, σ y=⟨f y,D.forward (f a) (f y) v⟩ := by
  obtain ⟨v,hv⟩ := hσ a
  exact ⟨v,by simpa only [D.forward_self] using hv.self_of_nhds,hv⟩

lemma horizontal_base {A : Type*} [TopologicalSpace A] {f : A → B}
    {σ : A → (b : B) × V b} (hσ : D.IsHorizontalAlong f σ) (a : A) : (σ a).1=f a := by
  obtain ⟨v,hv,_⟩ := D.horizontal_local_form hσ a
  rw [hv]

 

theorem horizontal_equalizer_clopen {A : Type*} [TopologicalSpace A] {f : A → B}
    (hf : Continuous f) {σ τ : A → (b : B) × V b}
    (hσ : D.IsHorizontalAlong f σ) (hτ : D.IsHorizontalAlong f τ) :
    IsClopen {a | σ a=τ a} := by
  have hevent (a : A) : ∀ᶠ y in 𝓝 a, (σ y=τ y) ↔ (σ a=τ a) := by
    obtain ⟨v,hv,hσv⟩ := D.horizontal_local_form hσ a
    obtain ⟨w,hw,hτw⟩ := D.horizontal_local_form hτ a
    filter_upwards [hσv,hτw,hf.continuousAt ((D.domain_open (f a)).mem_nhds (D.domain_self (f a)))] with y hy hz hd
    rw [hy,hz,hv,hw]
    constructor
    · intro he
      have hvw : v=w := (D.left_inv (f a) (f y) hd).injective (sigma_mk_injective he)
      rw [hvw]
    · intro he
      rw [sigma_mk_injective he]
  constructor
  · apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    exact (hevent a).mono fun y hy he => ha (hy.mp he)
  · apply isOpen_iff_mem_nhds.mpr
    intro a ha
    exact (hevent a).mono fun y hy => hy.mpr ha

 

theorem horizontal_unique {A : Type*} [TopologicalSpace A] [ConnectedSpace A]
    {f : A → B} (hf : Continuous f) {σ τ : A → (b : B) × V b}
    (hσ : D.IsHorizontalAlong f σ) (hτ : D.IsHorizontalAlong f τ)
    (a : A) (he : σ a=τ a) : σ=τ := by
  have hu := (D.horizontal_equalizer_clopen hf hσ hτ).eq_univ ⟨a,he⟩
  exact funext fun y => show y ∈ {a | σ a=τ a} from hu ▸ mem_univ y

variable [ConnectedSpace B]

 

theorem exists_normalized_horizontal {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : A → B} (hf : Continuous f) (a : A) (v : V (f a)) :
    ∃ σ : A → (b : B) × V b, D.IsHorizontalAlong f σ ∧ σ a=⟨f a,v⟩ := by
  let : TopologicalSpace (V (f a)) := ⊥
  let : DiscreteTopology (V (f a)) := ⟨rfl⟩
  let C := D.toCocycle (f a)
  obtain ⟨s,⟨hsa,hsp⟩,_⟩ := C.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨f,hf⟩ a (D.encode (f a) (f a) v) rfl
  refine ⟨fun y => D.decode (f a) (s y),?_,?_⟩
  · intro z
    exact D.decode_lift_local_form (f a) hf hsp (D.domain_self (f z))
  · change D.decode (f a) (s a)=_
    rw [hsa,D.decode_encode]

 

theorem exists_two_chart_horizontal {f g : ℂ → B} (hf : Continuous f) (hg : Continuous g)
    (hov : ∀ z : ℂ, z ≠ 0 → f z=g z⁻¹) (a : ℂ) (v : V (f a)) :
    ∃ σ τ : ℂ → (b : B) × V b,
      D.IsHorizontalAlong f σ ∧ D.IsHorizontalAlong g τ ∧ σ a=⟨f a,v⟩ ∧
      ∀ z : ℂ, z ≠ 0 → σ z=τ z⁻¹ := by
  let : TopologicalSpace (V (f a)) := ⊥
  let : DiscreteTopology (V (f a)) := ⟨rfl⟩
  let C := D.toCocycle (f a)
  obtain ⟨F,G,hFa,hFp,hGp,hFG⟩ := C.exists_two_chart_lifts hf hg hov a
    (D.encode (f a) (f a) v) rfl
  refine ⟨fun z => D.decode (f a) (F z),fun z => D.decode (f a) (G z),?_,?_,?_,?_⟩
  · intro z
    exact D.decode_lift_local_form (f a) hf hFp (D.domain_self (f z))
  · intro z
    exact D.decode_lift_local_form (f a) hg hGp (D.domain_self (g z))
  · change D.decode (f a) (F a)=_
    rw [hFa,D.decode_encode]
  · intro z hz
    change D.decode (f a) (F z)=D.decode (f a) (G z⁻¹)
    rw [hFG z hz]

end SplitTangent.HorizontalCovering.LocalTransportData

namespace SplitTangent.PullbackConnection
section
open HorizontalCovering Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
abbrev ImageFiber (P : E → E →L[ℂ] E) (g : ℂ → E) (z : ℂ) :=
  {v : E // P (g z) v=v}

 

structure LocalImages (P : E → E →L[ℂ] E) (g : ℂ → E) where
  radius : ℂ → ℝ
  positive : ∀ x, 0 < radius x
  trans : ℂ → ℂ → ℂ → E →L[ℂ] E
  analytic : ∀ x, AnalyticOnNhd ℂ (fun w : ℂ × ℂ => trans x w.1 w.2)
    (Metric.ball x (radius x) ×ˢ Metric.ball x (radius x))
  normalized : ∀ x s, s ∈ Metric.ball x (radius x) → trans x s s=1
  cocycle : ∀ x s, s ∈ Metric.ball x (radius x) → ∀ t, t ∈ Metric.ball x (radius x) →
    ∀ u, u ∈ Metric.ball x (radius x) → trans x t u*trans x s t=trans x s u
  preserves_horizontal : ∀ x s, s ∈ Metric.ball x (radius x) → ∀ t, t ∈ Metric.ball x (radius x) →
    ∀ v, P (g s) v=v → P (g t) (trans x s t v)=trans x s t v ∧
      covariantDerivative P g (fun w => trans x s w v) t=0

namespace LocalImages
variable {P : E → E →L[ℂ] E} {g : ℂ → E} (L : LocalImages P g)

omit [CompleteSpace E] in
lemma center (x : ℂ) : x ∈ Metric.ball x (L.radius x) := Metric.mem_ball_self (L.positive x)

omit [CompleteSpace E] in
lemma trans_analytic {x s t : ℂ} (hs : s ∈ Metric.ball x (L.radius x))
    (ht : t ∈ Metric.ball x (L.radius x)) (v : E) :
    AnalyticAt ℂ (fun w => L.trans x s w v) t := by
  have h := (L.analytic x (s,t) ⟨hs,ht⟩).comp (analyticAt_const.prod analyticAt_id)
  exact ((ContinuousLinearMap.apply ℂ E (E := E)).analyticAt_bilinear _).comp (analyticAt_const.prod h)

def forward (x y : ℂ) (v : ImageFiber P g x) : ImageFiber P g y := by
  classical
  exact if hy : y ∈ Metric.ball x (L.radius x) then
    ⟨L.trans x x y v,(L.preserves_horizontal x x (L.center x) y hy v v.2).1⟩
  else ⟨0,by simp⟩

def reverse (x y : ℂ) (v : ImageFiber P g y) : ImageFiber P g x := by
  classical
  exact if hy : y ∈ Metric.ball x (L.radius x) then
    ⟨L.trans x y x v,(L.preserves_horizontal x y hy x (L.center x) v v.2).1⟩
  else ⟨0,by simp⟩

omit [CompleteSpace E] in
lemma forward_val {x y : ℂ} (hy : y ∈ Metric.ball x (L.radius x)) (v : ImageFiber P g x) :
    (L.forward x y v).1=L.trans x x y v := by simp only [forward,dite_eq_left hy]
omit [CompleteSpace E] in
lemma reverse_val {x y : ℂ} (hy : y ∈ Metric.ball x (L.radius x)) (v : ImageFiber P g y) :
    (L.reverse x y v).1=L.trans x y x v := by simp only [reverse,dite_eq_left hy]

omit [CompleteSpace E] in
lemma left_inverse {x y : ℂ} (hy : y ∈ Metric.ball x (L.radius x)) :
    Function.LeftInverse (L.reverse x y) (L.forward x y) := by
  intro v
  apply Subtype.ext
  rw [L.reverse_val hy,L.forward_val hy]
  have he := congrArg (fun A : E →L[ℂ] E => A v)
    (L.cocycle x x (L.center x) y hy x (L.center x))
  simpa only [L.normalized x x (L.center x),mul_apply_eq_comp,
    one_apply_eq_self] using he

omit [CompleteSpace E] in
lemma right_inverse {x y : ℂ} (hy : y ∈ Metric.ball x (L.radius x)) :
    Function.RightInverse (L.reverse x y) (L.forward x y) := by
  intro v
  apply Subtype.ext
  rw [L.forward_val hy,L.reverse_val hy]
  have he := congrArg (fun A : E →L[ℂ] E => A v)
    (L.cocycle x y hy x (L.center x) y hy)
  simpa only [L.normalized x y hy,mul_apply_eq_comp,
    one_apply_eq_self] using he

omit [CompleteSpace E] in
lemma normalized_forward (x : ℂ) (v : ImageFiber P g x) : L.forward x x v=v := by
  apply Subtype.ext
  rw [L.forward_val (L.center x),L.normalized x x (L.center x),one_apply_eq_self]

 
lemma overlap (hP : ∀ z, AnalyticAt ℂ P (g z)) (hg : AnalyticOnNhd ℂ g univ)
    (hid : ∀ z, ∀ᶠ y in 𝓝 (g z), P y*P y=P y)
    (x y z : ℂ) (hz : z ∈ Metric.ball x (L.radius x) ∩ Metric.ball y (L.radius y))
    (v : ImageFiber P g x) :
    ∀ᶠ w in 𝓝 z, L.forward y w (L.reverse y z (L.forward x z v))=L.forward x w v := by
  let u : ImageFiber P g y := L.reverse y z (L.forward x z v)
  have he : L.trans y y z u=L.trans x x z v := by
    have hinv := congrArg Subtype.val (L.right_inverse hz.2 (L.forward x z v))
    simpa only [L.forward_val hz.2,L.forward_val hz.1] using hinv
  have huniq : (fun w => L.trans y y w u) =ᶠ[𝓝 z] (fun w => L.trans x x w v) := by
    apply horizontal_local_uniqueness (hP z) (hg z (mem_univ z)) (hid z) _ _ _ _ he
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with w hw
      exact ⟨(L.trans_analytic (L.center y) hw u).differentiableAt,
        (L.preserves_horizontal y y (L.center y) w hw u u.2).2⟩
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz.1] with w hw
      exact ⟨(L.trans_analytic (L.center x) hw v).differentiableAt,
        (L.preserves_horizontal x x (L.center x) w hw v v.2).2⟩
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with w hw
      exact (L.preserves_horizontal y y (L.center y) w hw u u.2).1
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz.1] with w hw
      exact (L.preserves_horizontal x x (L.center x) w hw v v.2).1
  filter_upwards [huniq,Metric.isOpen_ball.mem_nhds hz.1,Metric.isOpen_ball.mem_nhds hz.2] with w he hx hy
  apply Subtype.ext
  rw [L.forward_val hy,L.forward_val hx]
  exact he

 

def toData (hP : ∀ z, AnalyticAt ℂ P (g z)) (hg : AnalyticOnNhd ℂ g univ)
    (hid : ∀ z, ∀ᶠ y in 𝓝 (g z), P y*P y=P y) :
    LocalTransportData ℂ (ImageFiber P g) where
  domain := fun x => Metric.ball x (L.radius x)
  domain_open := fun _ => Metric.isOpen_ball
  domain_self := L.center
  forward := L.forward
  reverse := L.reverse
  left_inv := fun _ _ hy => L.left_inverse hy
  right_inv := fun _ _ hy => L.right_inverse hy
  forward_self := L.normalized_forward
  overlap := L.overlap hP hg hid

end LocalImages

 

theorem exists_local_images {P : E → E →L[ℂ] E} {g : ℂ → E}
    (hP : ∀ z, AnalyticAt ℂ P (g z)) (hg : AnalyticOnNhd ℂ g univ)
    (hid : ∀ z, ∀ᶠ y in 𝓝 (g z), P y*P y=P y) : Nonempty (LocalImages P g) := by
  have hex := fun z => exists_local_horizontal_transport (hP z) (hg z (mem_univ z)) (hid z)
  choose r hr T hTa hT0 hTu hTc hTh using hex
  exact ⟨⟨r,hr,T,hTa,hT0,hTc,hTh⟩⟩

end

open HorizontalCovering Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
omit [CompleteSpace E] in
lemma covariantDerivative_congr {P : E → E →L[ℂ] E} {g f h : ℂ → E} {z : ℂ}
    (he : f =ᶠ[𝓝 z] h) : covariantDerivative P g f z=covariantDerivative P g h z := by
  simp only [covariantDerivative,he.deriv_eq,he.self_of_nhds]

 

theorem exists_entire_horizontal {P : E → E →L[ℂ] E} {g : ℂ → E}
    (hP : ∀ z, AnalyticAt ℂ P (g z)) (hg : AnalyticOnNhd ℂ g univ)
    (hid : ∀ z, ∀ᶠ y in 𝓝 (g z), P y*P y=P y)
    (a : ℂ) (v : E) (hv : P (g a) v=v) :
    ∃ s : ℂ → E, AnalyticOnNhd ℂ s univ ∧ s a=v ∧
      (∀ z, P (g z) (s z)=s z) ∧ ∀ z, covariantDerivative P g s z=0 := by
  obtain ⟨L⟩ := exists_local_images hP hg hid
  let D := L.toData hP hg hid
  obtain ⟨σ,hσ,hσa⟩ := D.exists_normalized_horizontal continuous_id a (⟨v,hv⟩ : ImageFiber P g a)
  let s : ℂ → E := fun z => (σ z).2.1
  have hbase (z : ℂ) : (σ z).1=z := D.horizontal_base hσ z
  have hlocal (z : ℂ) : ∃ u : ImageFiber P g z,
      s =ᶠ[𝓝 z] fun w => L.trans z z w u := by
    obtain ⟨u,hu⟩ := hσ z
    refine ⟨u,?_⟩
    filter_upwards [hu,Metric.isOpen_ball.mem_nhds (L.center z)] with w hw hm
    change (σ w).2.1=L.trans z z w u
    rw [hw]
    exact L.forward_val hm u
  refine ⟨s,?_,?_,?_,?_⟩
  · intro z _
    obtain ⟨u,hu⟩ := hlocal z
    exact (L.trans_analytic (L.center z) (L.center z) u).congr hu.symm
  · change (σ a).2.1=v
    rw [hσa]
  · intro z
    have hi : P (g (σ z).1) (s z)=s z := (σ z).2.2
    rwa [hbase z] at hi
  · intro z
    obtain ⟨u,hu⟩ := hlocal z
    rw [covariantDerivative_congr hu]
    exact (L.preserves_horizontal z z (L.center z) z (L.center z) u u.2).2

 
theorem entire_horizontal_unique {P : E → E →L[ℂ] E} {g f h : ℂ → E}
    (hP : ∀ z, AnalyticAt ℂ P (g z)) (hg : AnalyticOnNhd ℂ g univ)
    (hid : ∀ z, ∀ᶠ y in 𝓝 (g z), P y*P y=P y)
    (hf : AnalyticOnNhd ℂ f univ) (hh : AnalyticOnNhd ℂ h univ)
    (hfi : ∀ z, P (g z) (f z)=f z) (hhi : ∀ z, P (g z) (h z)=h z)
    (hfh : ∀ z, covariantDerivative P g f z=0)
    (hhh : ∀ z, covariantDerivative P g h z=0)
    (a : ℂ) (he : f a=h a) : f=h := by
  have h := horizontal_eqOn isOpen_univ isPreconnected_univ (fun z _ => hP z)
    hg hf hh (fun z _ => hid z) (fun z _ => hfi z) (fun z _ => hhi z)
    (fun z _ => hfh z) (fun z _ => hhh z) (mem_univ a) he
  exact funext fun z => h (mem_univ z)

end SplitTangent.PullbackConnection

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

namespace SplitTangent.TangentSplitting
section
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem coordinateProjector_analytic (x : X.Carrier) :
    AnalyticOnNhd ℂ (S.coordinateProjector x) (chartAt (Model X) x).target := by
  let e : Matrix (Fin X.dim) (Fin X.dim) ℂ ≃L[ℂ] (Model X →L[ℂ] Model X) :=
    (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  intro z hz
  have hM : AnalyticAt ℂ (fun z i j => S.coordinateMatrix x i j z) z := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    exact S.coordinateMatrix_analytic x i j z hz
  have he : (fun z => e (fun i j => S.coordinateMatrix x i j z))=S.coordinateProjector x := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    change Matrix.toLin' (LinearMap.toMatrix' (S.coordinateProjector x z).toLinearMap) v=_
    rw [Matrix.toLin'_toMatrix']
    rfl
  rw [← he]
  exact (e.toContinuousLinearMap.analyticAt _).comp hM

lemma coordinateProjector_fixed (x : X.Carrier) {y : X.Carrier}
    (hy : y ∈ (chartAt (Model X) x).source) (v : Tangent X y) :
    S.coordinateProjector x ((chartAt (Model X) x) y)
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ y v) =
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ y (S.projector y v) := by
  dsimp only [coordinateProjector]
  rw [(chartAt (Model X) x).left_inv hy]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hy]

lemma coordinateCurve_analytic {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) {z : ℂ}
    (hz : g z ∈ (chartAt (Model X) x).source) :
    AnalyticAt ℂ ((chartAt (Model X) x) ∘ g) z := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z (hg z)).contDiffAt.analyticAt

lemma coordinateCurve_derivative {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) {z : ℂ}
    (hz : g z ∈ (chartAt (Model X) x).source) :
    deriv ((chartAt (Model X) x) ∘ g) z =
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g z)
        (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ)) := by
  have hc := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz).mdifferentiableAt (by simp)
  have he := mfderiv_comp_apply z hc ((hg z).mdifferentiableAt (by simp)) (1 : ℂ)
  rw [mfderiv_eq_fderiv] at he
  change (fderiv ℂ ((chartAt (Model X) x) ∘ g) z) (1 : ℂ) =
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ)) at he
  rw [fderiv_eq_smul_deriv,one_smul] at he
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hz
  rw [ht]
  change deriv ((chartAt (Model X) x) ∘ g) z =
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))
  exact he

lemma coordinateCurve_complementary {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (x : X.Carrier) {z : ℂ} (hz : g z ∈ (chartAt (Model X) x).source) :
    S.coordinateProjector x ((chartAt (Model X) x) (g z))
      (deriv ((chartAt (Model X) x) ∘ g) z)=0 := by
  rw [coordinateCurve_derivative hg x hz,S.coordinateProjector_fixed x hz,hv z,map_zero]

 
lemma coordinateProjector_eventually_idempotent (x : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target) :
    ∀ᶠ w in 𝓝 z, S.coordinateProjector x w*S.coordinateProjector x w=S.coordinateProjector x w := by
  filter_upwards [(chartAt (Model X) x).open_target.mem_nhds hz] with w hw
  apply ContinuousLinearMap.ext
  intro v
  exact S.coordinateProjector_idempotent x hw v

 

theorem exists_manifold_local_transport {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (a : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → Model X →L[ℂ] Model X,
      (∀ z ∈ Metric.ball a ε, g z ∈ (chartAt (Model X) (g a)).source) ∧
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2) (Metric.ball a ε ×ˢ Metric.ball a ε) ∧
      (∀ s ∈ Metric.ball a ε, T s s=1) ∧
      (∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε, ∀ u ∈ Metric.ball a ε, T t u*T s t=T s u) ∧
      (∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε, ∀ v : Model X,
        S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g s)) v=v →
        S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g t)) (T s t v)=T s t v ∧
        PullbackConnection.covariantDerivative (S.coordinateProjector (g a))
          ((chartAt (Model X) (g a)) ∘ g) (fun w => T s w v) t=0) := by
  let c := chartAt (Model X) (g a)
  have ha : g a ∈ c.source := mem_chart_source (Model X) (g a)
  have hat : c (g a) ∈ c.target := c.map_source ha
  obtain ⟨r,hr,T,hTa,hT0,_,hTc,hTh⟩ := PullbackConnection.exists_local_horizontal_transport
    (S.coordinateProjector_analytic (g a) _ hat) (coordinateCurve_analytic hg (g a) ha)
    (S.coordinateProjector_eventually_idempotent (g a) hat)
  obtain ⟨q,hq,hqn⟩ := Metric.eventually_nhds_iff_ball.mp (hg.continuous.continuousAt (c.open_source.mem_nhds ha))
  have hrm : Metric.ball a (min r q) ⊆ Metric.ball a r := Metric.ball_subset_ball (min_le_left _ _)
  have hqm : Metric.ball a (min r q) ⊆ Metric.ball a q := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r q,lt_min hr hq,T,?_,?_,?_,?_,?_⟩
  · exact fun z hz => hqn z (hqm hz)
  · exact hTa.mono (Set.prod_mono hrm hrm)
  · exact fun s hs => hT0 s (hrm hs)
  · exact fun s hs t ht u hu => hTc s (hrm hs) t (hrm ht) u (hrm hu)
  · exact fun s hs t ht v hv => hTh s (hrm hs) t (hrm ht) v hv

end

open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

abbrev TangentImageFiber (g : ℂ → X.Carrier) (z : ℂ) :=
  {v : Tangent X (g z) // S.projector (g z) v=v}

 

structure LocalChartImages (g : ℂ → X.Carrier) where
  radius : ℂ → ℝ
  positive : ∀ a, 0 < radius a
  chart_source : ∀ a z, z ∈ Metric.ball a (radius a) → g z ∈ (chartAt (Model X) (g a)).source
  trans : ℂ → ℂ → ℂ → Model X →L[ℂ] Model X
  analytic : ∀ a, AnalyticOnNhd ℂ (fun w : ℂ × ℂ => trans a w.1 w.2)
    (Metric.ball a (radius a) ×ˢ Metric.ball a (radius a))
  normalized : ∀ a s, s ∈ Metric.ball a (radius a) → trans a s s=1
  cocycle : ∀ a s, s ∈ Metric.ball a (radius a) → ∀ t, t ∈ Metric.ball a (radius a) →
    ∀ u, u ∈ Metric.ball a (radius a) → trans a t u*trans a s t=trans a s u
  horizontal : ∀ a s, s ∈ Metric.ball a (radius a) → ∀ t, t ∈ Metric.ball a (radius a) →
    ∀ v : Model X, S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g s)) v=v →
      S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g t)) (trans a s t v)=trans a s t v ∧
      covariantDerivative (S.coordinateProjector (g a)) ((chartAt (Model X) (g a)) ∘ g)
        (fun w => trans a s w v) t=0

namespace LocalChartImages
variable {S} {g : ℂ → X.Carrier} (L : LocalChartImages S g)

abbrev frame (_L : LocalChartImages S g) (a : ℂ) := trivializationAt (Model X) (Tangent X) (g a)
abbrev coords (a z : ℂ) := (L.frame a).continuousLinearMapAt ℂ (g z)
abbrev uncoords (a z : ℂ) := (L.frame a).symmL ℂ (g z)

lemma center (a : ℂ) : a ∈ Metric.ball a (L.radius a) := Metric.mem_ball_self (L.positive a)
lemma frame_mem {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) : g z ∈ (L.frame a).baseSet :=
  L.chart_source a z hz
lemma uncoords_coords {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : Tangent X (g z)) :
    L.uncoords a z (L.coords a z v)=v := (L.frame a).symmL_continuousLinearMapAt (L.frame_mem hz) v
lemma coords_uncoords {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : Model X) :
    L.coords a z (L.uncoords a z v)=v := (L.frame a).continuousLinearMapAt_symmL (L.frame_mem hz) v

lemma coords_fixed {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : TangentImageFiber S g z) :
    S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g z)) (L.coords a z v)=L.coords a z v := by
  rw [S.coordinateProjector_fixed (g a) (L.chart_source a z hz),v.2]

lemma uncoords_fixed {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) {v : Model X}
    (hv : S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g z)) v=v) :
    S.projector (g z) (L.uncoords a z v)=L.uncoords a z v := by
  have h := S.coordinateProjector_fixed (g a) (L.chart_source a z hz) (L.uncoords a z v)
  change S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g z))
    (L.coords a z (L.uncoords a z v))=L.coords a z (S.projector (g z) (L.uncoords a z v)) at h
  rw [L.coords_uncoords hz,hv] at h
  have he := congrArg (L.uncoords a z) h
  rw [L.uncoords_coords hz] at he
  exact he.symm

lemma trans_analytic {a s t : ℂ} (hs : s ∈ Metric.ball a (L.radius a))
    (ht : t ∈ Metric.ball a (L.radius a)) (v : Model X) :
    AnalyticAt ℂ (fun w => L.trans a s w v) t := by
  have h := (L.analytic a (s,t) ⟨hs,ht⟩).comp (analyticAt_const.prod analyticAt_id)
  exact ((ContinuousLinearMap.apply ℂ (Model X) (E := Model X)).analyticAt_bilinear _).comp (analyticAt_const.prod h)

def forward (a z : ℂ) (v : TangentImageFiber S g a) : TangentImageFiber S g z := by
  classical
  exact if hz : z ∈ Metric.ball a (L.radius a) then
    ⟨L.uncoords a z (L.trans a a z (L.coords a a v)),
      L.uncoords_fixed hz ((L.horizontal a a (L.center a) z hz _ (L.coords_fixed (L.center a) v)).1)⟩
  else ⟨0,by simp⟩

def reverse (a z : ℂ) (v : TangentImageFiber S g z) : TangentImageFiber S g a := by
  classical
  exact if hz : z ∈ Metric.ball a (L.radius a) then
    ⟨L.uncoords a a (L.trans a z a (L.coords a z v)),
      L.uncoords_fixed (L.center a) ((L.horizontal a z hz a (L.center a) _ (L.coords_fixed hz v)).1)⟩
  else ⟨0,by simp⟩

lemma forward_val {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : TangentImageFiber S g a) :
    (L.forward a z v).1=L.uncoords a z (L.trans a a z (L.coords a a v)) := by
  simp only [forward,dite_eq_left hz]
lemma reverse_val {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : TangentImageFiber S g z) :
    (L.reverse a z v).1=L.uncoords a a (L.trans a z a (L.coords a z v)) := by
  simp only [reverse,dite_eq_left hz]

lemma left_inverse {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) :
    Function.LeftInverse (L.reverse a z) (L.forward a z) := by
  intro v
  apply Subtype.ext
  rw [L.reverse_val hz,L.forward_val hz,L.coords_uncoords hz]
  have he := congrArg (fun A : Model X →L[ℂ] Model X => A (L.coords a a v))
    (L.cocycle a a (L.center a) z hz a (L.center a))
  rw [L.normalized a a (L.center a)] at he
  change L.uncoords a a (L.trans a z a (L.trans a a z (L.coords a a v)))=v
  rw [show L.trans a z a (L.trans a a z (L.coords a a v))=L.coords a a v from he]
  exact L.uncoords_coords (L.center a) v

lemma right_inverse {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) :
    Function.RightInverse (L.reverse a z) (L.forward a z) := by
  intro v
  apply Subtype.ext
  rw [L.forward_val hz,L.reverse_val hz,L.coords_uncoords (L.center a)]
  have he := congrArg (fun A : Model X →L[ℂ] Model X => A (L.coords a z v))
    (L.cocycle a z hz a (L.center a) z hz)
  rw [L.normalized a z hz] at he
  change L.uncoords a z (L.trans a a z (L.trans a z a (L.coords a z v)))=v
  rw [show L.trans a a z (L.trans a z a (L.coords a z v))=L.coords a z v from he]
  exact L.uncoords_coords hz v

lemma normalized_forward (a : ℂ) (v : TangentImageFiber S g a) : L.forward a a v=v := by
  apply Subtype.ext
  rw [L.forward_val (L.center a),L.normalized a a (L.center a),one_apply_eq_self]
  exact L.uncoords_coords (L.center a) v

end LocalChartImages

 

theorem exists_local_chart_images {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) : Nonempty (LocalChartImages S g) := by
  have h := fun a => S.exists_manifold_local_transport hg a
  choose r hr T hsrc hTa hTn hTc hTh using h
  exact ⟨⟨r,hr,hsrc,T,hTa,hTn,hTc,hTh⟩⟩

end SplitTangent.TangentSplitting

namespace SplitTangent.PullbackConnection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma covariantDerivative_curve_congr {P : E → E →L[ℂ] E} {g h v : ℂ → E} {z : ℂ}
    (he : g =ᶠ[𝓝 z] h) : covariantDerivative P g v z=covariantDerivative P h v z := by
  simp only [covariantDerivative,coefficient,he.eq_of_nhds,he.deriv_eq]
end SplitTangent.PullbackConnection

namespace SplitTangent.TangentSplitting.LocalChartImages
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)

lemma transition_curve {a b z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) :
    coordinateTransition (g a) (g b) ((chartAt (Model X) (g a)) (g z)) =
      (chartAt (Model X) (g b)) (g z) := by
  dsimp only [coordinateTransition,Function.comp_apply]
  rw [(chartAt (Model X) (g a)).left_inv (L.chart_source a z hz)]

lemma transition_derivative {a b z : ℂ} (ha : z ∈ Metric.ball a (L.radius a))
    (hb : z ∈ Metric.ball b (L.radius b)) :
    fderiv ℂ (coordinateTransition (g a) (g b)) ((chartAt (Model X) (g a)) (g z)) =
      (L.coords b z).comp (L.uncoords a z) := by
  have hsa := L.chart_source a z ha
  have hsb := L.chart_source b z hb
  have he := (chartAt (Model X) (g a)).left_inv hsa
  rw [coordinateTransition_derivative (g a) (g b) ((chartAt (Model X) (g a)).map_source hsa)
    (by rw [he]; exact hsb),he]

lemma overlap_locally_unique
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    {a b z : ℂ} (ha : z ∈ Metric.ball a (L.radius a)) (hb : z ∈ Metric.ball b (L.radius b))
    (v : TangentImageFiber S g a) :
    ∀ᶠ w in 𝓝 z, L.forward b w (L.reverse b z (L.forward a z v))=L.forward a w v := by
  let c := chartAt (Model X) (g a)
  let d := chartAt (Model X) (g b)
  let φ := coordinateTransition (g a) (g b)
  let P := S.coordinateProjector (g a)
  let Q := S.coordinateProjector (g b)
  let u := L.reverse b z (L.forward a z v)
  let f := fun w => L.trans a a w (L.coords a a v)
  let h := fun w => L.trans b b w (L.coords b b u)
  have hsa : g z ∈ c.source := L.chart_source a z ha
  have hsb : g z ∈ d.source := L.chart_source b z hb
  have he : c.symm (c (g z))=g z := c.left_inv hsa
  have hφ : φ (c (g z))=d (g z) := L.transition_curve ha
  have hhp : AnalyticAt ℂ P (c (g z)) := S.coordinateProjector_analytic (g a) _ (c.map_source hsa)
  have hhq : AnalyticAt ℂ Q (φ (c (g z))) := by
    rw [hφ]
    exact S.coordinateProjector_analytic (g b) _ (d.map_source hsb)
  have hha : AnalyticAt ℂ φ (c (g z)) := coordinateTransition_analytic (g a) (g b)
    (c.map_source hsa) (by change c.symm (c (g z)) ∈ d.source; rw [he]; exact hsb)
  have hiq : ∀ᶠ y in 𝓝 (φ (c (g z))), Q y*Q y=Q y := by
    rw [hφ]
    exact S.coordinateProjector_eventually_idempotent (g b) (d.map_source hsb)
  have hnat : ∀ᶠ y in 𝓝 (c (g z)), ∀ t : Model X,
      Q (φ y) (fderiv ℂ φ y t)=fderiv ℂ φ y (P y t) := by
    have hcn : ContinuousAt c.symm (c (g z)) := c.continuousAt_symm (c.map_source hsa)
    have hy : ∀ᶠ y in 𝓝 (c (g z)), c.symm y ∈ d.source :=
      hcn (d.open_source.mem_nhds (by rw [he]; exact hsb))
    filter_upwards [c.open_target.mem_nhds (c.map_source hsa),hy] with y hy hy'
    intro t
    exact (congrArg (fun A : Model X →L[ℂ] Model X => A t)
      (S.coordinateProjector_intertwining (g a) (g b) hy hy')).symm
  have hnA : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball a (L.radius a) := Metric.isOpen_ball.mem_nhds ha
  have hnB : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball b (L.radius b) := Metric.isOpen_ball.mem_nhds hb
  have hcur : (φ ∘ (c ∘ g)) =ᶠ[𝓝 z] d ∘ g := by
    filter_upwards [hnA] with w hw
    exact L.transition_curve hw
  have hcur' := eventually_eventually_nhds.mpr hcur
  have hvel : ∀ᶠ w in 𝓝 z, P ((c ∘ g) w) (deriv (c ∘ g) w)=0 := by
    filter_upwards [hnA] with w hw
    exact S.coordinateCurve_complementary hg hv (g a) (L.chart_source a w hw)
  have hfi : ∀ᶠ w in 𝓝 z, P ((c ∘ g) w) (f w)=f w := by
    filter_upwards [hnA] with w hw
    exact (L.horizontal a a (L.center a) w hw _ (L.coords_fixed (L.center a) v)).1
  have hhi : ∀ᶠ w in 𝓝 z, Q (φ ((c ∘ g) w)) (h w)=h w := by
    filter_upwards [hnA,hnB] with w hw hw'
    rw [show φ ((c ∘ g) w)=d (g w) from L.transition_curve hw]
    exact (L.horizontal b b (L.center b) w hw' _ (L.coords_fixed (L.center b) u)).1
  have hfh : ∀ᶠ w in 𝓝 z, covariantDerivative P (c ∘ g) f w=0 := by
    filter_upwards [hnA] with w hw
    exact (L.horizontal a a (L.center a) w hw _ (L.coords_fixed (L.center a) v)).2
  have hhh : ∀ᶠ w in 𝓝 z, covariantDerivative Q (φ ∘ (c ∘ g)) h w=0 := by
    filter_upwards [hnB,hcur'] with w hw hc
    rw [covariantDerivative_curve_congr hc]
    exact (L.horizontal b b (L.center b) w hw _ (L.coords_fixed (L.center b) u)).2
  have hstart : h z=fderiv ℂ φ ((c ∘ g) z) (f z) := by
    have hs := congrArg (fun t : TangentImageFiber S g z => L.coords b z t.1)
      (L.right_inverse hb (L.forward a z v))
    rw [L.forward_val hb,L.forward_val ha,L.coords_uncoords hb] at hs
    rw [show fderiv ℂ φ ((c ∘ g) z)=(L.coords b z).comp (L.uncoords a z) from
      L.transition_derivative ha hb]
    exact hs
  have hu := horizontal_chart_compatibility hhp hhq hha (coordinateCurve_analytic hg (g a) hsa)
    (L.trans_analytic (L.center a) ha _) (L.trans_analytic (L.center b) hb _)
    hiq hnat hvel hfi hhi hfh hhh hstart
  filter_upwards [hu,hnA,hnB] with w hw hwA hwB
  apply Subtype.ext
  rw [L.forward_val hwB,L.forward_val hwA]
  change L.uncoords b w (h w)=L.uncoords a w (f w)
  change h w=fderiv ℂ φ ((c ∘ g) w) (f w) at hw
  rw [hw,show fderiv ℂ φ ((c ∘ g) w)=(L.coords b w).comp (L.uncoords a w) from
    L.transition_derivative hwA hwB,ContinuousLinearMap.comp_apply,L.uncoords_coords hwB]

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

namespace LocalChartImages
variable {S} {g : ℂ → X.Carrier} (L : LocalChartImages S g)

 

def toData (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0) :
    LocalTransportData ℂ (TangentImageFiber S g) where
  domain := fun a => Metric.ball a (L.radius a)
  domain_open := fun _ => Metric.isOpen_ball
  domain_self := L.center
  forward := L.forward
  reverse := L.reverse
  left_inv := fun _ _ hz => L.left_inverse hz
  right_inv := fun _ _ hz => L.right_inverse hz
  forward_self := L.normalized_forward
  overlap := fun _ _ _ hz v => L.overlap_locally_unique hg hv hz.1 hz.2 v

end LocalChartImages

 

theorem exists_manifold_horizontal {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (a : ℂ) (v : Tangent X (g a)) (hvi : S.projector (g a) v=v) :
    ∃ s : ∀ z, Tangent X (g z),
      ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
        (fun z => (⟨g z,s z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) ∧
      s a=v ∧ (∀ z, S.projector (g z) (s z)=s z) ∧
      ∀ z, covariantDerivative (S.coordinateProjector (g z)) ((chartAt (Model X) (g z)) ∘ g)
        (fun w => (trivializationAt (Model X) (Tangent X) (g z)).continuousLinearMapAt ℂ (g w) (s w)) z=0 := by
  obtain ⟨L⟩ := S.exists_local_chart_images hg
  let D := L.toData hg hv
  obtain ⟨σ,hσ,hσa⟩ := D.exists_normalized_horizontal continuous_id a (⟨v,hvi⟩ : TangentImageFiber S g a)
  let s : ∀ z, Tangent X (g z) := fun z => (σ z).2.1
  have hbase (z : ℂ) : (σ z).1=z := D.horizontal_base hσ z
  have hlocal (z : ℂ) : ∃ u : TangentImageFiber S g z,
      (fun w => L.coords z w (s w)) =ᶠ[𝓝 z] fun w => L.trans z z w (L.coords z z u) := by
    obtain ⟨u,hu⟩ := hσ z
    refine ⟨u,?_⟩
    filter_upwards [hu,Metric.isOpen_ball.mem_nhds (L.center z)] with w hw hm
    change L.coords z w ((σ w).2.1)=_
    rw [hw]
    change L.coords z w (L.forward z w u).1=_
    rw [L.forward_val hm,L.coords_uncoords hm]
  refine ⟨s,?_,?_,?_,?_⟩
  · intro z
    obtain ⟨u,hu⟩ := hlocal z
    have han : AnalyticAt ℂ (fun w => L.coords z w (s w)) z :=
      (L.trans_analytic (L.center z) (L.center z) _).congr hu.symm
    let t := trivializationAt (Model X) (Tangent X) (g z)
    have hz : g z ∈ t.baseSet := L.frame_mem (L.center z)
    apply (t.contMDiffAt_iff (f := fun w => (⟨g w,s w⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
      (by simpa only [t.mem_source] using hz)).mpr
    refine ⟨hg z,?_⟩
    apply han.contDiffAt.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [Metric.isOpen_ball.mem_nhds (L.center z)] with w hw
    exact (t.continuousLinearMapAt_apply_of_mem ℂ (L.frame_mem hw) (s w)).symm
  · change (σ a).2.1=v
    rw [hσa]
  · intro z
    have hi : S.projector (g (σ z).1) (s z)=s z := (σ z).2.2
    rwa [hbase z] at hi
  · intro z
    obtain ⟨u,hu⟩ := hlocal z
    rw [covariantDerivative_congr hu]
    exact (L.horizontal z z (L.center z) z (L.center z) _ (L.coords_fixed (L.center z) u)).2

end SplitTangent.TangentSplitting

open Filter Topology
namespace SplitTangent.AnalyticContinuation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

theorem subset_of_local_analytic_equations {U Z : Set E} (hU : IsPreconnected U)
    (hlocal : ∀ x ∈ U, ∃ f : E → F, AnalyticAt ℂ f x ∧
      ∀ᶠ y in 𝓝 x, y ∈ Z ↔ f y = 0)
    (hne : (U ∩ interior Z).Nonempty) : U ⊆ Z := by
  suffices U ⊆ interior Z from this.trans interior_subset
  apply hU.subset_of_closure_inter_subset isOpen_interior hne
  rintro x ⟨hx,hxU⟩
  obtain ⟨f,hf,he⟩ := hlocal x hxU
  have hn : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ f y ∧ (y ∈ Z ↔ f y = 0) :=
    hf.eventually_analyticAt.and he
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨y,hy,hyI⟩ := mem_closure_iff.mp hx (Metric.ball x r) Metric.isOpen_ball
    (Metric.mem_ball_self hr)
  have hzero : f =ᶠ[𝓝 y] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy,isOpen_interior.mem_nhds hyI] with a ha hai
    exact (hrsub ha).2.mp (interior_subset hai)
  have ha : AnalyticOnNhd ℂ f (Metric.ball x r) := fun a ha => (hrsub ha).1
  have hball : Set.EqOn f 0 (Metric.ball x r) :=
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball x r).isPreconnected hy hzero
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hr)
  intro y hy
  exact (hrsub hy).2.mpr (hball hy)

end SplitTangent.AnalyticContinuation

namespace SplitTangent.AnalyticManifoldMaps
open Filter Topology Set
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold 𝓘(ℂ,H) ω M] [T2Space M]

omit [CompleteSpace H] in
lemma equality_local_equations {F G : E → M} {z : E}
    (hF : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,H) ω F z)
    (hG : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,H) ω G z) :
    ∃ f : E → ℂ × H, AnalyticAt ℂ f z ∧
      ∀ᶠ w in 𝓝 z, F w = G w ↔ f w = 0 := by
  classical
  by_cases he : F z = G z
  · let c := chartAt H (F z)
    have hFc : F z ∈ c.source := mem_chart_source H (F z)
    have hGc : G z ∈ c.source := he ▸ hFc
    have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ,H)) (n := ω) (F z)
    have hFA := ((contMDiffAt_of_mem_maximalAtlas hc hFc).comp z hF).contDiffAt.analyticAt
    have hGA := ((contMDiffAt_of_mem_maximalAtlas hc hGc).comp z hG).contDiffAt.analyticAt
    refine ⟨fun w => (0,c (F w)-c (G w)), analyticAt_const.prod (hFA.sub hGA),?_⟩
    filter_upwards [hF.continuousAt.eventually (c.open_source.mem_nhds hFc),
      hG.continuousAt.eventually (c.open_source.mem_nhds hGc)] with w hwF hwG
    constructor
    · intro h; simp only [h,sub_self,Prod.zero_eq_mk]
    · intro h
      have hh := congrArg Prod.snd h
      exact c.injOn hwF hwG (sub_eq_zero.mp hh)
  · refine ⟨fun _ => (1,0),analyticAt_const,?_⟩
    have hn : ∀ᶠ w in 𝓝 z, F w ≠ G w :=
      (hF.continuousAt.prodMk hG.continuousAt).eventually
        (isClosed_diagonal.isOpen_compl.mem_nhds he)
    filter_upwards [hn] with w hw
    simp only [hw,Prod.zero_eq_mk,Prod.mk.injEq,one_ne_zero,false_and]

theorem eqOn_of_eventuallyEq {F G : E → M} {U : Set E}
    (hU : IsPreconnected U)
    (hF : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,H) ω F z)
    (hG : ∀ z ∈ U, ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,H) ω G z)
    {a : E} (ha : a ∈ U) (he : F =ᶠ[𝓝 a] G) : Set.EqOn F G U := by
  exact AnalyticContinuation.subset_of_local_analytic_equations hU
    (fun z hz => equality_local_equations (hF z hz) (hG z hz))
    ⟨a,ha,mem_interior_iff_mem_nhds.mpr he⟩

end SplitTangent.AnalyticManifoldMaps

namespace SplitTangent.PullbackConnection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
lemma covariantDerivative_reparam {P : E → E →L[ℂ] E} {g s : ℂ → E} {k : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g (k z)) (hs : DifferentiableAt ℂ s (k z))
    (hk : DifferentiableAt ℂ k z) :
    covariantDerivative P (g ∘ k) (s ∘ k) z =
      deriv k z • covariantDerivative P g s (k z) := by
  have hg' := (hg.hasDerivAt.scomp z hk.hasDerivAt).deriv
  have hs' := (hs.hasDerivAt.scomp z hk.hasDerivAt).deriv
  simp only [covariantDerivative,coefficient,Function.comp_apply,hg',hs',
    ContinuousLinearMap.flip_apply,map_smul,smul_apply,smul_add]

end SplitTangent.PullbackConnection

namespace SplitTangent.TangentSplitting.LocalChartImages
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
variable (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

lemma cover_section_coordinates {σ : ℂ → (z : ℂ) × TangentImageFiber S g z}
    (hσ : (L.toData hg hv).IsHorizontalAlong id σ) (z : ℂ) :
    ∃ u : TangentImageFiber S g z,
      (fun w => L.coords z w ((σ w).2.1)) =ᶠ[𝓝 z] fun w => L.trans z z w (L.coords z z u) := by
  obtain ⟨u,hu⟩ := hσ z
  refine ⟨u,?_⟩
  filter_upwards [hu,Metric.isOpen_ball.mem_nhds (L.center z)] with w hw hm
  rw [hw]
  change L.coords z w (L.forward z w u).1=_
  rw [L.forward_val hm,L.coords_uncoords hm]

lemma cover_section_holomorphic {σ : ℂ → (z : ℂ) × TangentImageFiber S g z}
    (hσ : (L.toData hg hv).IsHorizontalAlong id σ) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,(σ z).2.1⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) := by
  intro z
  obtain ⟨u,hu⟩ := L.cover_section_coordinates hg hv hσ z
  have han : AnalyticAt ℂ (fun w => L.coords z w ((σ w).2.1)) z :=
    (L.trans_analytic (L.center z) (L.center z) _).congr hu.symm
  let t := trivializationAt (Model X) (Tangent X) (g z)
  have hz : g z ∈ t.baseSet := L.frame_mem (L.center z)
  apply (t.contMDiffAt_iff (f := fun w => (⟨g w,(σ w).2.1⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
    (by simpa only [t.mem_source] using hz)).mpr
  refine ⟨hg z,?_⟩
  apply han.contDiffAt.contMDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds (L.center z)] with w hw
  exact (t.continuousLinearMapAt_apply_of_mem ℂ (L.frame_mem hw) ((σ w).2.1)).symm

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

lemma rational_forward_germ (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (v : TangentImageFiber S g.finite 1) (w : TangentImageFiber S g.infinity 1)
    (hvw : v.1=w.1) :
    (fun z => (Lf.forward 1 z v).1) =ᶠ[𝓝 (1 : ℂ)] fun z => (Li.forward 1 z⁻¹ w).1 := by
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  let c := chartAt (Model X) (g.finite 1)
  let P := S.coordinateProjector (g.finite 1)
  let f := fun z => Lf.trans 1 1 z (Lf.coords 1 1 v)
  let h := fun z => Li.trans 1 1 z⁻¹ (Li.coords 1 1 w)
  have hi : Tendsto (fun z : ℂ => z⁻¹) (𝓝 1) (𝓝 1) := by simpa using (continuousAt_inv₀ (one_ne_zero : (1:ℂ)≠0)).tendsto
  have hnF : ∀ᶠ z : ℂ in 𝓝 1, z ∈ Metric.ball 1 (Lf.radius 1) := Metric.isOpen_ball.mem_nhds (Lf.center 1)
  have hnI : ∀ᶠ z : ℂ in 𝓝 1, z⁻¹ ∈ Metric.ball 1 (Li.radius 1) := hi (Metric.isOpen_ball.mem_nhds (Li.center 1))
  have hn0 : ∀ᶠ z : ℂ in 𝓝 1, z≠0 := eventually_ne_nhds one_ne_zero
  have hcur : (c ∘ g.finite) =ᶠ[𝓝 (1 : ℂ)] (c ∘ g.infinity) ∘ (fun z => z⁻¹) := by
    filter_upwards [hn0] with z hz
    exact congrArg c (g.overlap z hz)
  have hcur' := eventually_eventually_nhds.mpr hcur
  have hf : ∀ᶠ z : ℂ in 𝓝 1, DifferentiableAt ℂ f z ∧ covariantDerivative P (c ∘ g.finite) f z=0 := by
    filter_upwards [hnF] with z hz
    exact ⟨(Lf.trans_analytic (Lf.center 1) hz _).differentiableAt,
      (Lf.horizontal 1 1 (Lf.center 1) z hz _ (Lf.coords_fixed (Lf.center 1) v)).2⟩
  have hh : ∀ᶠ z : ℂ in 𝓝 1, DifferentiableAt ℂ h z ∧ covariantDerivative P (c ∘ g.finite) h z=0 := by
    filter_upwards [hnI,hn0,hcur'] with z hz hz0 hcz
    have hA := Li.trans_analytic (Li.center 1) hz (Li.coords 1 1 w)
    have hk : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := differentiableAt_inv hz0
    have hgA := coordinateCurve_analytic g.infinity_holomorphic (g.infinity 1) (Li.chart_source 1 z⁻¹ hz)
    have hh0 := (Li.horizontal 1 1 (Li.center 1) z⁻¹ hz _ (Li.coords_fixed (Li.center 1) w)).2
    have hrep := covariantDerivative_reparam (P := S.coordinateProjector (g.infinity 1)) hgA.differentiableAt hA.differentiableAt hk
    refine ⟨hA.differentiableAt.comp z hk,?_⟩
    rw [covariantDerivative_curve_congr hcz]
    dsimp only [P,c,h]
    rw [hb]
    change covariantDerivative (S.coordinateProjector (g.infinity 1))
      (((chartAt (Model X) (g.infinity 1)) ∘ g.infinity) ∘ (fun z => z⁻¹))
      ((fun z => Li.trans 1 1 z (Li.coords 1 1 w)) ∘ (fun z => z⁻¹)) z=0
    rw [hrep,hh0,smul_zero]
  have hfi : ∀ᶠ z : ℂ in 𝓝 1, P ((c ∘ g.finite) z) (f z)=f z := by
    filter_upwards [hnF] with z hz
    exact (Lf.horizontal 1 1 (Lf.center 1) z hz _ (Lf.coords_fixed (Lf.center 1) v)).1
  have hhi : ∀ᶠ z : ℂ in 𝓝 1, P ((c ∘ g.finite) z) (h z)=h z := by
    filter_upwards [hnI,hn0] with z hz hz0
    dsimp only [P,c,Function.comp_apply]
    rw [g.overlap z hz0,hb]
    exact (Li.horizontal 1 1 (Li.center 1) z⁻¹ hz _ (Li.coords_fixed (Li.center 1) w)).1
  have he : f 1=h 1 := by
    dsimp only [f,h]
    rw [inv_one,Lf.normalized 1 1 (Lf.center 1),Li.normalized 1 1 (Li.center 1)]
    simp only [one_apply_eq_self]
    change (trivializationAt (Model X) (Tangent X) (g.finite 1)).continuousLinearMapAt ℂ (g.finite 1) v.1=
      (trivializationAt (Model X) (Tangent X) (g.infinity 1)).continuousLinearMapAt ℂ (g.infinity 1) w.1
    simp only [hb,hvw]
    have hcbase (x y : X.Carrier) (hxy : x=y) (q : Model X) :
        (trivializationAt (Model X) (Tangent X) (g.infinity 1)).continuousLinearMapAt ℂ x q =
          (trivializationAt (Model X) (Tangent X) (g.infinity 1)).continuousLinearMapAt ℂ y q := by
      subst y
      rfl
    exact hcbase _ _ hb w.1
  have hsource : g.finite 1 ∈ c.source := mem_chart_source (Model X) (g.finite 1)
  have hu := horizontal_local_uniqueness (S.coordinateProjector_analytic _ _ (c.map_source hsource))
    (coordinateCurve_analytic g.finite_holomorphic _ hsource)
    (S.coordinateProjector_eventually_idempotent _ (c.map_source hsource)) hf hh hfi hhi he
  filter_upwards [hu,hnF,hnI,hn0] with z hz hzF hzI hz0
  rw [Lf.forward_val hzF,Li.forward_val hzI]
  change Lf.uncoords 1 z (f z)=Li.uncoords 1 z⁻¹ (h z)
  rw [hz]
  dsimp only [LocalChartImages.uncoords,LocalChartImages.frame]
  simp only [hb]
  have hubase (x y : X.Carrier) (hxy : x=y) (q : Model X) :
      (trivializationAt (Model X) (Tangent X) (g.infinity 1)).symmL ℂ x q =
        (trivializationAt (Model X) (Tangent X) (g.infinity 1)).symmL ℂ y q := by
    subst y
    rfl
  exact hubase _ _ (g.overlap z hz0) (h z)

end SplitTangent.TangentSplitting

namespace SplitTangent
open Filter Topology Set
variable {X : ComplexManifold.{u}}

 

lemma rational_section_gluing (g : RationalCurve X)
    (sf : ∀ z, Tangent X (g.finite z)) (si : ∀ z, Tangent X (g.infinity z))
    (hf : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.finite z,sf z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)))
    (hi : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.infinity z,si z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)))
    (he : sf =ᶠ[𝓝 (1:ℂ)] fun z => si z⁻¹) : ∀ z, z≠0 → sf z=si z⁻¹ := by
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) (0 : ℂ)).isConnected.isPreconnected
  have hl : ∀ z ∈ ({0}ᶜ : Set ℂ), ∃ f : ℂ → Model X, AnalyticAt ℂ f z ∧
      ∀ᶠ w in 𝓝 z, sf w=si w⁻¹ ↔ f w=0 := by
    intro z hz
    let t := trivializationAt (Model X) (Tangent X) (g.finite z)
    have hzF : g.finite z ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
    have hzI : g.infinity z⁻¹ ∈ t.baseSet := (g.overlap z hz) ▸ hzF
    have hF := ((t.contMDiffAt_iff (f := fun w => (⟨g.finite w,sf w⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
      (t.mem_source.mpr hzF)).mp (hf z)).2.contDiffAt.analyticAt
    have hInv : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w : ℂ => w⁻¹) z :=
      (analyticAt_id.inv hz).contDiffAt.contMDiffAt
    have hI := ((t.contMDiffAt_iff (f := fun w => (⟨g.infinity w⁻¹,si w⁻¹⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
      (t.mem_source.mpr hzI)).mp ((hi z⁻¹).comp z hInv)).2.contDiffAt.analyticAt
    refine ⟨fun w => (t ⟨g.finite w,sf w⟩).2-(t ⟨g.infinity w⁻¹,si w⁻¹⟩).2,hF.sub hI,?_⟩
    filter_upwards [(g.finite_holomorphic.continuous.continuousAt.eventually (t.open_baseSet.mem_nhds hzF)),
      eventually_ne_nhds hz] with w hw hw0
    have hbw := g.overlap w hw0
    have hwF : (⟨g.finite w,sf w⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := t.mem_source.mpr hw
    have hwI : (⟨g.infinity w⁻¹,si w⁻¹⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := t.mem_source.mpr (hbw ▸ hw)
    constructor
    · intro h
      have htotal : (⟨g.finite w,sf w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)=⟨g.infinity w⁻¹,si w⁻¹⟩ :=
        Bundle.TotalSpace.ext hbw (heq_of_eq h)
      exact sub_eq_zero.mpr (congrArg (fun q => (t q).2) htotal)
    · intro h
      have hh : t ⟨g.finite w,sf w⟩=t ⟨g.infinity w⁻¹,si w⁻¹⟩ := by
        apply Prod.ext
        · rw [t.coe_fst hwF,t.coe_fst hwI]
          exact hbw
        · exact sub_eq_zero.mp h
      have hh' := t.injOn hwF hwI hh
      exact congrArg (fun q : TangentBundle (ModelWithCorners X) X.Carrier => q.2) hh'
  exact fun z hz => AnalyticContinuation.subset_of_local_analytic_equations hconn hl
    ⟨1,one_ne_zero,mem_interior_iff_mem_nhds.mpr he⟩ hz

end SplitTangent

namespace SplitTangent.HorizontalCovering.LocalTransportData
open Filter Topology
variable {B : Type*} [TopologicalSpace B] {V : B → Type*}
  (D : LocalTransportData B V)
lemma horizontal_germ_of_value {σ : B → (b : B) × V b}
    (hσ : D.IsHorizontalAlong id σ) {a : B} {v : V a} (ha : σ a=⟨a,v⟩) :
    σ =ᶠ[𝓝 a] fun z => ⟨z,D.forward a z v⟩ := by
  obtain ⟨w,hw,hh⟩ := D.horizontal_local_form hσ a
  have hwv : w=v := sigma_mk_injective (hw.symm.trans ha)
  cases hwv
  exact hh
end SplitTangent.HorizontalCovering.LocalTransportData

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem exists_rational_horizontal_section (g : RationalCurve X)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) (v : Tangent X (g.finite a)) (hv : S.projector (g.finite a) v=v) :
    ∃ s : CurveTangentSection g, s.finite a=v ∧
      (∀ z, S.projector (g.finite z) (s.finite z)=s.finite z) ∧
      (∀ z, S.projector (g.infinity z) (s.infinity z)=s.infinity z) := by
  classical
  obtain ⟨Lf⟩ := S.exists_local_chart_images g.finite_holomorphic
  obtain ⟨Li⟩ := S.exists_local_chart_images g.infinity_holomorphic
  let Df := Lf.toData g.finite_holomorphic hvf
  let Di := Li.toData g.infinity_holomorphic hvi
  obtain ⟨σ,hσ,hσa⟩ := Df.exists_normalized_horizontal continuous_id a (⟨v,hv⟩ : TangentImageFiber S g.finite a)
  obtain ⟨u,hu,huσ⟩ := Df.horizontal_local_form hσ 1
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  let w : TangentImageFiber S g.infinity 1 := ⟨u.1,by rw [← hb]; exact u.2⟩
  obtain ⟨τ,hτ,hτ1⟩ := Di.exists_normalized_horizontal continuous_id 1 w
  have hτg := Di.horizontal_germ_of_value hτ hτ1
  let sf : ∀ z, Tangent X (g.finite z) := fun z => (σ z).2.1
  let si : ∀ z, Tangent X (g.infinity z) := fun z => (τ z).2.1
  have hsf := Lf.cover_section_holomorphic g.finite_holomorphic hvf hσ
  have hsi := Li.cover_section_holomorphic g.infinity_holomorphic hvi hτ
  have hloc := S.rational_forward_germ g Lf Li u w rfl
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (𝓝 1) (𝓝 1) := by simpa using (continuousAt_inv₀ (one_ne_zero : (1:ℂ)≠0)).tendsto
  have he : sf =ᶠ[𝓝 (1:ℂ)] fun z => si z⁻¹ := by
    filter_upwards [huσ,hinv hτg,hloc] with z hz hz' hzv
    dsimp only [sf,si]
    rw [hz,hz']
    exact hzv
  have hEq := rational_section_gluing g sf si hsf hsi he
  let s : CurveTangentSection g := {
    finite := sf
    infinity := si
    finite_holomorphic := hsf
    infinity_holomorphic := hsi
    overlap := fun z hz => by
      exact hEq z hz }
  refine ⟨s,?_,?_,?_⟩
  · change (σ a).2.1=v
    rw [hσa]
  · intro z
    have hh := (σ z).2.2
    change S.projector (g.finite (σ z).1) (sf z)=sf z at hh
    rwa [Df.horizontal_base hσ z] at hh
  · intro z
    have hh := (τ z).2.2
    change S.projector (g.infinity (τ z).1) (si z)=si z at hh
    rwa [Di.horizontal_base hτ z] at hh

end SplitTangent.TangentSplitting

namespace SplitTangent.HorizontalCovering.LocalTransportData
open Filter Topology Set
variable {B : Type*} [TopologicalSpace B] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
  {V : B → Type*} (D : LocalTransportData B V)

 
noncomputable def globalSection (a : B) (v : V a) : (b : B) → V b :=
  fun b => Classical.choose (D.horizontal_local_form
    (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).1 b)

lemma globalSection_horizontal (a : B) (v : V a) :
    D.IsHorizontalAlong id (fun b => ⟨b,D.globalSection a v b⟩) := by
  let σ := Classical.choose (D.exists_normalized_horizontal continuous_id a v)
  have hσ := (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).1
  have he : σ=(fun b => ⟨b,D.globalSection a v b⟩) := by
    funext b
    exact (Classical.choose_spec (D.horizontal_local_form hσ b)).1
  rw [← he]
  exact hσ

lemma globalSection_self (a : B) (v : V a) : D.globalSection a v a=v := by
  have hσ := (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).1
  have he := (Classical.choose_spec (D.horizontal_local_form hσ a)).1
  have hn := (Classical.choose_spec (D.exists_normalized_horizontal continuous_id a v)).2
  exact sigma_mk_injective (he.symm.trans hn)

lemma globalSection_unique {σ : (b : B) → V b}
    (hσ : D.IsHorizontalAlong id (fun b => ⟨b,σ b⟩)) (a : B) :
    D.globalSection a (σ a)=σ := by
  have he := D.horizontal_unique continuous_id
    (D.globalSection_horizontal a (σ a)) hσ a
    (by rw [D.globalSection_self])
  funext b
  exact sigma_mk_injective (congrFun he b)

lemma globalSection_cocycle (a b c : B) (v : V a) :
    D.globalSection b (D.globalSection a v b) c=D.globalSection a v c := by
  exact congrFun (D.globalSection_unique (D.globalSection_horizontal a v) b) c

 

noncomputable def globalTransport (a b : B) : V a ≃ V b where
  toFun v := D.globalSection a v b
  invFun v := D.globalSection b v a
  left_inv v := by
    change D.globalSection b (D.globalSection a v b) a=v
    rw [D.globalSection_cocycle,D.globalSection_self]
  right_inv v := by
    change D.globalSection a (D.globalSection b v a) b=v
    rw [D.globalSection_cocycle,D.globalSection_self]

lemma globalTransport_self (a : B) (v : V a) : D.globalTransport a a v=v :=
  D.globalSection_self a v

lemma globalTransport_cocycle (a b c : B) (v : V a) :
    D.globalTransport b c (D.globalTransport a b v)=D.globalTransport a c v :=
  D.globalSection_cocycle a b c v

lemma globalTransport_germ (a b : B) (v : V a) :
    ∀ᶠ z in 𝓝 b, D.globalTransport a z v =
      D.forward b z (D.globalTransport a b v) := by
  obtain ⟨w,hw,hh⟩ := D.horizontal_local_form (D.globalSection_horizontal a v) b
  have hwv : w=D.globalSection a v b := sigma_mk_injective hw.symm
  filter_upwards [hh] with z hz
  change D.globalSection a v z=_
  exact (sigma_mk_injective hz).trans (congrArg (D.forward b z) hwv)

end SplitTangent.HorizontalCovering.LocalTransportData

namespace SplitTangent.TangentSplitting.LocalChartImages
section
open Filter Topology Set HorizontalCovering
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

 

noncomputable def continuation (a b : ℂ) :
    TangentImageFiber S g a ≃ TangentImageFiber S g b :=
  (L.toData hg hv).globalTransport a b

lemma continuation_self (a : ℂ) (v : TangentImageFiber S g a) :
    L.continuation hg hv a a v=v :=
  (L.toData hg hv).globalTransport_self a v

lemma continuation_cocycle (a b c : ℂ) (v : TangentImageFiber S g a) :
    L.continuation hg hv b c (L.continuation hg hv a b v)=L.continuation hg hv a c v :=
  (L.toData hg hv).globalTransport_cocycle a b c v

lemma continuation_holomorphic (a : ℂ) (v : TangentImageFiber S g a) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,(L.continuation hg hv a z v).1⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) := by
  exact L.cover_section_holomorphic hg hv ((L.toData hg hv).globalSection_horizontal a v)

lemma continuation_add (a b : ℂ) (v w : TangentImageFiber S g a) :
    (L.continuation hg hv a b ⟨v.1+w.1,by simp only [map_add,v.2,w.2]⟩).1 =
      (L.continuation hg hv a b v).1+(L.continuation hg hv a b w).1 := by
  let D := L.toData hg hv
  let τ : (z : ℂ) → TangentImageFiber S g z := fun z => ⟨
    (D.globalTransport a z v).1+(D.globalTransport a z w).1,
    by rw [map_add,(D.globalTransport a z v).2,(D.globalTransport a z w).2]⟩
  have ht : D.IsHorizontalAlong id (fun z => ⟨z,τ z⟩) := by
    intro c
    refine ⟨τ c,?_⟩
    filter_upwards [D.globalTransport_germ a c v,D.globalTransport_germ a c w,
      Metric.ball_mem_nhds c (L.positive c)] with z hzv hzw hz
    apply congrArg (Sigma.mk z)
    apply Subtype.ext
    change (D.globalTransport a z v).1+(D.globalTransport a z w).1=(L.forward c z (τ c)).1
    rw [hzv,hzw]
    change (L.forward c z (D.globalTransport a c v)).1+
      (L.forward c z (D.globalTransport a c w)).1=(L.forward c z (τ c)).1
    rw [L.forward_val hz,L.forward_val hz,L.forward_val hz]
    simp only [τ,map_add]
  have he := congrFun (D.globalSection_unique ht a) b
  have hta : τ a=⟨v.1+w.1,by simp only [map_add,v.2,w.2]⟩ := by
    apply Subtype.ext
    dsimp only [τ]
    rw [D.globalTransport_self,D.globalTransport_self]
  rw [hta] at he
  exact congrArg Subtype.val he

lemma continuation_smul (a b : ℂ) (c : ℂ) (v : TangentImageFiber S g a) :
    (L.continuation hg hv a b ⟨c • v.1,by simp only [map_smul,v.2]⟩).1 =
      c • (L.continuation hg hv a b v).1 := by
  let D := L.toData hg hv
  let τ : (z : ℂ) → TangentImageFiber S g z := fun z => ⟨
    c • (D.globalTransport a z v).1,
    by rw [map_smul,(D.globalTransport a z v).2]⟩
  have ht : D.IsHorizontalAlong id (fun z => ⟨z,τ z⟩) := by
    intro d
    refine ⟨τ d,?_⟩
    filter_upwards [D.globalTransport_germ a d v,
      Metric.ball_mem_nhds d (L.positive d)] with z hzv hz
    apply congrArg (Sigma.mk z)
    apply Subtype.ext
    change c • (D.globalTransport a z v).1=(L.forward d z (τ d)).1
    rw [hzv]
    change c • (L.forward d z (D.globalTransport a d v)).1=(L.forward d z (τ d)).1
    rw [L.forward_val hz,L.forward_val hz]
    simp only [τ,map_smul]
  have he := congrFun (D.globalSection_unique ht a) b
  have hta : τ a=⟨c • v.1,by simp only [map_smul,v.2]⟩ := by
    apply Subtype.ext
    dsimp only [τ]
    rw [D.globalTransport_self]
  rw [hta] at he
  exact congrArg Subtype.val he

end

open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

 

noncomputable def continuationLinear (a b : ℂ) :
    Tangent X (g a) →ₗ[ℂ] Tangent X (g b) where
  toFun v := (L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩).1
  map_add' v w := by
    simpa only [map_add] using L.continuation_add hg hv a b
      ⟨S.projector (g a) v,S.idempotent (g a) v⟩ ⟨S.projector (g a) w,S.idempotent (g a) w⟩
  map_smul' c v := by
    simpa only [map_smul,RingHom.id_apply] using L.continuation_smul hg hv a b c
      ⟨S.projector (g a) v,S.idempotent (g a) v⟩

noncomputable def continuationMap (a b : ℂ) :
    Tangent X (g a) →L[ℂ] Tangent X (g b) := by
  let t := trivializationAt (Model X) (Tangent X) (g a)
  let e := t.continuousLinearEquivAt ℂ (g a) (FiberBundle.mem_baseSet_trivializationAt' (g a))
  letI : FiniteDimensional ℂ (Tangent X (g a)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact (L.continuationLinear hg hv a b).toContinuousLinearMap

lemma continuationMap_apply (a b : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv a b v =
      (L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩).1 := rfl

lemma continuationMap_fixed (a b : ℂ) (v : Tangent X (g a)) :
    S.projector (g b) (L.continuationMap hg hv a b v)=L.continuationMap hg hv a b v :=
  (L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩).2

lemma continuationMap_self (a : ℂ) : L.continuationMap hg hv a a=S.projector (g a) := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg Subtype.val (L.continuation_self hg hv a
    ⟨S.projector (g a) v,S.idempotent (g a) v⟩)

lemma continuationMap_cocycle (a b c : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv b c (L.continuationMap hg hv a b v)=L.continuationMap hg hv a c v := by
  rw [L.continuationMap_apply]
  have he : (⟨S.projector (g b) (L.continuationMap hg hv a b v),
      S.idempotent (g b) (L.continuationMap hg hv a b v)⟩ : TangentImageFiber S g b)=
      L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩ := by
    apply Subtype.ext
    exact L.continuationMap_fixed hg hv a b v
  rw [he,L.continuation_cocycle]
  rfl

lemma continuationMap_reverse (a b : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv b a (L.continuationMap hg hv a b v)=S.projector (g a) v := by
  rw [L.continuationMap_cocycle,L.continuationMap_self]

lemma continuationMap_holomorphic (a : ℂ) (v : Tangent X (g a)) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,L.continuationMap hg hv a z v⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) :=
  L.continuation_holomorphic hg hv a ⟨S.projector (g a) v,S.idempotent (g a) v⟩

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.HorizontalCovering.LocalTransportData
open Filter Topology Set
variable {B : Type*} [TopologicalSpace B] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
  {V : B → Type*} (D : LocalTransportData B V)

 

lemma globalTransport_local (a : B) (hc : IsConnected (D.domain a)) (v : V a)
    {b : B} (hb : b ∈ D.domain a) : D.globalTransport a b v=D.forward a b v := by
  let : ConnectedSpace (D.domain a) := isConnected_iff_connectedSpace.mp hc
  have hglobal : D.IsHorizontalAlong (fun z : D.domain a => (z : B))
      (fun z => ⟨(z : B),D.globalTransport a z v⟩) := by
    intro z
    obtain ⟨w,hw⟩ := D.globalSection_horizontal a v (z : B)
    exact ⟨w,continuous_subtype_val.continuousAt hw⟩
  have hlocal : D.IsHorizontalAlong (fun z : D.domain a => (z : B))
      (fun z => ⟨(z : B),D.forward a z v⟩) := by
    intro z
    refine ⟨D.forward a z v,?_⟩
    have hh := D.overlap a z z ⟨z.2,D.domain_self z⟩ v
    rw [D.reverse_self] at hh
    filter_upwards [continuous_subtype_val.continuousAt hh] with w hw
    exact congrArg (Sigma.mk (w : B)) hw.symm
  have he := D.horizontal_unique continuous_subtype_val hglobal hlocal
    (⟨a,D.domain_self a⟩ : D.domain a) (by rw [D.globalTransport_self,D.forward_self])
  exact sigma_mk_injective (congrFun he (⟨b,hb⟩ : D.domain a))

lemma globalTransport_reverse_local (a : B) (hc : IsConnected (D.domain a))
    {b : B} (hb : b ∈ D.domain a) (v : V b) :
    D.globalTransport b a v=D.reverse a b v := by
  apply (D.globalTransport a b).injective
  rw [D.globalTransport_cocycle,D.globalTransport_self,D.globalTransport_local a hc _ hb]
  exact (D.right_inv a b hb v).symm

end SplitTangent.HorizontalCovering.LocalTransportData

namespace SplitTangent.TangentSplitting.LocalChartImages
section
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

lemma continuationMap_reverse_local (b : ℂ) {z : ℂ} (hz : z ∈ Metric.ball b (L.radius b))
    (v : Tangent X (g z)) : L.continuationMap hg hv z b v=
      L.uncoords b b (L.trans b z b (L.coords b z (S.projector (g z) v))) := by
  rw [L.continuationMap_apply]
  have hc : IsConnected ((L.toData hg hv).domain b) :=
    ⟨⟨b,L.center b⟩,(convex_ball b (L.radius b)).isPreconnected⟩
  change ((L.toData hg hv).globalTransport z b
    ⟨S.projector (g z) v,S.idempotent (g z) v⟩).1=_
  rw [(L.toData hg hv).globalTransport_reverse_local b hc hz]
  exact L.reverse_val hz _

 

lemma continuationMap_reverse_holomorphic_at (a b : ℂ) (v : ∀ z, Tangent X (g z))
    (hvs : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g a,L.continuationMap hg hv z a (v z)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) b := by
  let t := L.frame b
  let u := trivializationAt (Model X) (Tangent X) (g a)
  have ht : g b ∈ t.baseSet := L.frame_mem (L.center b)
  have hu : g a ∈ u.baseSet := FiberBundle.mem_baseSet_trivializationAt' (g a)
  have hp : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,S.projector (g z) (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b :=
    S.holomorphic.contMDiffAt.comp b hvs
  have hp' := ((t.contMDiffAt_iff (f := fun z => (⟨g z,S.projector (g z) (v z)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using ht)).mp hp).2
  have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω
      (fun z => L.coords b z (S.projector (g z) (v z))) b := by
    apply hp'.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds b (L.positive b)] with z hz
    exact t.continuousLinearMapAt_apply_of_mem ℂ (L.frame_mem hz) _
  have hTa : AnalyticAt ℂ (fun z => L.trans b z b) b :=
    (L.analytic b (b,b) ⟨L.center b,L.center b⟩).comp
      (g := fun w : ℂ × ℂ => L.trans b w.1 w.2)
      (f := fun z : ℂ => (z,b)) (analyticAt_id.prod analyticAt_const)
  have hf := hTa.contDiffAt.contMDiffAt.clm_apply hc
  let C : Model X →L[ℂ] Model X := (u.continuousLinearMapAt ℂ (g a)).comp
    ((L.continuationMap hg hv b a).comp (L.uncoords b b))
  have hCf : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω
      (fun z => C (L.trans b z b (L.coords b z (S.projector (g z) (v z))))) b :=
    C.contDiff.contMDiff.contMDiffAt.comp b hf
  apply (u.contMDiffAt_iff (f := fun z => (⟨g a,L.continuationMap hg hv z a (v z)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [u.mem_source] using hu)).mpr
  refine ⟨contMDiffAt_const,?_⟩
  apply hCf.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds b (L.positive b)] with z hz
  rw [← L.continuationMap_cocycle hg hv z b a (v z),L.continuationMap_reverse_local hg hv b hz]
  exact (u.continuousLinearMapAt_apply_of_mem ℂ hu _).symm

end

open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
lemma continuation_germ (a b : ℂ) (v : TangentImageFiber S g a) :
    ∀ᶠ z in 𝓝 b, L.continuation hg hv a z v =
      L.forward b z (L.continuation hg hv a b v) :=
  (L.toData hg hv).globalTransport_germ a b v

lemma continuationMap_apply_fixed (a b : ℂ) (v : Tangent X (g a))
    (h : S.projector (g a) v=v) : L.continuationMap hg hv a b v=
      (L.continuation hg hv a b ⟨v,h⟩).1 := by
  rw [L.continuationMap_apply]
  congr 2
  exact Subtype.ext h
end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

lemma rational_continuation_overlap (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) (v : Tangent X (g.finite a)) {z : ℂ} (hz : z ≠ 0) :
    Lf.continuationMap g.finite_holomorphic hvf a z v =
      Li.continuationMap g.infinity_holomorphic hvi 1 z⁻¹
        (Lf.continuationMap g.finite_holomorphic hvf a 1 v) := by
  let u0 : TangentImageFiber S g.finite a := ⟨S.projector (g.finite a) v,S.idempotent _ v⟩
  let u := Lf.continuation g.finite_holomorphic hvf a 1 u0
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  let w : TangentImageFiber S g.infinity 1 := ⟨u.1,by rw [← hb]; exact u.2⟩
  let sf := fun q => (Lf.continuation g.finite_holomorphic hvf a q u0).1
  let si := fun q => (Li.continuation g.infinity_holomorphic hvi 1 q w).1
  have hsf := Lf.continuation_holomorphic g.finite_holomorphic hvf a u0
  have hsi := Li.continuation_holomorphic g.infinity_holomorphic hvi 1 w
  have hf := Lf.continuation_germ g.finite_holomorphic hvf a 1 u0
  have hi := Li.continuation_germ g.infinity_holomorphic hvi 1 1 w
  rw [Li.continuation_self] at hi
  have hloc := S.rational_forward_germ g Lf Li u w rfl
  have hinv : Tendsto (fun q : ℂ => q⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuousAt_inv₀ (one_ne_zero : (1:ℂ)≠0)).tendsto
  have he : sf =ᶠ[𝓝 (1:ℂ)] fun q => si q⁻¹ := by
    filter_upwards [hf,hinv hi,hloc] with q hq hq' hqv
    dsimp only [sf,si]
    rw [hq,hq']
    exact hqv
  have hEq := rational_section_gluing g sf si hsf hsi he z hz
  rw [Lf.continuationMap_apply]
  change sf z=Li.continuationMap g.infinity_holomorphic hvi 1 z⁻¹ u.1
  rw [Li.continuationMap_apply_fixed _ _ _ _ _ w.2]
  exact hEq

end SplitTangent.TangentSplitting

namespace SplitTangent
section
open Filter Topology Set

lemma holomorphic_const_fiber_linear_at {X : ComplexManifold.{u}} {x y : X.Carrier}
    (A : Tangent X x →L[ℂ] Tangent X y) {v : ℂ → Tangent X x} {b : ℂ}
    (hv : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨x,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨y,A (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b := by
  let t := trivializationAt (Model X) (Tangent X) x
  let u := trivializationAt (Model X) (Tangent X) y
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hy : y ∈ u.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
  have hvc := ((t.contMDiffAt_iff (f := fun z => (⟨x,v z⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp hv).2
  let C : Model X →L[ℂ] Model X := (u.continuousLinearMapAt ℂ y).comp (A.comp (t.symmL ℂ x))
  have hc := C.contDiff.contMDiff.contMDiffAt.comp b hvc
  apply (u.contMDiffAt_iff (f := fun z => (⟨y,A (v z)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [u.mem_source] using hy)).mpr
  refine ⟨contMDiffAt_const,?_⟩
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with z
  change (u ⟨y,A (v z)⟩).2=C (t ⟨x,v z⟩).2
  rw [← t.continuousLinearMapAt_apply_of_mem ℂ hx]
  dsimp only [C,ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hx]
  exact (u.continuousLinearMapAt_apply_of_mem ℂ hy _).symm

namespace TangentSplitting.LocalChartImages
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
lemma continuationMap_source (a b : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv a b (S.projector (g a) v)=L.continuationMap hg hv a b v := by
  rw [L.continuationMap_apply,L.continuationMap_apply]
  congr 2
  exact Subtype.ext (S.idempotent _ v)
end TangentSplitting.LocalChartImages

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
lemma rational_reverse_overlap (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) {z : ℂ} (hz : z ≠ 0) (v : Tangent X (g.finite z)) :
    Lf.continuationMap g.finite_holomorphic hvf z a v =
      Lf.continuationMap g.finite_holomorphic hvf 1 a
        (Li.continuationMap g.infinity_holomorphic hvi z⁻¹ 1 v) := by
  let f := Lf.continuationMap g.finite_holomorphic hvf
  let i := Li.continuationMap g.infinity_holomorphic hvi
  let w := i z⁻¹ 1 v
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  have hw : S.projector (g.finite 1) w=w := by
    rw [hb]
    exact Li.continuationMap_fixed _ _ _ _ _
  have hfw : f a 1 (f 1 a w)=w := by
    dsimp only [f]
    erw [Lf.continuationMap_reverse,hw]
  have hiw : i 1 z⁻¹ w=S.projector (g.finite z) v := by
    dsimp only [i,w]
    erw [Li.continuationMap_reverse,g.overlap z hz]
  change f z a v=f 1 a w
  calc
    _ = f z a (S.projector (g.finite z) v) := (Lf.continuationMap_source _ _ _ _ _).symm
    _ = f z a (i 1 z⁻¹ w) := by rw [hiw]
    _ = f z a (i 1 z⁻¹ (f a 1 (f 1 a w))) := by rw [hfw]
    _ = f z a (f a z (f 1 a w)) := by
      rw [S.rational_continuation_overlap g Lf Li hvf hvi a (f 1 a w) hz]
    _ = f 1 a w := by
      dsimp only [f]
      erw [Lf.continuationMap_reverse,Lf.continuationMap_fixed]

 

noncomputable def rationalReverseMap (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) : CurveBundleMap g (RationalCurve.constant (g.finite a)) where
  finite z := Lf.continuationMap g.finite_holomorphic hvf z a
  infinity z := (Lf.continuationMap g.finite_holomorphic hvf 1 a).comp
    (Li.continuationMap g.infinity_holomorphic hvi z 1)
  overlap z hz := by
    apply ContinuousLinearMap.ext
    intro v
    exact S.rational_reverse_overlap g Lf Li hvf hvi a hz v
  finite_holomorphic U hU v hv z hz :=
    (Lf.continuationMap_reverse_holomorphic_at g.finite_holomorphic hvf a z v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))).contMDiffWithinAt
  infinity_holomorphic U hU v hv z hz := by
    have h := Li.continuationMap_reverse_holomorphic_at g.infinity_holomorphic hvi 1 z v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))
    have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
    rw [← hb] at h
    exact (holomorphic_const_fiber_linear_at
      (Lf.continuationMap g.finite_holomorphic hvf 1 a) h).contMDiffWithinAt

theorem exists_rational_reverse_map (g : RationalCurve X)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) : ∃ B : CurveBundleMap g (RationalCurve.constant (g.finite a)),
      B.finite a=S.projector (g.finite a) := by
  obtain ⟨Lf⟩ := S.exists_local_chart_images g.finite_holomorphic
  obtain ⟨Li⟩ := S.exists_local_chart_images g.infinity_holomorphic
  exact ⟨S.rationalReverseMap g Lf Li hvf hvi a,Lf.continuationMap_self _ _ a⟩
end TangentSplitting
end

open Filter Topology Set

 

lemma holomorphic_along_sum_smul_at {X : ComplexManifold.{u}}
    {ι : Type*} [Fintype ι] {g : ℂ → X.Carrier} {z : ℂ}
    (hg : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g z)
    (c : ι → ℂ → ℂ) (v : ι → ∀ w, Tangent X (g w))
    (hc : ∀ i, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (c i) z)
    (hv : ∀ i, ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨g w,v i w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨g w,∑ i, c i w • v i w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  let t := trivializationAt (Model X) (Tangent X) (g z)
  have hz : g z ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' (g z)
  have hsrc (v' : Tangent X (g z)) : (⟨g z,v'⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := by
    simpa only [t.mem_source] using hz
  apply (t.contMDiffAt_iff (f := fun w => (⟨g w,∑ i, c i w • v i w⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mpr
  refine ⟨hg,?_⟩
  have hv' (i : ι) := ((t.contMDiffAt_iff (f := fun w => (⟨g w,v i w⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mp (hv i)).2
  have hsum : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω
      (fun w => ∑ i, c i w • (t ⟨g w,v i w⟩).2) z := by
    apply ContMDiffAt.sum
    intro i _
    exact (hc i).smul (hv' i)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hg.continuousAt.eventually (t.open_baseSet.mem_nhds hz)] with w hw
  change (t.linearEquivAt ℂ (g w) hw) (∑ i, c i w • v i w)=_
  simp only [map_sum,map_smul,Bundle.Trivialization.linearEquivAt_apply]

namespace CurveBundleMap
variable {X : ComplexManifold.{u}} {g : RationalCurve X}

 

def ofSections (x : X.Carrier) (σ : Fin X.dim → CurveTangentSection g) :
    CurveBundleMap (RationalCurve.constant x) g := by
  classical
  let t := trivializationAt (Model X) (Tangent X) x
  let e := t.continuousLinearEquivAt ℂ x (FiberBundle.mem_baseSet_trivializationAt' x)
  let f : ℂ → Tangent X x →L[ℂ] Model X := fun z => (∑ i, (ContinuousLinearMap.proj i).smulRight (show Model X from (σ i).finite z)).comp e.toContinuousLinearMap
  let h : ℂ → Tangent X x →L[ℂ] Model X := fun z => (∑ i, (ContinuousLinearMap.proj i).smulRight (show Model X from (σ i).infinity z)).comp e.toContinuousLinearMap
  have hf (z : ℂ) (v : Tangent X x) : f z v=∑ i, (e v) i • (σ i).finite z := by
    simp only [f,ContinuousLinearMap.comp_apply,sum_apply,ContinuousLinearEquiv.coe_coe]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hh (z : ℂ) (v : Tangent X x) : h z v=∑ i, (e v) i • (σ i).infinity z := by
    simp only [h,ContinuousLinearMap.comp_apply,sum_apply,ContinuousLinearEquiv.coe_coe]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hcoeff {U : Set ℂ} (hU : IsOpen U) (v : ℂ → Tangent X x)
      (hv : ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
        (fun z => (⟨x,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U)
      (z : ℂ) (hz : z ∈ U) (i : Fin X.dim) :
      ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w => (e (v w)) i) z := by
    have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    have hvz := (hv z hz).contMDiffAt (hU.mem_nhds hz)
    have hc := ((t.contMDiffAt_iff (f := fun w => (⟨x,v w⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp hvz).2
    exact (contMDiffAt_pi_space.mp hc) i
  refine ⟨f,h,?_,?_,?_⟩
  · intro z hz
    apply ContinuousLinearMap.ext
    intro v
    erw [hf,hh]
    simp only [fun i => (σ i).overlap z hz]
    rfl
  · intro U hU v hv z hz
    have hd := holomorphic_along_sum_smul_at (g.finite_holomorphic z)
      (fun i w => (e (v w)) i) (fun i w => (σ i).finite w)
      (fun i => hcoeff hU v hv z hz i) (fun i => (σ i).finite_holomorphic z)
    have he : (fun w => (⟨g.finite w,f w (v w)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) =
        (fun w => (⟨g.finite w,∑ i, (e (v w)) i • (σ i).finite w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) := by
      funext w
      erw [hf]
    erw [he]
    exact hd.contMDiffWithinAt
  · intro U hU v hv z hz
    have hd := holomorphic_along_sum_smul_at (g.infinity_holomorphic z)
      (fun i w => (e (v w)) i) (fun i w => (σ i).infinity w)
      (fun i => hcoeff hU v hv z hz i) (fun i => (σ i).infinity_holomorphic z)
    have he : (fun w => (⟨g.infinity w,h w (v w)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) =
        (fun w => (⟨g.infinity w,∑ i, (e (v w)) i • (σ i).infinity w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) := by
      funext w
      erw [hh]
    erw [he]
    exact hd.contMDiffWithinAt

lemma ofSections_finite (x : X.Carrier) (σ : Fin X.dim → CurveTangentSection g)
    (z : ℂ) (v : Tangent X x) :
    (ofSections x σ).finite z v = ∑ i,
      (trivializationAt (Model X) (Tangent X) x ⟨x,v⟩).2 i • (σ i).finite z := by
  classical
  dsimp only [ofSections]
  change @Eq (Model X)
    ((∑ i, (ContinuousLinearMap.proj i).smulRight (M₂ := Model X) ((σ i).finite z))
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearEquivAt ℂ x
        (FiberBundle.mem_baseSet_trivializationAt' x) v)) _
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

lemma ofSections_infinity (x : X.Carrier) (σ : Fin X.dim → CurveTangentSection g)
    (z : ℂ) (v : Tangent X x) :
    (ofSections x σ).infinity z v = ∑ i,
      (trivializationAt (Model X) (Tangent X) x ⟨x,v⟩).2 i • (σ i).infinity z := by
  classical
  dsimp only [ofSections]
  change @Eq (Model X)
    ((∑ i, (ContinuousLinearMap.proj i).smulRight (M₂ := Model X) ((σ i).infinity z))
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearEquivAt ℂ x
        (FiberBundle.mem_baseSet_trivializationAt' x) v)) _
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

end CurveBundleMap
end SplitTangent

namespace SplitTangent.TangentSplitting
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def rationalContinuationSection (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) (v : Tangent X (g.finite a)) : CurveTangentSection g where
  finite z := Lf.continuationMap g.finite_holomorphic hvf a z v
  infinity z := Li.continuationMap g.infinity_holomorphic hvi 1 z
    (Lf.continuationMap g.finite_holomorphic hvf a 1 v)
  finite_holomorphic := Lf.continuationMap_holomorphic _ _ a v
  infinity_holomorphic := Li.continuationMap_holomorphic _ _ 1 _
  overlap _ hz := S.rational_continuation_overlap g Lf Li hvf hvi a v hz

 

theorem exists_rational_trivialization (g : RationalCurve X)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) :
    ∃ (A : CurveBundleMap (RationalCurve.constant (g.finite a)) g)
      (B : CurveBundleMap g (RationalCurve.constant (g.finite a))),
      A.finite a=S.projector (g.finite a) ∧ B.finite a=S.projector (g.finite a) ∧
      (∀ z v, B.finite z (A.finite z v)=S.projector (g.finite a) v) ∧
      (∀ z v, A.finite z (B.finite z v)=S.projector (g.finite z) v) ∧
      (∀ z v, B.infinity z (A.infinity z v)=S.projector (g.finite a) v) ∧
      (∀ z v, A.infinity z (B.infinity z v)=S.projector (g.infinity z) v) := by
  classical
  obtain ⟨Lf⟩ := S.exists_local_chart_images g.finite_holomorphic
  obtain ⟨Li⟩ := S.exists_local_chart_images g.infinity_holomorphic
  let f := Lf.continuationMap g.finite_holomorphic hvf
  let i := Li.continuationMap g.infinity_holomorphic hvi
  let t := trivializationAt (Model X) (Tangent X) (g.finite a)
  let e := t.continuousLinearEquivAt ℂ (g.finite a)
    (FiberBundle.mem_baseSet_trivializationAt' (g.finite a))
  let b := Pi.basisFun ℂ (Fin X.dim)
  let σ := fun j => S.rationalContinuationSection g Lf Li hvf hvi a (e.symm (b j))
  let A := CurveBundleMap.ofSections (g.finite a) σ
  let B := S.rationalReverseMap g Lf Li hvf hvi a
  have heq (v : Tangent X (g.finite a)) : ∑ j, (e v) j • e.symm (b j)=v := by
    have hsum : ∑ j, (e v) j • b j=e v := by
      simpa only [b,Pi.basisFun_repr] using b.sum_repr (e v)
    calc
      _ = e.symm (∑ j, (e v) j • b j) := by simp only [map_sum,map_smul]
      _ = v := by rw [hsum,e.symm_apply_apply]
  have hAf (z : ℂ) (v : Tangent X (g.finite a)) : A.finite z v=f a z v := by
    erw [CurveBundleMap.ofSections_finite]
    change ∑ j, (e v) j • f a z (e.symm (b j))=f a z v
    simpa only [map_sum,map_smul] using congrArg (f a z) (heq v)
  have hAi (z : ℂ) (v : Tangent X (g.finite a)) : A.infinity z v=i 1 z (f a 1 v) := by
    erw [CurveBundleMap.ofSections_infinity]
    change ∑ j, (e v) j • i 1 z (f a 1 (e.symm (b j)))=i 1 z (f a 1 v)
    let C : Tangent X (g.finite a) →L[ℂ] Tangent X (g.infinity z) :=
      (i 1 z).comp (f a 1)
    change ∑ j, (e v) j • C (e.symm (b j)) = C v
    simpa only [map_sum,map_smul] using congrArg C (heq v)
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  refine ⟨A,B,?_,Lf.continuationMap_self _ _ a,?_,?_,?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    erw [hAf]
    exact congrArg (fun C : Tangent X (g.finite a) →L[ℂ] Tangent X (g.finite a) => C v)
      (Lf.continuationMap_self _ _ a)
  · intro z v
    erw [hAf]
    exact Lf.continuationMap_reverse _ _ a z v
  · intro z v
    erw [hAf]
    exact Lf.continuationMap_reverse _ _ z a v
  · intro z v
    erw [hAi]
    change f 1 a (i z 1 (i 1 z (f a 1 v)))=S.projector (g.finite a) v
    erw [Li.continuationMap_reverse]
    erw [← hb,Lf.continuationMap_fixed]
    exact Lf.continuationMap_reverse _ _ a 1 v
  · intro z v
    erw [hAi]
    change i 1 z (f a 1 (f 1 a (i z 1 v)))=S.projector (g.infinity z) v
    erw [Lf.continuationMap_reverse]
    rw [hb,Li.continuationMap_fixed]
    exact Li.continuationMap_reverse _ _ z 1 v

end SplitTangent.TangentSplitting

end

end OAI
